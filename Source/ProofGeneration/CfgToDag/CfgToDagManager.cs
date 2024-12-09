using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.PhasesUtil;
using ProofGeneration.Util;

namespace ProofGeneration.CfgToDag
{
  public class CfgToDagManager
    {
        /**
         * cases:
         * 1) is loop head block
         * 2) is back edge block
         * 3) successor is loop head block
         * 
         * any combination is possible
         */
        public static Theory CfgToDagProof(
            PhasesTheories phasesTheories,
            EndToEndLemmaConfig endToEndLemmaConfig,
            bool generatePassificationProof,
            bool generateVcProof,
            Term vcAssm,
            CFGRepr beforeDagCfg,
            CFGRepr afterDagCfg,
            Block afterUniqueExit,
            BoogieMethodData beforeDagData,
            CfgToDagHintManager hintManager,
            IDictionary<Block, Block> beforeToAfter,
            IProgramAccessor beforeDagProgAccess,
            IProgramAccessor afterDagProgAccess,
            IVariableTranslationFactory varFactory,
            IDictionary<Block, IList<Block>> blocksToLoops)
        {
            var afterToBefore = beforeToAfter.InverseDict();

            //track mapping from blocks to loops that the block is contained in and for which it is not the loop head
            
            
            var varContextName = "\\<Lambda>1";
            var varContextAbbrev = new AbbreviationDecl(
                varContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), beforeDagProgAccess.VarContext())
            );

            var funContextWfName = "Wf_Fun";
            var boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName(varContextName),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.EmptyList);
            var lemmaManager = new CfgToDagLemmaManager(
                beforeDagProgAccess,
                afterDagProgAccess,
                boogieContext,
                afterDagCfg,
                funContextWfName,
                hintManager,
                blocksToLoops,
                beforeToAfter,
                beforeDagData,
                afterUniqueExit,
                varFactory);

            var lemmaNamer = new IsaUniqueNamer();
            var outerDecls = new List<OuterDecl>();

            outerDecls.Add(varContextAbbrev);
            outerDecls.Add(new DeclareDecl("Nat.One_nat_def[simp del]"));
            if (afterUniqueExit != null)
                outerDecls.AddRange(lemmaManager.UnifiedExitLemma(GetCfgLemmaName(afterUniqueExit, lemmaNamer)));

            foreach (var afterBlock in afterDagCfg.GetBlocksBackwards())
                if (afterToBefore.TryGetValue(afterBlock, out var beforeBlock))
                {
                    //if the node's only edge is a backedge, then an "assume false" will be added
                    var singleCutEdge = hintManager.TryIsBackedgeNode(beforeBlock, out var _) &&
                                        beforeDagCfg.NumOfSuccessors(beforeBlock) == 1;

                    var (localLemmas, cfgLemma) =
                        lemmaManager.BlockLemma(
                            beforeBlock,
                            afterBlock,
                            beforeDagCfg.GetSuccessorBlocks(beforeBlock),
                            block => GetLemmaName(block, lemmaNamer),
                            block => GetCfgLemmaName(block, lemmaNamer),
                            singleCutEdge
                        );

                    outerDecls.AddRange(localLemmas);
                    outerDecls.Add(cfgLemma);
                }
                else
                {
                    //block was added as part of transformation 
                    if (afterBlock == afterDagCfg.entry)
                        //entry lemma handled elsewhere
                        continue;

                    var afterBlockSuccessors = afterDagCfg.GetSuccessorBlocks(afterBlock);
                    var afterBlockSuccessorsList = afterBlockSuccessors.ToList();
                    if (!afterBlockSuccessorsList.Any())
                    {
                        //this must be the unique node
                        if (afterUniqueExit == null)
                            throw new ProofGenUnexpectedStateException(
                                "unique exit block added, but only exit block existed before cfg-to-dag");

                        continue;
                    }

                    if (afterBlockSuccessorsList.Count != 1)
                        throw new ProofGenUnexpectedStateException(
                            "Block added in CFG-to-DAG phase does not have a unique successor");

                    var afterUniqueSuc = afterBlockSuccessorsList.First();
                    if (afterToBefore.TryGetValue(afterUniqueSuc, out var beforeUniqueSuc))
                    {
                        hintManager.IsLoopHead(beforeUniqueSuc, out var hint);
                        var lemma = lemmaManager.NewBlockLemma(
                            GetCfgLemmaName(afterBlock, lemmaNamer),
                            afterBlock,
                            afterUniqueSuc,
                            hint
                        );
                        outerDecls.Add(lemma);
                    }
                    else if (hintManager.IsNewBackedgeBlock(afterBlock, out var loopHeadHint))
                    {
                        if (afterDagCfg.GetSuccessorBlocks(afterUniqueSuc).Any())
                            throw new ProofGenUnexpectedStateException(
                                "New backedge node has successor that is not the exit node.");

                        //afterUniqueSuc is a successor to a backedge node for which all edges were eliminated
                        var lemma = lemmaManager.NewBlockLemma(
                            GetCfgLemmaName(afterBlock, lemmaNamer),
                            afterBlock,
                            null,
                            loopHeadHint
                        );
                        outerDecls.Add(lemma);
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException(
                            "CFG-to-DAG: Unique successor of added block cannot be mapped to original block");
                    }
                }

            var entryLemma = lemmaManager.EntryLemma("entry_lemma", beforeDagCfg.entry, afterDagCfg.entry,
                b => GetCfgLemmaName(b, lemmaNamer));
            outerDecls.Add(entryLemma);

            var absValType = new VarType("a");
            var cfgToDagLemmasLocale = new LocaleDecl(
                "cfg_to_dag_lemmas",
                new ContextElem(
                    new List<Tuple<TermIdent, TypeIsa>>
                    {
                        Tuple.Create((TermIdent) boogieContext.absValTyMap,
                            IsaBoogieType.AbstractValueTyFunType(absValType)),
                        Tuple.Create((TermIdent) boogieContext.funContext, IsaBoogieType.FunInterpType(absValType))
                    },
                    new List<Term>
                    {
                        IsaBoogieTerm.FunInterpWf(boogieContext.absValTyMap, beforeDagProgAccess.FunctionsDecl(),
                            boogieContext.funContext)
                    },
                    new List<string> {funContextWfName}
                ),
                outerDecls
            );

            var theoryOuterDecls = new List<OuterDecl>();
            theoryOuterDecls.Add(cfgToDagLemmasLocale);

            if (endToEndLemmaConfig != EndToEndLemmaConfig.DoNotGenerate)
            {
                var endToEndManager = new CfgToDagEndToEnd();
                var endToEndDecls = endToEndManager.EndToEndProof(
                    endToEndLemmaConfig == EndToEndLemmaConfig.GenerateForProcedure,
                    cfgToDagLemmasLocale.Name + "." + entryLemma.Name,
                    phasesTheories.EndToEndLemmaName(PhasesTheories.Phase.Passification, true),
                    vcAssm,
                    beforeDagProgAccess,
                    beforeDagCfg
                );
                theoryOuterDecls.AddRange(endToEndDecls);
            }

            return new Theory(
                phasesTheories.TheoryName(PhasesTheories.Phase.CfgToDag),
                new List<string>
                {
                    "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.BackedgeElim", "Boogie_Lang.TypingML",
                    beforeDagProgAccess.TheoryName(),
                    afterDagProgAccess.TheoryName(), 
                    generatePassificationProof ? phasesTheories.TheoryName(PhasesTheories.Phase.Passification) : "",
                    generateVcProof ? phasesTheories.TheoryName(PhasesTheories.Phase.Vc) : ""
                },
                theoryOuterDecls
            );
        }

        private static string GetLemmaName(Block b, IsaUniqueNamer namer)
        {
            return namer.GetName(b, "block_" + b.Label);
        }

        private static string GetCfgLemmaName(Block b, IsaUniqueNamer namer)
        {
            return "cfg_" + namer.GetName(b, "block_" + b.Label);
        }
    }
}