using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.ML;
using Microsoft.Boogie;
using Microsoft.Boogie.ProofGen;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;

namespace ProofGeneration.ProgramToVCProof
{
    public class ProgramVcProofData
    {
        public ProgramVcProofData(
            IEnumerable<Function> vcFunctions,
            VcBoogieInfo vcBoogieInfo,
            VCHintManager vcHintManager,
            LocaleDecl vcLocale,
            IVCVarFunTranslator vcTranslator)
        {
            VcFunctions = vcFunctions;
            VcBoogieInfo = vcBoogieInfo;
            VcHintManager = vcHintManager;
            VcLocale = vcLocale;
            VcTranslator = vcTranslator;
        }

        public IEnumerable<Function> VcFunctions { get; }
        public VcBoogieInfo VcBoogieInfo { get; }
        public VCHintManager VcHintManager { get; }
        public LocaleDecl VcLocale { get; }
        public IVCVarFunTranslator VcTranslator { get; }
    }

    /// <summary>
    ///     Responsible for producing theory for the proof of the final Boogie program under the assumption of the VC
    /// </summary>
    public class VcPhaseManager
    {
        public static Theory ProgramToVcProof(
            string theoryName,
            bool generateEndToEndProof,
            CFGRepr finalCfg,
            CFGRepr afterPassificationCfg,
            IDictionary<Block, Block> afterPassiveToFinalBlock,
            IDictionary<Block, Block> afterPassiveToOrigBlock,
            IProgramAccessor passiveProgAccess,
            IProgramAccessor beforePassiveProgAccess,
            BoogieMethodData methodData,
            ProgramVcProofData vcProofData,
            IVariableTranslationFactory varFactory,
            TypePremiseEraserFactory eraserFactory,
            VCExpressionGenerator gen,
            IsaUniqueNamer namerForFunctions,
            out Term vcAssm,
            out LemmaDecl endToEndLemma)
        {
            var lemmaNamer = new IsaUniqueNamer();
            var passiveLemmaManager = new VcPhaseLemmaManager(
                vcProofData.VcBoogieInfo.VcInst,
                methodData,
                vcProofData.VcFunctions,
                passiveProgAccess.BlockInfo(),
                varFactory);

            var afterPassiveReachableBlocks = ReachableBlocks(afterPassificationCfg);

            var finalProgramLemmas =
                GenerateVCLemmas(afterPassificationCfg, finalCfg, afterPassiveToFinalBlock, afterPassiveToOrigBlock,
                    afterPassiveReachableBlocks, passiveLemmaManager, vcProofData.VcHintManager, lemmaNamer);
            var cfgProgramLemmas =
                GenerateCfgLemmas(afterPassificationCfg, finalCfg, afterPassiveToFinalBlock,
                    afterPassiveReachableBlocks, finalProgramLemmas, passiveLemmaManager, passiveProgAccess.CfgDecl(),
                    lemmaNamer);

            var afterPassificationDecls = new List<OuterDecl>();
            foreach (var v in finalProgramLemmas.Values) afterPassificationDecls.AddRange(v);
            afterPassificationDecls.AddRange(cfgProgramLemmas.Values);

            var afterPassificationLocale =
                GenerateLocale("passification", passiveLemmaManager, afterPassificationDecls);

            var passiveOuterDecls = new List<OuterDecl> {vcProofData.VcLocale};
            passiveOuterDecls.Add(afterPassificationLocale);

            //generate axiom
            var axiomUniqueNamer = new IsaUniqueNamer();
            var axId = 0;
            var axiomToLemma = new Dictionary<Axiom, OuterDecl>();
            var vcRewriteLemmaGen =
                new VcRewriteLemmaGen(eraserFactory, VCExprToIsaTranslator.CreateNameBasedTranslator(new IsaUniqueNamer()));

            var vcAxiomLemmaManager = new VcAxiomLemmaManager(
                vcProofData.VcBoogieInfo.VcInstAxiom,
                methodData,
                vcProofData.VcFunctions,
                vcRewriteLemmaGen, varFactory);

            var axiomLocaleRequiredDecls = new List<OuterDecl>();
            foreach (var axiom in vcProofData.VcBoogieInfo.VcAxiomsInfo)
                if (axiom is VcBoogieAxiomInfo vcBoogieAxiom)
                {
                    var axiomVcLemma =
                        vcAxiomLemmaManager.AxiomVcLemma(
                            axiomUniqueNamer.GetName(axiom, "axiom_vc_" + axId),
                            vcBoogieAxiom.Axiom,
                            vcBoogieAxiom.Expr,
                            out var requiredDecls);
                    axiomToLemma.Add(vcBoogieAxiom.Axiom, axiomVcLemma);
                    axiomLocaleRequiredDecls.AddRange(requiredDecls);
                }

            /* we add the required declarations for the axiom locale to the outer theory, since the axiom locale fixes variables that could clash
             * with the declarations */
            passiveOuterDecls.AddRange(axiomLocaleRequiredDecls);
            var axiomLocale = GenerateLocale("axioms", vcAxiomLemmaManager, axiomToLemma.Values.ToList());
            passiveOuterDecls.Add(axiomLocale);

            if (generateEndToEndProof)
            {
                var endToEnd = new EndToEndVCProof(
                    methodData,
                    passiveProgAccess,
                    vcProofData.VcFunctions,
                    vcProofData.VcBoogieInfo,
                    afterPassificationCfg,
                    finalCfg,
                    afterPassificationLocale.Name + "." + cfgProgramLemmas[afterPassificationCfg.entry].Name,
                    axiomLocale.Name,
                    ax => axiomLocale.Name + "." + axiomToLemma[ax].Name,
                    varFactory,
                    vcProofData.VcTranslator,
                    eraserFactory,
                    namerForFunctions,
                    gen);
                passiveOuterDecls.AddRange(endToEnd.GenerateProof(out vcAssm, out endToEndLemma));
            }
            else
            {
                vcAssm = null;
                endToEndLemma = null;
            }

            return
                new Theory(theoryName,
                    new List<string>
                    {
                        "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.VCHints", "Boogie_Lang.VCPhaseML",
                        passiveProgAccess.TheoryName(), 
                        beforePassiveProgAccess != null ? beforePassiveProgAccess.TheoryName() : ""
                    },
                    passiveOuterDecls);
        }

        private static HashSet<Block> ReachableBlocks(CFGRepr cfg)
        {
            var reachableBlocks = new HashSet<Block>();
            var queue = new Queue<Block>();
            reachableBlocks.Add(cfg.entry);
            queue.Enqueue(cfg.entry);

            while (queue.TryDequeue(out var b))
                if (!LemmaHelper.FinalStateIsMagic(b))
                {
                    //b's successors are not trivially unreachable
                    var successors = cfg.GetSuccessorBlocks(b);
                    foreach (var suc in successors)
                    {
                        reachableBlocks.Add(suc);
                        queue.Enqueue(suc);
                    }
                }

            return reachableBlocks;
        }


        //assume that block identities in the two CFGs are the same (only edges may be different)
        private static IDictionary<Block, IList<OuterDecl>> GenerateVCLemmas(
            CFGRepr afterPassificationCfg,
            CFGRepr finalCfg,
            IDictionary<Block, Block> afterPassiveToFinalBlock,
            IDictionary<Block, Block> afterPassiveToOrigBlock,
            HashSet<Block> reachableBlocks,
            VcPhaseLemmaManager vcPhaseLemmaManager,
            VCHintManager vcHintManager,
            IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, IList<OuterDecl>>();

            foreach (var bAfterPassive in afterPassificationCfg.GetBlocksBackwards())
            {
                var result = new List<OuterDecl>();

                if (afterPassiveToFinalBlock.TryGetValue(bAfterPassive, out var bFinal))
                {
                    string vcHintsName = null;
                    if (vcHintManager.TryGetHints(afterPassiveToOrigBlock[bAfterPassive], out var hints,
                        out var requiredDecls))
                    {
                        //FIXME potential val name clash
                        vcHintsName = GetLemmaName(bAfterPassive, lemmaNamer) + "_hints";
                        var code = MLUtil.DefineVal(vcHintsName, MLUtil.MLList(hints));
                        //required declarations must be added first
                        result.AddRange(requiredDecls);
                        result.Add(new MLDecl(code));
                    }

                    result.Add(vcPhaseLemmaManager.GenerateBlockLemma(
                        bAfterPassive, bFinal, finalCfg.GetSuccessorBlocks(bFinal), GetLemmaName(bFinal, lemmaNamer),
                        vcHintsName));
                    //do not use identity of final CFG block to be consistent with other branches
                    blockToLemmaDecls.Add(bAfterPassive, result);
                }
                else if (reachableBlocks.Contains(bAfterPassive))
                {
                    //block was removed after peephole but is reachable before peephole
                    if (bAfterPassive.Cmds.Count == 0)
                    {
                        //find the successors of b in the final cfg (i.e., the first non-empty reachable blocks)
                        var nonEmptyReachableSuccessors =
                            GetNonEmptyReachableSuccessors(bAfterPassive, afterPassificationCfg, finalCfg,
                                afterPassiveToFinalBlock);
                        //add lemma
                        var decls = new List<OuterDecl>
                        {
                            vcPhaseLemmaManager.GenerateEmptyBlockLemma(
                                bAfterPassive,
                                nonEmptyReachableSuccessors.Select(b => afterPassiveToFinalBlock[b]),
                                GetLemmaName(bAfterPassive, lemmaNamer))
                        };
                        blockToLemmaDecls.Add(bAfterPassive, decls);
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException(
                            "Non-empty reachable block removed during peep-hole");
                    }
                }
            }

            return blockToLemmaDecls;
        }

        private static IDictionary<Block, OuterDecl> GenerateCfgLemmas(
            CFGRepr afterPassificationCfg,
            CFGRepr finalCfg,
            IDictionary<Block, Block> afterPassiveToFinalBlock,
            HashSet<Block> reachableBlocks,
            IDictionary<Block, IList<OuterDecl>> lemmaDecls,
            VcPhaseLemmaManager vcPhaseLemmaManager,
            Term cfgTerm,
            IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, OuterDecl>();

            foreach (var bAfterPassive in afterPassificationCfg.GetBlocksBackwards())
            {
                IEnumerable<Block> finalCfgSuccessors;
                var isContainedInFinalCfg = afterPassiveToFinalBlock.TryGetValue(bAfterPassive, out var bFinal);
                if (!isContainedInFinalCfg)
                {
                    if (reachableBlocks.Contains(bAfterPassive))
                        finalCfgSuccessors =
                            GetNonEmptyReachableSuccessors(bAfterPassive, afterPassificationCfg, finalCfg,
                                afterPassiveToFinalBlock).Select(b => afterPassiveToFinalBlock[b]);
                    else
                        continue;
                }
                else
                {
                    finalCfgSuccessors = finalCfg.GetSuccessorBlocks(bFinal);
                }

                var lemma = vcPhaseLemmaManager.GenerateCfgLemma(
                    bAfterPassive,
                    bFinal,
                    isContainedInFinalCfg,
                    afterPassificationCfg.GetSuccessorBlocks(bAfterPassive),
                    finalCfgSuccessors,
                    cfgTerm,
                    b => "cfg_" + lemmaNamer.GetName(b, b.Label),
                    (LemmaDecl) lemmaDecls[bAfterPassive].Last());
                blockToLemmaDecls.Add(bAfterPassive, lemma);
            }

            return blockToLemmaDecls;
        }

        private static string GetLemmaName(Block b, IsaUniqueNamer uniqueNamer)
        {
            return uniqueNamer.GetName(b, "block_" + b.Label);
        }

        private static LocaleDecl GenerateLocale(string localeName, ILocaleContext localeContext,
            IList<OuterDecl> coreLemmas)
        {
            var prelude = localeContext.Prelude();
            prelude.AddRange(coreLemmas);
            return new LocaleDecl(localeName, localeContext.Context(), prelude);
        }

        //return first reachable blocks from block in afterPassificationCfg, which are non-empty and contained in finalCfg
        private static IEnumerable<Block> GetNonEmptyReachableSuccessors(
            Block afterPassiveBlock,
            CFGRepr afterPassificationCfg,
            CFGRepr finalCfg,
            IDictionary<Block, Block> afterPassiveToFinalBlock)
        {
            //block is unreachable after peephole
            var nonEmptySuccessors = new HashSet<Block>();

            if (afterPassificationCfg.NumOfSuccessors(afterPassiveBlock) > 0)
            {
                //find first reachable blocks that are not empty
                var toVisit = new Queue<Block>();
                toVisit.Enqueue(afterPassiveBlock);
                while (toVisit.Count > 0)
                {
                    var curBlock = toVisit.Dequeue();

                    if (curBlock.Cmds.Count != 0 && finalCfg.ContainsBlock(afterPassiveToFinalBlock[curBlock]))
                        nonEmptySuccessors.Add(curBlock);
                    else
                        foreach (var succ in afterPassificationCfg.GetSuccessorBlocks(curBlock))
                            toVisit.Enqueue(succ);
                }
            }

            return nonEmptySuccessors;
        }
    }
}