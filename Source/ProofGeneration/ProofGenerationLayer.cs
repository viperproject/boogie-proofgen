﻿using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Isa;
using ProofGeneration.IsaPrettyPrint;
using ProofGeneration.VCProofGen;
using ProofGeneration.ProgramToVCProof;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using ProofGeneration.Util;
using ProofGeneration.BoogieIsaInterface;

namespace ProofGeneration
{
    public class ProofGenerationLayer
    {
        private static Implementation afterPassificationImpl;

        private static IDictionary<Block, Block> beforeDagOrigBlock;
        private static CFGRepr beforeDagCfg;
        private static IEnumerable<Variable> beforeDagInParams;
        private static IEnumerable<Variable> beforeDagLocalVars;
        private static IEnumerable<Variable> beforeDagOutParams;


        private static IDictionary<Block, Block> beforePassiveOrigBlock;
        private static CFGRepr beforePassificationCfg;
        private static IEnumerable<Variable> beforePassiveInParams;
        private static IEnumerable<Variable> beforePassiveLocalVars;
        private static IEnumerable<Variable> beforePassiveOutParams;

        private static CFGRepr afterPassificationCfg;
        private static CFGRepr noEmptyBlocksCfg;
        private static CFGRepr afterUnreachablePruningCfg;

        private static IEnumerable<Axiom> axioms;
        private static IEnumerable<Function> functions;
        private static IEnumerable<Variable> inParams;
        private static IEnumerable<Variable> localVars;
        private static IEnumerable<Variable> outParams;

        private static IDictionary<Block, IDictionary<Variable, Variable>> finalVarMapping = new Dictionary<Block, IDictionary<Variable, Variable>>();
        private static IDictionary<Variable, Variable> passiveToOrigVar = new Dictionary<Variable, Variable>();

        //VC Automation Hints
        private static readonly VCHintManager vcHintManager = new VCHintManager();

        public static void Program(Program p)
        {
            axioms = p.Axioms;
            functions = p.Functions;
        }

        public static void BeforeCFGToDAG(Implementation impl)
        {
            beforeDagCfg = CFGReprTransformer.getCFGRepresentation(impl, true, out beforeDagOrigBlock, false);

            beforeDagInParams = new List<Variable>(impl.InParams);
            beforeDagLocalVars = new List<Variable>(impl.LocVars);
            beforeDagOutParams = new List<Variable>(impl.OutParams);
        }

        public static void BeforePassification(Implementation impl)
        {
            beforePassificationCfg = CFGReprTransformer.getCFGRepresentation(impl, true, out beforePassiveOrigBlock);

            beforePassiveInParams = new List<Variable>(impl.InParams);
            beforePassiveLocalVars = new List<Variable>(impl.LocVars);
            beforePassiveOutParams = new List<Variable>(impl.OutParams);
        }

        /*
        public static void RecordFinalVariableMapping(Block b, IDictionary<Variable, Expr> variableToExpr)
        {
            Contract.Requires(b != null);
            Contract.Requires(variableToExpr != null);

            var origVarToPassiveVar = new Dictionary<Variable, Variable>();

            foreach (var kv in variableToExpr)
            {
                if (kv.Value is IdentifierExpr ie && ie.Decl is Variable vPassive)
                {
                    origVarToPassiveVar.Add(kv.Key, vPassive);
                    if (passiveToOrigVar.TryGetValue(vPassive, out Variable origVarInMap))
                    {
                        if (origVarInMap != kv.Key)
                            throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer), "passive variable corresponds to more than one original variables");
                    } else
                    {
                        passiveToOrigVar.Add(vPassive, kv.Key);
                    }
                }
            }

            finalVarMapping.Add(b, origVarToPassiveVar);
        }
        */

        public static void AfterPassification(Implementation impl)
        {
            inParams = impl.InParams;
            localVars = impl.LocVars;
            outParams = impl.OutParams;
            afterPassificationImpl = impl;
            afterPassificationCfg = CFGReprTransformer.getCFGRepresentation(impl);

            var nameToVar = new Dictionary<string, Variable>();

            foreach(Variable v in beforePassiveInParams.Union(beforePassiveLocalVars).Union(beforePassiveOutParams))
            {
                nameToVar.Add(v.Name, v);
            }

            foreach(Variable vPassive in inParams.Union(localVars).Union(outParams))
            {
                //heuristic to get mapping
                string [] split = vPassive.Name.Split('@');
                if(nameToVar.TryGetValue(split[0], out Variable vOrig))
                {
                    passiveToOrigVar.Add(vPassive, vOrig);
                } else
                {
                    throw new ProofGenUnexpectedStateException(typeof(ProofGenerationLayer), "Cannot predict mapping between passive and original variable");
                }
            } 
        }

        public static void AfterEmptyBlockRemoval(Implementation impl)
        {
            noEmptyBlocksCfg = CFGReprTransformer.getCFGRepresentation(impl);
        }

        public static void AfterUnreachablePruning(Implementation impl)
        {
            afterUnreachablePruningCfg = CFGReprTransformer.getCFGRepresentation(impl);
        }

        /// <summary> Records hint for a cmd in the final passified Boogie program</summary>
        /// <param name="exprVC">the computed VC for the expression in the command</param>
        /// <param name="postVC">the computed postcondition of the command</param>
        /// <param name="resultVC">Wlp(cmd, postVC)</param>
        /// <param name="subsumptionOption">The subsumption option for this cmd.</param>
        public static void NextHintForBlock(
            Cmd cmd, 
            Block block, 
            VCExpr exprVC, 
            VCExpr postVC, 
            VCExpr resultVC, 
            CommandLineOptions.SubsumptionOption subsumptionOption)
        {
            vcHintManager.NextHintForBlock(cmd, block, exprVC, postVC, resultVC, subsumptionOption);
        }

        public static void VCGenerateAllProofs(VCExpr vc, VCExpressionGenerator gen, Boogie2VCExprTranslator translator)
        {           
            LocaleDecl vcLocale = VCToIsaInterface.ConvertVC(
                "vc",
                vc,
                new StandardActiveDecl(),
                gen,
                translator,
                functions,
                inParams,
                localVars,
                afterUnreachablePruningCfg,
                out VCInstantiation vcinst);

            var lemmaNamer = new IsaUniqueNamer();

            var passiveLemmaManager = new PassiveLemmaManager(vcinst, functions, inParams, localVars, outParams);
            IDictionary<Block, IList<OuterDecl>> finalProgramLemmas = GenerateVCLemmas(afterUnreachablePruningCfg, passiveLemmaManager, lemmaNamer);
            // ignore peephole for now
            //IDictionary<Block, LemmaDecl> beforePeepholeEmptyLemmas = GetAdjustedLemmas(afterPassificationCfg, afterUnreachablePruningCfg, passiveLemmaManager, lemmaNamer);

            //Contract.Assert(!finalProgramLemmas.Keys.Intersect(beforePeepholeEmptyLemmas.Keys).Any());

            
            List<OuterDecl> afterPassificationDecls = new List<OuterDecl>() { };
            foreach(var v in finalProgramLemmas.Values)
            {
                afterPassificationDecls.AddRange(v);
            }
            //afterPassificationDecls.AddRange(beforePeepholeEmptyLemmas.Values);
          

            IsaProgramRepr programRepr = new IsaProgramGenerator().GetIsaProgram("progLocale", afterPassificationImpl.Name, functions, axioms, beforeDagInParams, beforeDagLocalVars, beforeDagOutParams, beforeDagCfg, out IList<OuterDecl> programDecls);
            afterPassificationDecls.Add(passiveLemmaManager.MethodVerifiesLemma(
                afterUnreachablePruningCfg,
                programRepr.cfgDeclDef,
                "method_verifies"));

            LocaleDecl afterPassificationLocale = GenerateLocale("passification", passiveLemmaManager, afterPassificationDecls);

            var passiveOuterDecls = new List<OuterDecl>() { vcLocale };
            passiveOuterDecls.AddRange(programDecls);
            passiveOuterDecls.Add(afterPassificationLocale);

            var endToEnd = new EndToEndVCProof(functions, inParams, localVars, programRepr, vcinst, afterUnreachablePruningCfg);
            passiveOuterDecls.AddRange(endToEnd.GenerateProof());

            Theory theoryPassive = new Theory(afterPassificationImpl.Name+"_passive",
                new List<string>() { "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.VCHints", "Boogie_Lang.ExperimentalML" },
                passiveOuterDecls);

            StoreTheory(theoryPassive);
        }

        private static ISet<Block> ComputeReachableEmptyBlocks(CFGRepr beforePeephole)
        {
            var result = new HashSet<Block>();

            Queue<Block> queue = new Queue<Block>();
            queue.Enqueue(beforePeephole.entry);

            while(queue.Any())
            {
                Block curBlock = queue.Dequeue();
                if(!LemmaHelper.FinalStateIsMagic(curBlock))
                {
                    if (curBlock.Cmds.Count == 0)
                        result.Add(curBlock);

                    foreach(Block bSucc in beforePeephole.GetSuccessorBlocks(curBlock))
                    {
                        queue.Enqueue(bSucc);
                    }
                }
            }

            return result;
        }

        private static IDictionary<Block, IList<OuterDecl>> GenerateVCLemmas(CFGRepr cfg, PassiveLemmaManager passiveLemmaManager, IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, IList<OuterDecl>>();

            foreach (Block b in cfg.GetBlocksBackwards())
            {
                //TODO move elsewhere
                var result = new List<OuterDecl>();
                string vcHintsName = null;
                if (vcHintManager.TryGetHints(b, out IEnumerable<VCHint> hints))
                {
                    //FIXME potential val name clash
                    vcHintsName = b.Label + "_hints";
                    var code = MLUtil.DefineVal(b.Label + "_hints", MLUtil.MLList(hints));
                    result.Add(new MLDecl(code));
                }
                result.Add(passiveLemmaManager.GenerateBlockLemma(b, cfg.GetSuccessorBlocks(b), lemmaNamer.GetName(b, GetLemmaName(b)), vcHintsName));
                blockToLemmaDecls.Add(b, result);
            }

            return blockToLemmaDecls;
        }

        //return first reachable blocks from block which are non-empty
        private static IEnumerable<Block> GetNonEmptySuccessors(Block block, CFGRepr cfg)
        {            
            //block is unreachable after peephole
                var nonEmptySuccessors = new List<Block>();

                if (cfg.NumOfSuccessors(block) > 0)
                {
                    //find first reachable blocks that are not empty
                    Queue<Block> toVisit = new Queue<Block>();
                    toVisit.Enqueue(block);
                    while (toVisit.Count > 0)
                    {
                        Block curBlock = toVisit.Dequeue();

                        if (curBlock.Cmds.Count != 0)
                        {
                            nonEmptySuccessors.Add(curBlock);
                        }
                        else
                        {
                            foreach (Block succ in cfg.GetSuccessorBlocks(curBlock))
                            {
                                toVisit.Enqueue(succ);
                            }
                        }
                    }
                }
                        
            return nonEmptySuccessors;
        }

        //assume that block identities in beforePruning and afterPruning are the same (only edges may be different)
        private static IDictionary<Block, LemmaDecl> GetAdjustedLemmas(CFGRepr beforePeepholeCfg, 
            CFGRepr afterPeepholeCfg, 
            IBlockLemmaManager lemmaManager, 
            IsaUniqueNamer lemmaNamer)
        {
            var blocksToLemmas = new Dictionary<Block, LemmaDecl>();

            foreach(Block block in beforePeepholeCfg.GetBlocksBackwards())
            {
                if(!afterPeepholeCfg.ContainsBlock(block))               
                {
                    //block is unreachable after peephole

                    if(block.Cmds.Count == 0)
                    {
                        var nonEmptySuccessors = GetNonEmptySuccessors(block, beforePeepholeCfg);

                        //add lemma
                        blocksToLemmas.Add(block, lemmaManager.GenerateEmptyBlockLemma(block, nonEmptySuccessors, lemmaNamer.GetName(block, GetLemmaName(block))));
                    }
                }     
            }

            return blocksToLemmas;
        }

        private static LocaleDecl GenerateLocale(string localeName, IBlockLemmaManager lemmaManager, IList<OuterDecl> coreLemmas)
        {
            IList<OuterDecl> prelude = lemmaManager.Prelude();
            prelude.AddRange(coreLemmas);
            return new LocaleDecl(localeName, lemmaManager.Context(), prelude);
        }

        private static string GetLemmaName(Block b)
        {
            return "block_" + b.Label;
        }
        
        private static void StoreTheory(Theory theory)
        {
            var sw = new StreamWriter(theory.theoryName + ".thy");

            string theoryString = IsaPrettyPrinter.PrintTheory(theory);

            sw.WriteLine(theoryString);
            sw.Close();
        }

        /* old code
        private static IDictionary<Block, LemmaDecl> GenerateBeforePassiveLemmas(
            CFGRepr beforePassiveCfg,
            CFGRepr finalCfg,
            CFGRepr beforePeephole,
            PrePassiveLemmaManager prePassiveLemmaManager,
            IsaUniqueNamer lemmaNamer)
        {
            var blockToLemmaDecls = new Dictionary<Block, LemmaDecl>();

            ISet<Block> beforePeepholeReachable = ComputeReachableEmptyBlocks(beforePeephole);

            foreach (Block b in beforePassiveCfg.GetBlocksBackwards())
            {
                Block origBlock = beforePassiveOrigBlock[b];
                if (finalCfg.ContainsBlock(origBlock))
                {
                    LemmaDecl lemma = prePassiveLemmaManager.GenerateBlockLemma(
                        b,
                        finalCfg.GetSuccessorBlocks(origBlock),
                        lemmaNamer.GetName(b, GetLemmaName(b)),
                        null);
                    blockToLemmaDecls.Add(b, lemma);
                }
                else if (beforePeepholeReachable.Contains(origBlock))
                {
                    var nonEmptySuccessors = GetNonEmptySuccessors(origBlock, beforePeephole);
                    LemmaDecl lemma = prePassiveLemmaManager.GenerateEmptyBlockLemma(
                        b,
                        nonEmptySuccessors,
                        lemmaNamer.GetName(b, GetLemmaName(b)));
                    blockToLemmaDecls.Add(b, lemma);
                }
            }

            return blockToLemmaDecls;
        }

        private static IDictionary<Block, LemmaDecl> GetAdjustedPassiveLemmas(
            CFGRepr beforePassification,
            IDictionary<Block, Block> beforePassiveToOrig,
            CFGRepr beforePeephole,
            IBlockLemmaManager lemmaManager,
            IsaUniqueNamer lemmaNamer)
        {
            var blocksToLemmas = new Dictionary<Block, LemmaDecl>();

            foreach (Block block in beforePassification.GetBlocksBackwards())
            {
                Block origBlock = beforePassiveToOrig[block];

                if (origBlock.Cmds.Count == 0)
                {
                    var nonEmptySuccessors = GetNonEmptySuccessors(origBlock, beforePeephole);
                    blocksToLemmas.Add(block, lemmaManager.GenerateEmptyBlockLemma(block, nonEmptySuccessors, lemmaNamer.GetName(block, GetLemmaName(block))));
                }
            }

            return blocksToLemmas;
        }
        */

    }

}