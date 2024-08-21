using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;

namespace ProofGeneration.CfgToDag
{
    public class CfgToDagLemmaManager
    {
        private readonly CFGRepr afterDagCfg;
        private readonly IProgramAccessor afterDagProgAccess;
        private readonly Block afterExitBlock;

        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor;

        private readonly IProgramAccessor beforeDagProgAccess;
        private readonly IDictionary<Block, Block> beforeToAfterBlock;
        private readonly IDictionary<Block, IList<Block>> blocksToLoops;
        private readonly BoogieContextIsa boogieContext;
        private readonly string dagAssmsName = "DagAssms";
        private readonly string dagVerifiesName = "DagVerifies";
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");
        private readonly Term finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly string funContextWfName;

        private readonly CfgToDagHintManager hintManager;
        private readonly Term initState1;
        private readonly Term initState2;

        private readonly IsaUniqueNamer namer = new IsaUniqueNamer();

        private readonly Term normalInitState1 = IsaCommonTerms.TermIdentFromName("ns1");
        private readonly Term normalInitState2 = IsaCommonTerms.TermIdentFromName("ns2");

        private readonly string redCfgName = "Red";

        private readonly TypingTacticGenerator typingTacticGenerator;
        private readonly IVariableTranslation<Variable> variableTranslation;

        private readonly BoogieMethodData beforeDagData;
        private readonly string state2WellTyLoopHeadName = "StateWt2";

        private readonly string stateRelLoopHeadName = "StateRel1";

        //afterExitBlock is non-null iff afterExitBlock is a newly generated unique exit block after the CFG-to-DAG transformation
        public CfgToDagLemmaManager(
            IProgramAccessor beforeDagProgAccess,
            IProgramAccessor afterDagProgAccess,
            BoogieContextIsa boogieContext,
            CFGRepr afterDagCfg,
            string funContextWfName,
            CfgToDagHintManager hintManager,
            IDictionary<Block, IList<Block>> blocksToLoops,
            IDictionary<Block, Block> beforeToAfterBlock,
            BoogieMethodData beforeDagData,
            Block afterExitBlock,
            IVariableTranslationFactory varFactory
        )
        {
            this.beforeDagProgAccess = beforeDagProgAccess;
            this.afterDagProgAccess = afterDagProgAccess;
            this.afterDagCfg = afterDagCfg;
            this.funContextWfName = funContextWfName;
            variableTranslation = varFactory.CreateTranslation().VarTranslation;
            this.hintManager = hintManager;
            this.blocksToLoops = blocksToLoops;
            this.beforeToAfterBlock = beforeToAfterBlock;
            this.beforeDagData = beforeDagData;
            this.afterExitBlock = afterExitBlock;
            this.boogieContext = boogieContext;
            initState1 = IsaBoogieTerm.Normal(normalInitState1);
            initState2 = IsaBoogieTerm.Normal(normalInitState2);
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(varFactory);
            typingTacticGenerator = new TypingTacticGenerator(beforeDagProgAccess, varFactory);
        }

        private TermList HavocedVarsTerm(IEnumerable<Variable> vars)
        {
            return new TermList(
                vars.Select(x =>
                {
                    if (variableTranslation.TryTranslateVariableId(x, out var varId, out _)) return varId;
                    throw new ProofGenUnexpectedStateException("Could not extract variable id");
                }).ToList());
        }

        private Term InvariantsTerm(IEnumerable<Expr> invs)
        {
            return new TermList(invs.Select(e => basicCmdIsaVisitor.Translate(e)).ToList());
        }

        /// <summary>
        ///     CFG Block lemma for a block that was added after the CFG-to-DAG step
        ///     must be a block that has a single successor bSuc, where bSuc has a corresponding node before the CFG-to-DAG step.
        /// </summary>
        /// <param name="cfgLemmaName"></param>
        /// <param name="afterDag"></param>
        /// <param name="afterDagSuccessor">successor of <paramref name="afterDag" /> (potentially null).</param>
        /// <param name="loopHeadHint">
        ///     non-null if the successor of <paramref name="afterDag" /> before the CFG-to-DAG transformation is a loop head
        ///     if <paramref name="afterDagSuccessor" /> is null, then afterDag must be a newly added backedgeNode for which
        ///     this hint indicates the corresponding loop head.
        /// </param>
        /// <returns></returns>
        public LemmaDecl NewBlockLemma(
            string cfgLemmaName,
            Block afterDag,
            Block afterDagSuccessor,
            LoopHeadHint loopHeadHint
        )
        {
            if (afterDagSuccessor == null && loopHeadHint == null)
                throw new ArgumentException("afterDagSuccessor and loopHeadHint cannot both be null");

            var finalNodeId2 = new SimpleIdentifier("m2'");
            var finalStateId2 = new SimpleIdentifier("s2'");
            var assumptions = new List<Term>();

            var dagVerifiesCfgAssm =
                DagVerifiesCfgAssumption(
                    new NatConst(afterDagProgAccess.BlockInfo().BlockIds[afterDag]),
                    normalInitState2,
                    finalNodeId2,
                    finalStateId2,
                    false);

            assumptions.Add(dagVerifiesCfgAssm);

            assumptions.Add(
                NstateSameOn(
                    normalInitState1,
                    normalInitState2,
                    IsaCommonTerms.EmptySet));

            assumptions.Add(StateWellTyped(normalInitState1));
            assumptions.Add(StateWellTyped(normalInitState2));

            Term conclusion = IsaCommonTerms.TermIdentFromName("R");
            var propagationAssm = conclusion;
            if (loopHeadHint != null)
            {
                var invsHold = IsaCommonTerms.ListAll(
                    IsaBoogieTerm.ExprSatPartial(boogieContext, normalInitState1),
                    new TermList(loopHeadHint.Invariants.Select(inv => basicCmdIsaVisitor.Translate(inv)).ToList())
                );
                propagationAssm = TermBinary.MetaImplies(invsHold, propagationAssm);
            }

            if (afterDagSuccessor != null)
            {
                var dagVerifiesCfgAssmSuc =
                    DagVerifiesCfgAssumption(
                        new NatConst(afterDagProgAccess.BlockInfo().BlockIds[afterDagSuccessor]),
                        normalInitState2,
                        finalNodeId2,
                        finalStateId2);

                propagationAssm = TermBinary.MetaImplies(dagVerifiesCfgAssmSuc, propagationAssm);
            }

            assumptions.Add(propagationAssm);

            var lemmas = new List<LemmaDecl>();

            List<string> proofMethods;
            if (loopHeadHint != null)
            {
                proofMethods =
                    new List<string>
                    {
                        "using assms",
                        ProofUtil.Apply("rule " + (afterDagSuccessor != null
                            ? "cfg_dag_no_cut_propagate_helper"
                            : "cfg_dag_cut_propagate_helper")),
                        "apply (assumption, fastforce)",
                        ProofUtil.Apply(
                            ProofUtil.Simp(afterDagProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterDag)))
                    };

                if (afterDagSuccessor != null)
                    proofMethods.Add(
                        ProofUtil.Apply(
                            ProofUtil.Simp(afterDagProgAccess.BlockInfo().OutEdgesMembershipLemma(afterDag)))
                    );

                var typingTacs = new List<string>();
                foreach (var inv in loopHeadHint.Invariants)
                {
                    var (typing_tac, tac_helper_lemmas) = typingTacticGenerator.GenerateTactic(inv);
                    lemmas.AddRange(tac_helper_lemmas);
                    typingTacs.Add(typing_tac);
                }

                proofMethods.Add("unfolding " + afterDagProgAccess.BlockInfo().CmdsQualifiedName(afterDag) + "_def");
                proofMethods.Add(ProofUtil.Apply("cfg_dag_rel_tac_single+"));
                proofMethods.Add(TypingTactics(typingTacs, null));
                proofMethods.Add("done");
            }
            else
            {
                proofMethods = new List<string>
                {
                    "using assms",
                    ProofUtil.Apply("rule " + "cfg_dag_empty_propagate_helper"),
                    "apply (assumption, simp)",
                    ProofUtil.Apply(
                        ProofUtil.Simp(afterDagProgAccess.BlockInfo().OutEdgesMembershipLemma(afterDag))),
                    ProofUtil.By(
                        ProofUtil.Simp(
                            afterDagProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterDag),
                            afterDagProgAccess.BlockInfo().CmdsQualifiedName(afterDag) + "_def"
                        )
                    )
                };
            }

            return new LemmaDecl(
                cfgLemmaName,
                ContextElem.CreateWithAssumptions(assumptions),
                conclusion,
                new Proof(proofMethods)
            );
        }

        private Term NstateSameOn(Term normalState1, Term normalState2, Term modSet)
        {
            return
                new TermApp(
                    IsaCommonTerms.TermIdentFromName("nstate_same_on"),
                    boogieContext.varContext,
                    normalInitState1,
                    normalInitState2,
                    modSet);
        }

        private Term StateWellTyped(Term normalState)
        {
            return new TermApp(
                IsaCommonTerms.TermIdentFromName("state_well_typed"),
                boogieContext.absValTyMap,
                boogieContext.varContext,
                boogieContext.rtypeEnv,
                normalState);
        }

        public LemmaDecl EntryLemma(string lemmaName, Block beforeEntryBlock, Block afterEntryBlock,
            Func<Block, string> cfgLemmaName)
        {
            Term numSteps = IsaCommonTerms.TermIdentFromName("j");
            var redCfg = IsaBoogieTerm.RedCFGKStep(
                boogieContext,
                beforeDagProgAccess.CfgDecl(),
                IsaBoogieTerm.CFGConfigNode(new NatConst(beforeDagProgAccess.BlockInfo().BlockIds[beforeEntryBlock]),
                    IsaBoogieTerm.Normal(normalInitState1)),
                numSteps,
                IsaBoogieTerm.CFGConfig(finalNode, finalState));

            var assumptions = new List<Term> {redCfg};
            var dagLemmaAssm = BlockLemmaAssumption(
                boogieContext,
                IsaCommonTerms.EmptyList,
                IsaCommonTerms.EmptyList);
            assumptions.Add(dagLemmaAssm);

            var finalNodeId2 = new SimpleIdentifier("m2'");
            var finalStateId2 = new SimpleIdentifier("s2'");

            var dagVerifiesCfgAssm =
                DagVerifiesCfgAssumption(
                    new NatConst(afterDagProgAccess.BlockInfo().BlockIds[afterEntryBlock]),
                    normalInitState2,
                    finalNodeId2,
                    finalStateId2);
            assumptions.Add(dagVerifiesCfgAssm);

            var preAssm =
                IsaBoogieTerm.ExprAllSat(boogieContext, normalInitState2, beforeDagProgAccess.PreconditionsDecl());
            assumptions.Add(preAssm);

            var afterEntrySuccessors = afterDagCfg.GetSuccessorBlocks(afterEntryBlock);
            if (afterEntrySuccessors.Count() != 1)
                throw new ProofGenUnexpectedStateException("CFG-to-DAG: entry block has only one successor");

            var afterEntrySuc = afterEntrySuccessors.First();

            return new LemmaDecl(
                lemmaName,
                ContextElem.CreateWithAssumptions(assumptions),
                CfgLemmaConclusion(finalNode, finalState),
                new Proof(new List<string>
                {
                    ProofUtil.Apply("rule cfg_dag_helper_entry"),
                    ProofUtil.Apply("rule " + afterDagProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterEntryBlock)),
                    ProofUtil.Apply("erule assms(3)"),
                    ProofUtil.Apply("rule assms(2)"),
                    "unfolding " + afterDagProgAccess.BlockInfo().CmdsQualifiedName(afterEntryBlock) + "_def",
                    ProofUtil.Apply("rule assume_pres_normal[where ?es=" + beforeDagProgAccess.PreconditionsDeclName() +
                                    "]"),
                    ProofUtil.Apply("rule assms(4)"),
                    "unfolding " + beforeDagProgAccess.PreconditionsDeclName() + "_def",
                    "apply simp",
                    ProofUtil.Apply("rule " + afterDagProgAccess.BlockInfo().OutEdgesMembershipLemma(afterEntryBlock)),
                    ProofUtil.Apply(ProofUtil.Simp(
                        afterDagProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterEntrySuc),
                        afterDagProgAccess.BlockInfo().CmdsQualifiedName(afterEntrySuc) + "_def")),
                    ProofUtil.Apply("rule " + afterDagProgAccess.BlockInfo().OutEdgesMembershipLemma(afterEntrySuc)),
                    ProofUtil.By("rule " + ProofUtil.OF(cfgLemmaName(beforeEntryBlock), "assms(1-2)"))
                })
            );
        }

        public IList<LemmaDecl> UnifiedExitLemma(string lemmaName)
        {
            if (afterExitBlock == null)
                throw new ProofGenUnexpectedStateException("incorrect state: assuming that there is no unified exit");

            var finalNodeId2 = new SimpleIdentifier("m2'");
            var finalStateId2 = new SimpleIdentifier("s2'");

            var dagVerifiesCfgAssm =
                DagVerifiesCfgAssumption(
                    new NatConst(afterDagProgAccess.BlockInfo().BlockIds[afterExitBlock]),
                    normalInitState2,
                    finalNodeId2,
                    finalStateId2);

            //this assumption is required to prove that the invariants reduce
            var stateWt = StateWellTyped(normalInitState2);

            var cfgAssumptions = new List<Term>
            {
                dagVerifiesCfgAssm,
                stateWt
            };

            var conclusion = IsaBoogieTerm.ExprAllSat(boogieContext, normalInitState2,
                beforeDagProgAccess.PostconditionsDecl());

            var typingTactics = new List<string>();
            var lemmas = new List<LemmaDecl>();
            foreach (var post in beforeDagData.Postconditions)
            {
                //only need to guarantee postconditions that are not free
                if (!post.Item2)
                {
                     var (typingTac, tacHelperLemmas) = typingTacticGenerator.GenerateTactic(post.Item1);
                     typingTactics.Add(typingTac);
                     lemmas.AddRange(tacHelperLemmas);
                }
            }

            var mainLemma =
                new LemmaDecl(
                    lemmaName,
                    ContextElem.CreateWithAssumptions(cfgAssumptions),
                    conclusion,
                    new Proof(new List<string>
                    {
                        "unfolding expr_all_sat_def " + beforeDagProgAccess.PostconditionsDeclName() + "_def ",
                        ProofUtil.Apply("rule cfg_dag_rel_post_invs_3"),
                        "apply (erule assms(1))",
                        ProofUtil.Apply("rule " +
                                        afterDagProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterExitBlock)),
                        TypingTactics(typingTactics, "assms(2)"),
                        "unfolding " + afterDagProgAccess.BlockInfo().CmdsQualifiedName(afterExitBlock) + "_def",
                        "by cfg_dag_rel_tac_single+"
                    })
                );
            lemmas.Add(mainLemma);
            return lemmas;
        }

        /// <summary>
        ///     first element of returned tuple are the lemmas for the local block proof
        ///     second element of returned tuple is the CFG block proof (i.e., depends on the local lemmas).
        /// </summary>
        public Tuple<IEnumerable<LemmaDecl>, LemmaDecl> BlockLemma(
            Block beforeBlock,
            Block afterBlock,
            IEnumerable<Block> successors,
            Func<Block, string> blockLemmaName,
            Func<Block, string> cfgLemmaName,
            bool singleEdgeCut)
        {
            var beforeCmdsDefName = beforeDagProgAccess.BlockInfo().CmdsQualifiedName(beforeBlock);
            Term beforeCmds = IsaCommonTerms.TermIdentFromName(beforeCmdsDefName);
            var afterCmdsDefName = afterDagProgAccess.BlockInfo().CmdsQualifiedName(afterBlock);
            Term afterCmds = IsaCommonTerms.TermIdentFromName(afterCmdsDefName);

            var finalNodeId2 = new SimpleIdentifier("m2'");
            var finalStateId2 = new SimpleIdentifier("s2'");
            Term finalState2 = new TermIdent(finalStateId2);

            Term preInvs;
            Term havocedVars;
            if (hintManager.IsLoopHead(beforeBlock, out var blockHeadHint))
            {
                preInvs = InvariantsTerm(blockHeadHint.Invariants);
                havocedVars = HavocedVarsTerm(blockHeadHint.ModifiedVars);
            }
            else
            {
                preInvs = IsaCommonTerms.EmptyList;
                havocedVars = IsaCommonTerms.EmptyList;
            }

            var loops = blocksToLoops[beforeBlock];
            var postInvsList = new List<Term>();
            var isPost = false;
            var nSuccessors = successors.Count();

            var localLemmas = new List<LemmaDecl>();

            //one tactic per post invariant: string is tactic and bool is whether it's the postcondition of the program
            var typingTactics = new List<string>();
            Action<Expr> addTypingTactic = inv =>
            {
                var typingTacticTuple = typingTacticGenerator.GenerateTactic(inv);
                localLemmas.AddRange(typingTacticTuple.Item2);
                typingTactics.Add(typingTacticTuple.Item1);
            };

            foreach (var bSuc in successors)
                if (hintManager.IsLoopHead(bSuc, out var hint) && nSuccessors == 1)
                {
                    /* only add invariants if the current block has exactly the loop head as successor, otherwise a block is
                       added between the two, which then asserts the invariants */
                    postInvsList.AddRange(hint.Invariants.Select(inv => basicCmdIsaVisitor.Translate(inv)));

                    foreach (var inv in hint.Invariants) addTypingTactic(inv);
                }

            if (!successors.Any() && afterExitBlock == null)
            {
                //postcondition is at the end: only need to consider non-free postconditions 
                foreach (var post in beforeDagData.Postconditions)
                {
                    if (!post.Item2)
                    {
                       postInvsList.Add(basicCmdIsaVisitor.Translate(post.Item1));
                       addTypingTactic(post.Item1);
                    }
                }
            }

            #region modified variables

            Block loopMod = null;
            TermList loopModTermList = null;
            if (loops.Any())
                /* If the loop is within multiple loops, we need to find the current loop (i.e., the most inner one) to know
                     * what variables are allowed to be modified.
                     * Since the CFG after the CFG-to-DAG transformation is acyclic, we can use the unique labels, which ensure that
                     * if a block occurs before another one, then it has a larger label.
                     * Hence it is sufficient to pick the active loop with the largest label, because all active loops of a block
                     * must be related in some way. If this were not the case, then it would be possible to enter some loop
                     * via two different paths, which cannot happen for reducible CFGs.
                     */
                loopMod = loops.OrderByDescending(
                    beforeLoopHead =>
                        afterDagCfg.GetUniqueIntLabel(beforeToAfterBlock[beforeLoopHead])).Last();
            if (hintManager.IsLoopHead(beforeBlock, out _)) loopMod = beforeBlock;

            if (loopMod != null)
            {
                var hint = hintManager.GetLoopHead(loopMod);
                loopModTermList = HavocedVarsTerm(hint.ModifiedVars);
                localLemmas.Add(BlockModVarsLemma(BlockModVarsLemmaName(beforeBlock), beforeCmds, beforeCmdsDefName,
                    loopModTermList));
            }

            #endregion


            var postInvs = new TermList(postInvsList);

            #region local block lemma

            var assumptions = new List<Term>
            {
                IsaBoogieTerm.RedCmdList(boogieContext, beforeCmds, initState1, finalState)
            };

            Term dagVerifiesAssm =
                TermQuantifier.MetaAll(
                    new List<Identifier> {finalStateId2},
                    null,
                    TermBinary.MetaImplies(
                        IsaBoogieTerm.RedCmdList(boogieContext, afterCmds, initState2, finalState2),
                        TermBinary.Neq(finalState2, IsaBoogieTerm.Failure()))
                );
            assumptions.Add(dagVerifiesAssm);

            var dagLemmaAssm = BlockLemmaAssumption(
                boogieContext,
                havocedVars,
                preInvs);
            assumptions.Add(dagLemmaAssm);

            var conclusion =
                BlockLemmaConclusion(
                    boogieContext,
                    postInvs,
                    afterCmds,
                    singleEdgeCut);

            var proofMethods = new List<string>
            {
                "using assms",
                "apply (rule dag_rel_block_lemma_compact, simp)",
                "unfolding " + beforeCmdsDefName + "_def " + afterCmdsDefName + "_def",
                "apply cfg_dag_rel_tac_single+",
                "apply simp"
            };

            if (blockHeadHint != null)
                foreach (var x in blockHeadHint.ModifiedVars)
                    proofMethods.Add(ProofUtil.Apply(ProofUtil.Simp(beforeDagProgAccess.LookupVarDeclLemma(x))));

            //TODO proof that post invariants reduce to booleans
            proofMethods.Add(TypingTactics(typingTactics, null));
            proofMethods.Add("done");

            var blockLemma = new LemmaDecl(
                blockLemmaName(beforeBlock),
                ContextElem.CreateWithAssumptions(assumptions),
                conclusion,
                new Proof(proofMethods)
            );

            #endregion

            #region cfg lemma

            Term numSteps = IsaCommonTerms.TermIdentFromName("j");


            var redCfg = IsaBoogieTerm.RedCFGKStep(
                boogieContext,
                beforeDagProgAccess.CfgDecl(),
                IsaBoogieTerm.CFGConfigNode(new NatConst(beforeDagProgAccess.BlockInfo().BlockIds[beforeBlock]),
                    IsaBoogieTerm.Normal(normalInitState1)),
                numSteps,
                IsaBoogieTerm.CFGConfig(finalNode, finalState));

            var cfgAssumptions = new List<Term>
            {
                redCfg,
                dagLemmaAssm
            };

            var dagVerifiesCfgAssm =
                DagVerifiesCfgAssumption(
                    new NatConst(afterDagProgAccess.BlockInfo().BlockIds[afterBlock]),
                    normalInitState2,
                    finalNodeId2,
                    finalStateId2);

            cfgAssumptions.Add(dagVerifiesCfgAssm);


            var cfgAssumptionNames = new List<string>
            {
                redCfgName, dagAssmsName, dagVerifiesName
            };

            foreach (var loopBlock in blocksToLoops[beforeBlock])
            {
                var hint = hintManager.GetLoopHead(loopBlock);
                var inductionHyp = LoopIndHypAssumption(
                    boogieContext,
                    beforeDagProgAccess.CfgDecl(),
                    HavocedVarsTerm(hint.ModifiedVars),
                    InvariantsTerm(hint.Invariants),
                    normalInitState1,
                    new NatConst(beforeDagProgAccess.BlockInfo().BlockIds[loopBlock]),
                    numSteps);

                cfgAssumptions.Add(inductionHyp);
                cfgAssumptionNames.Add(LoopIndHypName(loopBlock));
            }

            Proof cfgProof;
            if (!successors.Any())
            {
                cfgProof = GenerateProofExitNode(beforeBlock, afterBlock, blockLemmaName, cfgLemmaName);
            }
            else if (blockHeadHint == null)
            {
                var proofData = new NonLoopHeadProofData(
                    redCfgName,
                    dagAssmsName,
                    dagVerifiesName,
                    LoopIndHypName
                );
                cfgProof = GenerateProofBody(beforeBlock, afterBlock, proofData, blockLemmaName, cfgLemmaName,
                    successors);
            }
            else
            {
                cfgProof =
                    GenerateProofLoopHead(beforeBlock, afterBlock, loopModTermList, blockLemmaName, cfgLemmaName,
                        successors);
            }

            var cfgLemma = new LemmaDecl(
                cfgLemmaName(beforeBlock),
                ContextElem.CreateWithAssumptions(cfgAssumptions, cfgAssumptionNames),
                CfgLemmaConclusion(finalNode, finalState),
                cfgProof
            );

            #endregion

            localLemmas.Add(blockLemma);

            return new Tuple<IEnumerable<LemmaDecl>, LemmaDecl>(localLemmas, cfgLemma);
        }

        private Term CfgLemmaConclusion(Term finalNode, Term finalState)
        {
            return CfgLemmaConclusion(boogieContext, beforeDagProgAccess.PostconditionsDecl(),
                finalNode, finalState);
        }

        public static Term CfgLemmaConclusion(BoogieContextIsa boogieContext, Term post, Term finalNode,
            Term finalState)
        {
            return new TermApp(
                IsaCommonTerms.TermIdentFromName("Semantics.valid_configuration"),
                boogieContext.absValTyMap,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                post,
                finalNode,
                finalState);
        }

        private LemmaDecl BlockModVarsLemma(string lemmaName, Term cmds, string cmdsDef, Term modVarsList)
        {
            Term statement =
                new TermApp(
                    IsaCommonTerms.TermIdentFromName("mods_contained_in"),
                    IsaCommonTerms.SetOfList(modVarsList),
                    cmds);

            var proof =
                new Proof(
                    new List<string>
                    {
                        "unfolding " + cmdsDef + "_def",
                        "by simp"
                    }
                );

            return new LemmaDecl(lemmaName, statement, proof);
        }

        private Proof GenerateProofBody(
            Block beforeBlock,
            Block afterBlock,
            ICfgToDagProofData proofData,
            Func<Block, string> blockLemmaName,
            Func<Block, string> cfgLemmaName,
            IEnumerable<Block> successors)
        {
            var sb = new StringBuilder();
            GenerateProofBody(sb, false, beforeBlock, afterBlock, proofData, blockLemmaName, cfgLemmaName,
                successors);
            return new Proof(new List<string> {sb.ToString()});
        }

        private void GenerateProofBody(
            StringBuilder sb,
            bool isLoopHead,
            Block beforeBlock,
            Block afterBlock,
            ICfgToDagProofData proofData,
            Func<Block, string> blockLemmaName,
            Func<Block, string> cfgLemmaName,
            IEnumerable<Block> successors)
        {
            var loops = blocksToLoops[beforeBlock];
            var helperThm = loops.Any() || isLoopHead ? "cfg_dag_helper_2" : "cfg_dag_helper_1";

            sb.AppendLine(ProofUtil.Apply(
                ProofUtil.Rule(
                    ProofUtil.OF(helperThm, proofData.RedCfgAssmName(), "_", "_", proofData.DagVerifiesName(),
                        proofData.DagAssmName()))));
            sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule(beforeDagProgAccess.BlockInfo()
                .BlockCmdsMembershipLemma(beforeBlock))));
            sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule(afterDagProgAccess.BlockInfo()
                .BlockCmdsMembershipLemma(afterBlock))));
            sb.AppendLine(ProofUtil.Apply("assumption+"));
            sb.AppendLine(ProofUtil.Apply("rule " + blockLemmaName(beforeBlock)));
            sb.AppendLine(ProofUtil.Apply("assumption+"));

            if (loops.Any() || isLoopHead)
                sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule(BlockModVarsLemmaName(beforeBlock))));

            //out edges non-empty
            sb.AppendLine(
                ProofUtil.Apply(ProofUtil.Simp(beforeDagProgAccess.BlockInfo()
                    .OutEdgesMembershipLemma(beforeBlock))));
            //out edges in successor
            sb.AppendLine(
                ProofUtil.Apply(ProofUtil.Simp(beforeDagProgAccess.BlockInfo()
                    .OutEdgesMembershipLemma(beforeBlock))));

            /* handle each successor
             * assume that the edge list in embedding coincides with the iteration order of the successors
             */
            foreach (var bSuc in successors)
            {
                sb.AppendLine(ProofUtil.Apply("erule member_elim"));
                if (loops.Contains(bSuc) || beforeBlock.Equals(bSuc))
                {
                    //Edge is backedge --> need to apply IH

                    /* We need to check whether a new backedge block was added, which contains the assertion of the invariant.
                       If so, then we need to get the invariant satisfiability from that block.
                    */
                    foreach (var afterSuc in afterDagCfg.GetSuccessorBlocks(afterBlock))
                    {
                        if (hintManager.IsNewBackedgeBlock(afterSuc, out var loopHead, out var _) &&
                            loopHead == bSuc)
                        {
                          //TODO separate function for this and share code with case below
                          var afterSucId = afterDagProgAccess.BlockInfo().BlockIds[afterSuc];
                          sb.AppendLine("(* proof strategy for new backedge block *)");
                          sb.AppendLine("apply (erule allE[where x=" + afterSucId + "])");
                          sb.AppendLine(ProofUtil.Apply(
                            ProofUtil.Simp(afterDagProgAccess.BlockInfo()
                              .OutEdgesMembershipLemma(afterBlock))));
                          sb.AppendLine(ProofUtil.Apply(ProofUtil.Simp("member_rec(1)")));
                          sb.AppendLine(ProofUtil.Apply("erule " + cfgLemmaName(afterSuc)));
                          sb.AppendLine(ProofUtil.Apply("assumption, assumption, simp"));
                          sb.AppendLine("(* finish proof strategy for new backedge block *)");
                          break;
                        }
                    }

                    if (beforeBlock.Equals(bSuc))
                    {
                        //the backedge is to the current block (i.e., self-loop): need to use generated induction hypothesis
                        // ProveLoopHeadInductionHyp(sb, beforeBlock, proofData);
                        sb.AppendLine(ProofUtil.Apply("erule backedge_loop_head_helper"));
                        sb.AppendLine("apply (erule less.IH)");
                        sb.AppendLine("apply assumption+");
                        sb.AppendLine("using " + state2WellTyLoopHeadName + " apply assumption");
                        sb.AppendLine("apply (assumption, simp)");
                        sb.AppendLine(ProofUtil.Apply("rule " + stateRelLoopHeadName));
                        sb.AppendLine("apply assumption");
                    }
                    else
                    {
                        //the backedge is not to the current block: can use induction hypothesis in block lemma assumption
                        sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule("loop_ih_apply[where ?j'=\"j-1\"]")));
                        sb.AppendLine(ProofUtil.Apply(ProofUtil.Rule(proofData.LoopIndHypName(bSuc))));
                        sb.AppendLine(ProofUtil.Apply("simp, simp"));
                        sb.AppendLine("unfolding dag_lemma_assms_def");
                        sb.AppendLine(ProofUtil.Apply("intro conjI, simp"));
                        sb.AppendLine(ProofUtil.Apply("rule nstate_same_on_sym"));
                        if (loops.Count > 1)
                        {
                            /* if the block is within more than one loop, then the modified variables proved for the block may
                                 be a strict subset of the modified variables of the loop associated with the IH*/
                                sb.AppendLine(ProofUtil.Apply("erule nstate_same_on_subset_2"));
                        }
                        sb.AppendLine(ProofUtil.Apply("simp"));
                        sb.AppendLine(ProofUtil.Apply("simp"));
                        sb.AppendLine(ProofUtil.Apply("rule " + ProofUtil.OF("dag_lemma_assms_state_wt_1",
                            proofData.DagAssmName())));
                    }
                }
                else
                {
                    /* we need to check whether the edge to the successor also exists in the DAG
                       if not, then an edge was added in-between and we need to apply an additional lemma to
                       to propagate the execution in the DAG 
                     */
                    var bSucAfter = beforeToAfterBlock[bSuc];
                    int bSucAfterId;
                    var afterSuccessors = afterDagCfg.GetSuccessorBlocks(afterBlock);
                    Block addedBlock = null;
                    if (afterSuccessors.Contains(bSucAfter))
                    {
                        bSucAfterId = afterDagProgAccess.BlockInfo().BlockIds[bSucAfter];
                    }
                    else
                    {
                        // need to find the empty block that was added in between 
                        var bSucAfterIsLoopHead = hintManager.IsLoopHead(bSuc, out _);
                        
                        foreach (var afterSuc in afterSuccessors)
                        {
                            var afterSucSuccessors = afterDagCfg.GetSuccessorBlocks(afterSuc);
                            
                            // block in between must have a single expected successor
                            if (afterSucSuccessors.Count() != 1  || !afterSucSuccessors.First().Equals(bSucAfter))
                            {
                              continue;
                            }

                            /** if expected successor is not a loop head, then the block in between must be empty,
                             *  otherwise the block in between must be a new pre entry loop block (which asserts the loop invariant)
                             */
                            if ( (!bSucAfterIsLoopHead && !afterSuc.Cmds.Any()) 
                                ||
                                 (bSucAfterIsLoopHead && hintManager.IsNewPreLoopEntryBlock(afterSuc)) )
                            {
                                addedBlock = afterSuc;
                                break; //if there are multiple blocks that satisfy the criteria, then we can pick any, so break here
                            } 
                        }

                        if (addedBlock == null)
                        {
                          throw new ProofGenUnexpectedStateException("Could not find new target block added in between two source blocks");
                        }
                          
                        bSucAfterId = afterDagProgAccess.BlockInfo().BlockIds[addedBlock];
                    }

                    sb.AppendLine("apply simp");
                    sb.AppendLine("apply (erule allE[where x=" + bSucAfterId + "])");
                    sb.AppendLine(ProofUtil.Apply(
                        ProofUtil.Simp(afterDagProgAccess.BlockInfo()
                            .OutEdgesMembershipLemma(afterBlock))));
                    sb.AppendLine(ProofUtil.Apply(ProofUtil.Simp("member_rec(1)")));
                    if (addedBlock != null)
                    {
                        sb.AppendLine(ProofUtil.Apply("erule " + cfgLemmaName(addedBlock)));
                        sb.AppendLine(ProofUtil.Apply("assumption, assumption, simp"));
                    }

                    sb.AppendLine(ProofUtil.Apply("rule " + cfgLemmaName(bSuc)));
                    sb.AppendLine("apply simp");
                    sb.AppendLine("unfolding dag_lemma_assms_def");
                    sb.AppendLine("apply (intro conjI)");
                    sb.AppendLine("apply simp");
                    sb.AppendLine(hintManager.IsLoopHead(bSuc, out _)
                        ? "apply (erule nstate_same_on_empty_subset)"
                        : "apply simp");

                    sb.AppendLine(ProofUtil.Apply("fastforce"));
                    sb.AppendLine(ProofUtil.Apply("simp"));
                    sb.AppendLine(ProofUtil.Apply("simp"));
                    /* We need to prove all the induction hypotheses for the loops that the successor is in.
                     * We can be sure that every loop that the successor is, the current block is in too (since the CFG is reducible).
                     * Thus, we just need to propagate the induction hypotheses.
                     * If the current block B is a loop head, then a slightly different proof needs to be used to propagate the induction
                     * hypothesis of B.
                     */
                    var loopsSuc = blocksToLoops[bSuc];
                    foreach (var loopSuc in loopsSuc)
                        if (loopSuc != beforeBlock)
                        {
                            if (loops.Count == 1 && !isLoopHead)
                            {
                                sb.AppendLine(ProofUtil.Apply("rule loop_ih_convert_pred"));
                                sb.AppendLine("using " + proofData.LoopIndHypName(loopSuc) +
                                              " apply simp");
                                sb.AppendLine("apply simp");
                                sb.AppendLine(ProofUtil.Apply("rule " +
                                                              ProofUtil.OF("dag_lemma_assms_state_wt_1",
                                                                  proofData.DagAssmName())));
                            }
                            else
                            {
                                /* we are in multiple loops, hence need to take into account that modified vars associated
                                 * with the active loop is subset of those specified in loop_ih
                                 */
                                sb.AppendLine(ProofUtil.Apply("rule loop_ih_convert_subset_pred"));
                                sb.AppendLine("using " + proofData.LoopIndHypName(loopSuc) +
                                              " apply simp");
                                sb.AppendLine("apply assumption");
                                sb.AppendLine(ProofUtil.Apply("rule " +
                                                              ProofUtil.OF("dag_lemma_assms_state_wt_1",
                                                                  proofData.DagAssmName())));
                                sb.AppendLine("apply simp");
                            }
                        }
                        else
                        {
                            //we need to prove the induction hypothesis of the current loop head block
                            ProveLoopHeadInductionHyp(sb, beforeBlock, proofData);
                        }
                }
            }

            sb.AppendLine("by (simp add: member_rec(2))");
        }

        /// <summary>
        ///     return tactics to prove expressions reduce using the input tactics for well-typedness
        /// </summary>
        /// <param name="typingTactics"></param>
        /// <param name="stateWtThm">state well-typed assumption if the assumption is not already in the context otherwise null</param>
        /// <returns></returns>
        private string TypingTactics(IEnumerable<string> typingTactics, string stateWtThm)
        {
            var sb = new StringBuilder();
            sb.Append("apply simp");
            if (!typingTactics.Any())
                return sb.ToString();

            sb.AppendLine();

            if (typingTactics.Count() != 1) sb.AppendLine(ProofUtil.Apply("intro conjI"));

            foreach (var typingTac in typingTactics)
            {
                sb.AppendLine(ProofUtil.Apply((stateWtThm == null ? "erule " : "rule ") +
                                              ProofUtil.OF("" +
                                                           "type_safety_top_level_inv",
                                                  funContextWfName,
                                                  beforeDagProgAccess.FuncsWfTyLemma(),
                                                  beforeDagProgAccess.VarContextWfTyLemma())));
                if (stateWtThm != null)
                    sb.AppendLine(ProofUtil.Apply("rule " + stateWtThm));

                //expression wf
                sb.AppendLine(ProofUtil.Apply("simp"));
                //expression well-typed
                sb.AppendLine(typingTac);
            }

            return sb.ToString();
        }

        //proves the loop induction hypothesis of the current loop head 
        private void ProveLoopHeadInductionHyp(StringBuilder sb, Block loopHead,
            ICfgToDagProofData proofData)
        {
            sb.AppendLine(ProofUtil.Apply("rule loop_ih_prove"));
            sb.AppendLine(ProofUtil.Apply("rule less.IH"));
            sb.AppendLine(
                ProofUtil.Apply("erule strictly_smaller_helper, assumption, assumption"));
            sb.AppendLine("unfolding dag_lemma_assms_def");
            sb.AppendLine(ProofUtil.Apply("intro conjI, simp"));
            sb.AppendLine(ProofUtil.Apply("rule " +
                                          ProofUtil.OF("nstate_same_on_transitive_2", "_",
                                              "_", stateRelLoopHeadName)));
            sb.AppendLine(ProofUtil.Apply("(fastforce, simp, simp)"));
            sb.AppendLine(ProofUtil.Apply("rule " +
                                          ProofUtil.OF("dag_lemma_assms_state_wt_2",
                                              proofData.DagAssmName())));

            var loops = blocksToLoops[loopHead];
            foreach (var b in loops)
            {
                sb.AppendLine(ProofUtil.Apply("rule loop_ih_convert_subset_smaller_2"));
                sb.AppendLine("using " + proofData.LoopIndHypName(b) + " apply simp");
                sb.AppendLine(ProofUtil.Apply("simp, fastforce, assumption"));
                sb.AppendLine(ProofUtil.Apply("rule " +
                                              ProofUtil.OF("dag_lemma_assms_state_wt_1",
                                                  proofData.DagAssmName())));
                sb.AppendLine("apply simp");
            }
        }

        private Proof GenerateProofExitNode(
            Block beforeBlock,
            Block afterBlock,
            Func<Block, string> blockLemmaName,
            Func<Block, string> cfgLemmaName
        )
        {
            var sb = new StringBuilder();
            if (afterExitBlock == null)
            {
                //no new unified exit block was created
                sb.AppendLine(ProofUtil.Apply("rule " +
                                              ProofUtil.OF("cfg_dag_helper_return_1",
                                                  "assms(1)")));
                sb.AppendLine(ProofUtil.Apply("rule " +
                                              beforeDagProgAccess.BlockInfo()
                                                  .BlockCmdsMembershipLemma(beforeBlock)));
                sb.AppendLine(ProofUtil.Apply("rule " +
                                              afterDagProgAccess.BlockInfo()
                                                  .BlockCmdsMembershipLemma(afterBlock)));
                sb.AppendLine(ProofUtil.Apply("erule " + dagVerifiesName));
                sb.AppendLine(ProofUtil.Apply("rule " + dagAssmsName));
                sb.AppendLine("unfolding " + beforeDagProgAccess.PostconditionsDeclName() + "_def");
                sb.AppendLine(ProofUtil.Apply("rule " + blockLemmaName(beforeBlock)));
                sb.AppendLine("apply assumption+");
                sb.AppendLine(
                    ProofUtil.By("rule " + beforeDagProgAccess.BlockInfo()
                        .OutEdgesMembershipLemma(beforeBlock)));
            }
            else
            {
                //a new unified exit block was created
                sb.AppendLine(ProofUtil.Apply("rule " +
                                              ProofUtil.OF("cfg_dag_helper_return_2",
                                                  redCfgName)));
                sb.AppendLine(ProofUtil.Apply("rule " +
                                              beforeDagProgAccess.BlockInfo()
                                                  .BlockCmdsMembershipLemma(beforeBlock)));
                sb.AppendLine(
                    ProofUtil.Apply("rule " + afterDagProgAccess.BlockInfo()
                        .BlockCmdsMembershipLemma(afterBlock)));
                sb.AppendLine(ProofUtil.Apply("erule " + dagVerifiesName));
                sb.AppendLine(ProofUtil.Apply("rule " + dagAssmsName));
                sb.AppendLine(ProofUtil.Apply("erule " + blockLemmaName(beforeBlock)));
                sb.AppendLine("apply assumption+");
                sb.AppendLine(ProofUtil.Apply("rule " +
                                              beforeDagProgAccess.BlockInfo()
                                                  .OutEdgesMembershipLemma(beforeBlock)));

                sb.AppendLine(ProofUtil.Apply("rule " +
                                              afterDagProgAccess.BlockInfo()
                                                  .OutEdgesMembershipLemma(afterBlock)));
                sb.AppendLine(ProofUtil.Apply("erule " + cfgLemmaName(afterExitBlock)));
                sb.AppendLine("by assumption");
            }

            return new Proof(new List<string> {sb.ToString()});
        }

        private Proof GenerateProofLoopHead(
            Block beforeBlock,
            Block afterBlock,
            Term modVars,
            Func<Block, string> blockLemmaName,
            Func<Block, string> cfgLemmaName,
            IEnumerable<Block> successors)
        {
            var sb = new StringBuilder();
            var loops = blocksToLoops[beforeBlock];
            sb.AppendLine("using " + redCfgName + " " + dagAssmsName +
                          (loops.Any() ? " assms(4-)" : ""));
            sb.AppendLine("proof (induction j arbitrary: ns1 rule: less_induct)");
            sb.AppendLine("case (less j)");
            sb.AppendLine("show ?case");
            sb.AppendLine("proof (cases j)");
            sb.AppendLine(
                "case 0 with less.prems(1) show ?thesis unfolding Semantics.valid_configuration_def by auto");
            sb.AppendLine("next");
            sb.AppendLine("case (Suc j')");
            sb.Append("from less(3) have " + stateRelLoopHeadName + ":");
            sb.Append("\"" + NstateSameOn(normalInitState1, normalInitState2,
                IsaCommonTerms.SetOfList(modVars)) + "\"");
            sb.AppendLine("by (simp add: dag_lemma_assms_def)");
            sb.Append("from less(3) have " + state2WellTyLoopHeadName + ":");
            sb.Append("\"" + StateWellTyped(normalInitState2) + "\"");
            sb.AppendLine("by (simp add: dag_lemma_assms_def)");
            sb.AppendLine("show ?thesis");

            var proofData = new LoopHeadProofData(dagVerifiesName, loops);

            GenerateProofBody(sb, true, beforeBlock, afterBlock, proofData, blockLemmaName,
                cfgLemmaName, successors);
            sb.AppendLine("qed");
            sb.AppendLine("qed");
            return new Proof(new List<string> {sb.ToString()});
        }

        private Term DagVerifiesCfgAssumption(
            Term initialStateNode,
            Term initialNormalState,
            Identifier finalNodeId2,
            Identifier finalStateId2,
            bool useMetaConnectives = true
        )
        {
            Term finalNode2 = new TermIdent(finalNodeId2);
            Term finalState2 = new TermIdent(finalStateId2);

            Func<IList<Identifier>, IList<TypeIsa>, Term, TermQuantifier> forallConstructor;
            Func<Term, Term, TermBinary> impliesConstructor;
            if (useMetaConnectives)
            {
                forallConstructor = TermQuantifier.MetaAll;
                impliesConstructor = TermBinary.MetaImplies;
            }
            else
            {
                forallConstructor = TermQuantifier.ForAll;
                impliesConstructor = TermBinary.Implies;
            }

            return
                forallConstructor(
                    new List<Identifier> {finalNodeId2, finalStateId2},
                    null,
                    impliesConstructor(
                        IsaBoogieTerm.RedCFGMulti(boogieContext,
                            afterDagProgAccess.CfgDecl(),
                            IsaBoogieTerm.CFGConfigNode(
                                initialStateNode, IsaBoogieTerm.Normal(initialNormalState)
                            ),
                            IsaBoogieTerm.CFGConfig(finalNode2, finalState2)
                        ),
                        TermBinary.Neq(finalState2, IsaBoogieTerm.Failure()))
                );
        }

        private Term BlockLemmaAssumption(
            BoogieContextIsa boogieContext,
            Term havocedVars,
            Term preInvs
        )
        {
            return new TermApp(
                IsaCommonTerms.TermIdentFromName("dag_lemma_assms"),
                boogieContext.absValTyMap,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                havocedVars,
                preInvs,
                normalInitState1,
                normalInitState2
            );
        }

        private Term BlockLemmaConclusion(
            BoogieContextIsa boogieContext,
            Term postInvs,
            Term cmds2,
            bool singleEdgeCut
        )
        {
            return new TermApp(
                IsaCommonTerms.TermIdentFromName("dag_lemma_conclusion"),
                boogieContext.absValTyMap,
                boogieContext.methodContext,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                postInvs,
                cmds2,
                normalInitState2,
                finalState,
                new BoolConst(singleEdgeCut)
            );
        }

        private Term LoopIndHypAssumption(
            BoogieContextIsa boogieContext,
            Term cfg,
            Term modVars,
            Term invs,
            Term normalState,
            Term loopHeadNode,
            Term numSteps
        )
        {
            return new TermApp(
                IsaCommonTerms.TermIdentFromName("loop_ih"),
                boogieContext.absValTyMap,
                boogieContext.methodContext,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                cfg,
                modVars,
                invs,
                beforeDagProgAccess.PostconditionsDecl(),              
                normalState,
                finalState,
                loopHeadNode,
                finalNode,
                numSteps
            );
        }

        private string LoopIndHypName(Block b)
        {
            return "IH_" + namer.GetName(b, b.Label);
        }

        private string BlockModVarsLemmaName(Block b)
        {
            return "Mods_" + namer.GetName(b, b.Label);
        }
    }
}