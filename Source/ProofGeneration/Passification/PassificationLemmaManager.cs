using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.ML;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;

namespace ProofGeneration.Passification
{
    internal class PassificationLemmaManager
    {
        private readonly StateRelationData _oldStateRelationData;

        private readonly PassiveRelationGen _relationGen;

        private readonly BoogieContextIsa boogieContext;
        private readonly CFGRepr cfg;
        private readonly TermIdent constrainedVars = IsaCommonTerms.TermIdentFromName("D0");
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");

        private readonly string funAssmsName = "fun_assms";
        private readonly Term initState;

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");

        private readonly OldVarFinder oldVarFinder = new();
        private readonly IDictionary<Block, Block> origToPassiveBlock;
        private readonly IProgramAccessor passiveProgramAccessor;

        private readonly TermIdent passiveStates = IsaCommonTerms.TermIdentFromName("U0");
        private readonly TermIdent passiveVarContext;
        private readonly IVariableTranslation<Variable> passiveVarTranslation;

        private readonly IProgramAccessor programAccessor;

        private readonly Dictionary<Block, int> smallestRequiredVersionDict = new Dictionary<Block, int>();
        private readonly TermIdent stateRel = IsaCommonTerms.TermIdentFromName("R");
        private readonly string varAssmsName = "var_assms";

        private readonly IVariableTranslation<Variable> varTranslation;


        public PassificationLemmaManager(
            CFGRepr cfg,
            IDictionary<Block, Block> origToPassiveBlock,
            IProgramAccessor programAccessor,
            IProgramAccessor passiveProgramAccessor,
            Tuple<string, string> varContextNonPassivePassive,
            StateRelationData oldStateRelationData,
            PassiveRelationGen relationGen,
            IVariableTranslationFactory varTranslationFactory,
            IVariableTranslationFactory passiveTranslationFactory)
        {
            this.cfg = cfg;
            this.origToPassiveBlock = origToPassiveBlock;
            this.programAccessor = programAccessor;
            this.passiveProgramAccessor = passiveProgramAccessor;
            _oldStateRelationData = oldStateRelationData;
            _relationGen = relationGen;
            initState = IsaBoogieTerm.Normal(normalInitState);
            varTranslation = varTranslationFactory.CreateTranslation().VarTranslation;
            passiveVarTranslation = passiveTranslationFactory.CreateTranslation().VarTranslation;
            //separate unique namer for function interpretations (since they already have a name in uniqueNamer): possible clashes

            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName(varContextNonPassivePassive.Item1),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.TermIdentFromName("\\<Omega>")
            );
            passiveVarContext = IsaCommonTerms.TermIdentFromName(varContextNonPassivePassive.Item2);
        }

        //must be called in a topological backwards order
        public Tuple<LemmaDecl, LemmaDecl> GenerateBlockLemma(Block block, string localLemmaName,
            Func<Block, string> cfgLemmaNameFunc)
        {
            var cmdsDefName = programAccessor.BlockInfo().CmdsQualifiedName(block);
            Term cmds = IsaCommonTerms.TermIdentFromName(cmdsDefName);

            var passiveBlock = origToPassiveBlock[block];
            var passiveCmdsDefName = passiveProgramAccessor.BlockInfo().CmdsQualifiedName(passiveBlock);
            Term passiveCmds = IsaCommonTerms.TermIdentFromName(passiveCmdsDefName);

            #region compute variable relation update  information

            var successors = cfg.GetSuccessorBlocks(block);
            var varRelUpdates = _relationGen.GenerateVariableRelUpdates(block, out _);

            var constrainedPassiveVars = new List<Term>();
            var modifiedVarRelTerm = new List<Term>();
            var lookupTyUpdatesLemmas = new List<Tuple<string, string>>();

            foreach (var tuple in varRelUpdates)
            {
                var origVar = tuple.Item1;
                if (varTranslation.TryTranslateVariableId(origVar, out var origVarTerm, out _))
                {
                    if (tuple.Item2 is IdentifierExpr ie)
                    {
                        var passiveVar = ie.Decl;
                        if (passiveVarTranslation.TryTranslateVariableId(passiveVar, out var passiveVarTerm, out _))
                        {
                            modifiedVarRelTerm.Add(new TermTuple(origVarTerm, IsaCommonTerms.Inl(passiveVarTerm)));
                            /* don't add variable to newly constrained variables if update is associated with constant propagation
                             * in which case the variable is not newly constrained */
                            if (!tuple.Item3) constrainedPassiveVars.Add(passiveVarTerm);
                            lookupTyUpdatesLemmas.Add(
                                Tuple.Create(programAccessor.LookupVarTyLemma(origVar),
                                    passiveProgramAccessor.LookupVarTyLemma(passiveVar))
                            );
                        }
                        else
                        {
                            throw new ProofGenUnexpectedStateException(GetType(), "Could not translate variables.");
                        }
                    }
                    else if (tuple.Item2 is LiteralExpr lit)
                    {
                        var litTerm = IsaBoogieTerm.Literal(lit);
                        modifiedVarRelTerm.Add(new TermTuple(origVarTerm, IsaCommonTerms.Inr(litTerm)));
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException(GetType(),
                            "Unexpected orig variable to passive expression mapping");
                    }
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "Could not translate variables.");
                }
            }

            //find smallest required version
            var smallestRequired = 1000; //TODO: set to correct initial value
            if (constrainedPassiveVars.Any())
                smallestRequired = constrainedPassiveVars.Select(t => (t as NatConst).Val).Min();
            else if (successors.Any())
                smallestRequired = successors.Select(suc => smallestRequiredVersionDict[suc]).Min();

            smallestRequiredVersionDict[block] = smallestRequired;

            #endregion

            var passiveWitness = new PassificationWitness(
                passiveVarContext,
                new TermList(constrainedPassiveVars),
                new TermList(modifiedVarRelTerm),
                stateRel,
                _oldStateRelationData.StateRel,
                passiveStates,
                constrainedVars);

            var stateRelation = _relationGen.GenerateStateRelation(block);
            var stateRelationAssms = new List<Term>();

            foreach (var tupleRel in stateRelation)
            {
                var (origVar, passiveExpr) = tupleRel;
                stateRelationAssms.Add(StateRelAssm(stateRel, origVar, passiveExpr));
            }

            #region local block lemma

            var assumptions = new List<Term>
            {
                IsaBoogieTerm.RedCmdList(boogieContext, cmds, initState, finalState),
                BlockLemmaAssumption(boogieContext, passiveWitness, normalInitState)
            };

            assumptions.AddRange(stateRelationAssms);

            //conclusion
            var conclusion =
                BlockLemmaConclusion(boogieContext, passiveWitness, passiveCmds, finalState);

            var oldLocalVarLemmas = OldLocalVariableLemmas(block);

            var proofMethods =
                new List<string>
                {
                    ProofUtil.Apply("rule passification_block_lemma_compact[OF assms(1-2)]"),
                    "unfolding " + ProofUtil.DefLemma(cmdsDefName) + " " + ProofUtil.DefLemma(passiveCmdsDefName),
                    ProofUtil.Apply("passive_rel_tac" + (stateRelation.Any() ? " R_def: assms(3-)" : "") +
                                    (_oldStateRelationData.VarToLookupLemma.Any()
                                        ? " R_old_def: " + _oldStateRelationData.AllLemmasName
                                        : "") +
                                    (oldLocalVarLemmas.Any()
                                        ? " LocVar_assms:" + string.Join(" ", oldLocalVarLemmas)
                                        : "")
                    )
                };

            proofMethods.Add("apply (unfold type_rel_def, simp, (intro conjI)?)");

            proofMethods.AddRange(
                lookupTyUpdatesLemmas.Select(t => ProofUtil.Apply(ProofUtil.Simp(t.Item1, t.Item2)))
            );

            proofMethods.Add("by simp");

            var proof = new Proof(proofMethods);

            var localLemma = new LemmaDecl(localLemmaName, ContextElem.CreateWithAssumptions(assumptions), conclusion,
                proof);

            #endregion

            #region cfg lemma

            var redCfg = IsaBoogieTerm.RedCFGMulti(
                boogieContext,
                programAccessor.CfgDecl(),
                IsaBoogieTerm.CFGConfigNode(new NatConst(programAccessor.BlockInfo().BlockIds[block]),
                    IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNode, finalState));

            var cfgAssumptions = new List<Term>
            {
                redCfg,
                CfgBlockLemmaAssumption(boogieContext, passiveWitness, smallestRequired, normalInitState)
            };

            cfgAssumptions.AddRange(stateRelationAssms);

            var cfgConclusion = CfgLemmaConclusion(
                boogieContext,
                passiveWitness,
                passiveProgramAccessor,
                IsaCommonTerms.Inl(new NatConst(programAccessor.BlockInfo().BlockIds[block])),
                finalState);

            var cfgProof = CfgLemmaProof(
                block,
                localLemmaName,
                successors.Select(cfgLemmaNameFunc).ToList(),
                stateRelationAssms.Any()
            );

            var cfgLemma = new LemmaDecl(cfgLemmaNameFunc(block), ContextElem.CreateWithAssumptions(cfgAssumptions),
                cfgConclusion, cfgProof);

            #endregion

            return Tuple.Create(localLemma, cfgLemma);
        }

        /// <summary>
        ///     return all lookup lemmas for locals or parameters that appear within old expressions in <paramref name="block" />
        /// </summary>
        private IEnumerable<string> OldLocalVariableLemmas(Block block)
        {
            var oldLocalVars = oldVarFinder.FindOldVariables(block, v => v is Formal || v is LocalVariable);
            return oldLocalVars.Select(v => programAccessor.MembershipLemma(v));
        }

        private Term StateRelAssm(Term stateRelation, Variable origVar, Expr passiveExpr)
        {
            if (varTranslation.TryTranslateVariableId(origVar, out var origVarTerm, out _))
            {
                Term rhsValue;
                if (passiveExpr is IdentifierExpr ie)
                {
                    if (passiveVarTranslation.TryTranslateVariableId(ie.Decl, out var passiveVarTerm, out _))
                        rhsValue = IsaCommonTerms.Inl(passiveVarTerm);
                    else
                        throw new ProofGenUnexpectedStateException(GetType(), "can't translate variable");
                }
                else if (passiveExpr is LiteralExpr lit)
                {
                    rhsValue = IsaCommonTerms.Inr(IsaBoogieTerm.Literal(lit));
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "unsupported passive expression");
                }

                return TermBinary.Eq(
                    new TermApp(stateRelation, origVarTerm),
                    IsaCommonTerms.SomeOption(rhsValue));
            }

            throw new ProofGenUnexpectedStateException(GetType(), "unsupported passive expression");
        }

        public IList<OuterDecl> Prelude()
        {
            var result = new List<OuterDecl>();
            /*
            if(programVariables.Any())
            {
                result.Add(new LemmasDecl(varAssmsName, VarAssumptionLabels()));
            }

            if (methodData.Functions.Any())
            {
                result.Add(new LemmasDecl(funAssmsName, FunAssumptionLabels()));
            }
            */

            result.Add(new DeclareDecl("One_nat_def[simp del]"));

            return result;
        }

        private static Term BlockLemmaAssumption(
            BoogieContextIsa boogieContextSource,
            PassificationWitness passificationWitness,
            Term initNonPassiveState)
        {
            var args = new List<Term>
            {
                boogieContextSource.absValTyMap,
                boogieContextSource.methodContext,
                boogieContextSource.varContext,
                passificationWitness.VarContext,
                boogieContextSource.funContext,
                boogieContextSource.rtypeEnv,
                passificationWitness.ModifiedVars,
                passificationWitness.StateRelation,
                passificationWitness.OldStateRelation,
                passificationWitness.PassiveStates,
                passificationWitness.ConstrainedVariables,
                initNonPassiveState
            };
            // IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables, passificationWitness.ModifiedVars),

            return new TermApp(IsaCommonTerms.TermIdentFromName("passive_lemma_assms"), args);
        }


        private static Term CfgBlockLemmaAssumption(
            BoogieContextIsa boogieContextSource,
            PassificationWitness passificationWitness,
            int smallestFreeVar,
            Term initNonPassiveState)
        {
            var args = new List<Term>
            {
                boogieContextSource.absValTyMap,
                boogieContextSource.methodContext,
                boogieContextSource.varContext,
                passificationWitness.VarContext,
                boogieContextSource.funContext,
                boogieContextSource.rtypeEnv,
                new NatConst(smallestFreeVar),
                passificationWitness.StateRelation,
                passificationWitness.OldStateRelation,
                passificationWitness.PassiveStates,
                passificationWitness.ConstrainedVariables,
                initNonPassiveState
            };
            // IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables, passificationWitness.ModifiedVars),

            return new TermApp(IsaCommonTerms.TermIdentFromName("passive_lemma_assms_2"), args);
        }

        private static Term BlockLemmaConclusion(
            BoogieContextIsa boogieContextSource,
            PassificationWitness passificationWitness,
            Term passiveCmds,
            Term finalState)
        {
            var args = new List<Term>
            {
                boogieContextSource.absValTyMap,
                boogieContextSource.methodContext,
                boogieContextSource.varContext,
                passificationWitness.VarContext,
                boogieContextSource.funContext,
                boogieContextSource.rtypeEnv,
                passificationWitness.PassiveStates,
                IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables,
                    IsaCommonTerms.SetOfList(passificationWitness.ModifiedVars)),
                new TermApp(IsaCommonTerms.TermIdentFromName("update_nstate_rel"),
                    passificationWitness.StateRelation,
                    passificationWitness.ModifiedVarsRelation),
                passificationWitness.OldStateRelation,
                passiveCmds,
                finalState
            };
            // IsaCommonTerms.SetUnion(passificationWitness.ConstrainedVariables, passificationWitness.ModifiedVars),

            return new TermApp(IsaCommonTerms.TermIdentFromName("passive_block_conclusion"), args);
        }

        public static Term CfgLemmaConclusion(
            BoogieContextIsa boogieContextSource,
            PassificationWitness passificationWitness,
            IProgramAccessor passiveProgramAccessor,
            Term blockNodeId,
            Term finalState)
        {
            var passiveNormalStateId = new SimpleIdentifier("u");
            var passiveNormalState = new TermIdent(passiveNormalStateId);

            var args = new List<Term>
            {
                boogieContextSource.absValTyMap,
                boogieContextSource.methodContext,
                passificationWitness.VarContext,
                boogieContextSource.funContext,
                boogieContextSource.rtypeEnv,
                passiveProgramAccessor.CfgDecl(),
                passiveNormalState,
                blockNodeId
            };

            Term sim = new TermApp(IsaCommonTerms.TermIdentFromName("passive_sim_cfg_fail"), args);

            var rhs = TermQuantifier.Exists(
                new List<Identifier> {passiveNormalStateId},
                null,
                TermBinary.And(
                    IsaCommonTerms.Elem(passiveNormalState, passificationWitness.PassiveStates),
                    sim
                )
            );

            return TermBinary.Implies(
                TermBinary.Eq(finalState, IsaBoogieTerm.Failure()),
                rhs);
        }

        private Proof CfgLemmaProof(Block b, string blockLemmaName, IList<string> successorNames, bool hasStateRelAssms)
        {
            /*
             (tactic ‹cfg_lemma @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} 
            (@{thm sync_before_passive_prog.node_1}, @{thm sync_before_passive_prog.outEdges_1})
            (@{thm sync_passive_prog.node_1}, @{thm sync_passive_prog.outEdges_1}) 
            @{thm block_anon4_Then}
            [@{thm cfg_block_anon3}] 1›)
            */

            var beforePassiveNodeThm = MLUtil.IsaToMLThm(programAccessor.BlockInfo().BlockCmdsMembershipLemma(b));
            var beforePassiveEdgeThm = MLUtil.IsaToMLThm(programAccessor.BlockInfo().OutEdgesMembershipLemma(b));
            var passiveNodeThm =
                MLUtil.IsaToMLThm(passiveProgramAccessor.BlockInfo().BlockCmdsMembershipLemma(origToPassiveBlock[b]));
            var passiveEdgeThm =
                MLUtil.IsaToMLThm(passiveProgramAccessor.BlockInfo().OutEdgesMembershipLemma(origToPassiveBlock[b]));

            var cfgLemmaTacArgs = new List<string>
            {
                MLUtil.ContextAntiquotation(),
                MLUtil.IsaToMLThm("assms(1)"),
                MLUtil.IsaToMLThm("assms(2)"),
                hasStateRelAssms ? MLUtil.IsaToMLThms("assms(3-)") : MLUtil.MLList(new List<string>()),
                MLUtil.MLTuple(beforePassiveNodeThm, beforePassiveEdgeThm),
                MLUtil.MLTuple(passiveNodeThm, passiveEdgeThm),
                MLUtil.IsaToMLThm(blockLemmaName),
                MLUtil.MLList(successorNames.Select(MLUtil.IsaToMLThm))
            };

            var argsString = string.Join(" ", cfgLemmaTacArgs);

            var proofMethods = new List<string>
            {
                ProofUtil.By(ProofUtil.MLTactic("cfg_lemma_tac " + argsString, 1))
            };

            return new Proof(proofMethods);
        }
    }
}