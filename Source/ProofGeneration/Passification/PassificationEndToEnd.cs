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

namespace ProofGeneration.Passification
{
    public class PassificationEndToEnd
    {
        private readonly string axiomAssmName = "Axioms";
        private readonly string binderEmptyAssmName = "BinderNs";
        private readonly string closedAssmName = "Closed";
        private readonly string constsGlobalsAssmName = "ConstsGlobal";
        private readonly string finterpAssmName = "FInterp";
        private readonly string nonEmptyTypesAssmName = "NonEmptyTypes";
        private readonly string oldGlobalEqualAssmName = "OldGlobal";
        private readonly string paramsLocalsAssmName = "ParamsLocal";

        private readonly string redAssmName = "Red";
        private readonly Term stateRel;
        private readonly string stateRelDefName = "R_rel";
        private readonly Term stateRelList;

        private readonly string stateRelListDefName = "R_list";
        private readonly string vcAssmName = "VC";
        private BoogieContextIsa boogieContext;
        private string boogieToVcLemma;
        private CFGRepr cfg;
        private string entryCfgLemma;

        private readonly TermIdent finalNodeOrReturn = IsaCommonTerms.TermIdentFromName("m'");
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");

        private IEnumerable<Variable> liveEntryVars;
        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("ns");
        private StateRelationData oldRelationData;
        private IProgramAccessor passiveProgramAccessor;

        private TermIdent passiveVarContext;
        private IProgramAccessor programAccessor;
        private IVariableTranslation<Variable> varTranslation;
        private Term vcAssm;
        
        public PassificationEndToEnd()
        {
            stateRelList = IsaCommonTerms.TermIdentFromName(stateRelListDefName);
            stateRel = IsaCommonTerms.TermIdentFromName(stateRelDefName);
        }

        public IEnumerable<OuterDecl> EndToEndProof(
            string entryCfgLemma,
            string boogieToVcLemma,
            Term vcAssm,
            IProgramAccessor programAccessor,
            IProgramAccessor passiveProgramAccessor,
            Tuple<string, string> varContextNonPassivePassive,
            StateRelationData oldRelationData,
            CFGRepr cfg,
            IEnumerable<Variable> liveEntryVars,
            IVariableTranslation<Variable> varTranslation)
        {
            this.entryCfgLemma = entryCfgLemma;
            this.boogieToVcLemma = boogieToVcLemma;
            this.vcAssm = vcAssm;
            this.programAccessor = programAccessor;
            this.passiveProgramAccessor = passiveProgramAccessor;
            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName(varContextNonPassivePassive.Item1),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.EmptyList
            );
            passiveVarContext = IsaCommonTerms.TermIdentFromName(varContextNonPassivePassive.Item2);
            this.oldRelationData = oldRelationData;
            this.cfg = cfg;
            this.liveEntryVars = liveEntryVars;
            this.varTranslation = varTranslation;

            var locale = new LocaleDecl("glue_proof",
                Context(),
                GenerateLemma()
            );

            return new List<OuterDecl>
            {
                locale
            };
        }

        private List<OuterDecl> GenerateLemma()
        {
            var varIds = new List<Tuple<int, Variable>>();
            foreach (var v in liveEntryVars)
                if (varTranslation.TryTranslateVariableId(v, out var termId, out _))
                    varIds.Add(Tuple.Create((termId as NatConst).Val, v));
                else
                    throw new ProofGenUnexpectedStateException("cannot extract variable id");

            varIds.Sort((x, y) => x.Item1.CompareTo(y.Item1));

            Term stateRelationList = new TermList(varIds
                .Select(t => (Term) new TermTuple(new NatConst(t.Item1), IsaCommonTerms.Inl(new NatConst(t.Item1))))
                .ToList());

            var stateRelListDef = new DefDecl(stateRelListDefName, PassificationManager.StateRelListReprType,
                Tuple.Create((IList<Term>) new List<Term>(), stateRelationList));

            var stateRelDef = DefDecl.CreateWithoutArg(stateRelDefName,
                new TermApp(IsaCommonTerms.TermIdentFromName("map_of"), stateRelList));

            var result = new List<OuterDecl> {stateRelListDef, stateRelDef};

            var injectiveLemma = new LemmaDecl(
                "inj_R_rel",
                new TermApp(IsaCommonTerms.TermIdentFromName("inj_on_defined"), stateRel),
                new Proof(new List<string>
                    {
                        ProofUtil.Apply(
                            ProofUtil.Rule(ProofUtil.OF("injective_fun_to_list_2", stateRelDefName + "_def"))),
                        ProofUtil.By(ProofUtil.SimpAddDel(new List<string> {"distinct.simps"},
                            stateRelListDefName + "_def"))
                    }
                ));
            result.Add(injectiveLemma);

            Identifier xId = new SimpleIdentifier("x");
            var x = new TermIdent(xId);
            Identifier tau = new SimpleIdentifier("\\<tau>");
            var tauTerm = new TermIdent(tau);
            /*
             * lemma R_well_formed: "R_rel x = Some z ⟶ (∃τ. z = Inl x ∧ lookup_var_ty Λ1 x = Some τ ∧ lookup_var_ty Λ2 x = Some τ)"
             */

            #region relation well-formed

            Term z = IsaCommonTerms.TermIdentFromName("z");
            Term lhs = TermBinary.Eq(new TermApp(stateRel, x), IsaCommonTerms.SomeOption(z));

            Term rhs = TermQuantifier.Exists(
                new List<Identifier> {tau},
                null,
                TermBinary.And(
                    TermBinary.Eq(z, IsaCommonTerms.Inl(x)),
                    TermBinary.And(
                        TermBinary.Eq(IsaBoogieTerm.LookupVarTy(boogieContext.varContext, x),
                            IsaCommonTerms.SomeOption(tauTerm)),
                        TermBinary.Eq(IsaBoogieTerm.LookupVarTy(passiveVarContext, x),
                            IsaCommonTerms.SomeOption(tauTerm))
                    )
                )
            );

            var relWfProofMethods = new List<string>
            {
                ProofUtil.Apply(ProofUtil.Rule(ProofUtil.OF("convert_fun_to_list", stateRelDefName + "_def"))),
                ProofUtil.Apply(ProofUtil.Simp(stateRelListDefName + "_def")),
                ProofUtil.Apply("(intro conjI)?")
            };

            foreach (var idVar in varIds)
                relWfProofMethods.Add(
                    ProofUtil.Apply(ProofUtil.Simp(programAccessor.LookupVarTyLemma(idVar.Item2),
                        passiveProgramAccessor.LookupVarTyLemma(idVar.Item2)))
                );

            relWfProofMethods.Add("done");

            var relWellFormed = new LemmaDecl("R_well_formed",
                TermBinary.Implies(lhs, rhs),
                new Proof(
                    relWfProofMethods
                ));
            result.Add(relWellFormed);

            #endregion

            /*
             * lemma R_wt:"rel_well_typed A Λ1 Ω R_rel ns"
             */

            #region relation well typed

            var relWellTypedLemma = new LemmaDecl(
                "R_wt",
                new TermApp(IsaCommonTerms.TermIdentFromName("rel_well_typed"),
                    boogieContext.absValTyMap,
                    boogieContext.varContext,
                    boogieContext.rtypeEnv,
                    stateRel,
                    normalInitState
                ),
                new Proof(new List<string>
                {
                    ProofUtil.Apply(ProofUtil.Rule(ProofUtil.OF("rel_well_typed_state_typ_wf", paramsLocalsAssmName,
                        constsGlobalsAssmName))),
                    "using " + relWellFormed.Name + " by auto"
                })
            );

            result.Add(relWellTypedLemma);

            #endregion

            #region initial set U0

            var u0SetDecl = new AbbreviationDecl(
                "U0",
                new Tuple<IList<Term>, Term>(
                    new List<Term>(),
                    new TermApp(IsaCommonTerms.TermIdentFromName("initial_set"),
                        boogieContext.absValTyMap,
                        stateRel,
                        boogieContext.varContext,
                        passiveVarContext,
                        boogieContext.rtypeEnv,
                        normalInitState))
            );
            result.Add(u0SetDecl);

            Term u0Set = IsaCommonTerms.TermIdentFromName(u0SetDecl.Name);

            var nstateRelU0 = new LemmaDecl(
                "U0_ns_rel",
                new TermApp(IsaCommonTerms.TermIdentFromName("nstate_rel_states"),
                    boogieContext.varContext,
                    passiveVarContext,
                    stateRel,
                    normalInitState,
                    u0Set),
                new Proof(
                    new List<string>
                    {
                        "unfolding nstate_rel_states_def nstate_rel_def",
                        ProofUtil.By(ProofUtil.Simp(binderEmptyAssmName))
                    }
                )
            );
            result.Add(nstateRelU0);

            var proofMethods = new List<string>
            {
                ProofUtil.Apply("rule " + ProofUtil.OF("nstate_old_rel_states_helper", constsGlobalsAssmName,
                    oldGlobalEqualAssmName)),
                ProofUtil.Apply("simp only: fst_conv snd_conv " + programAccessor.GlobalsLocalsDisjointLemma())
            };

            void ConvertRelPropertyToListElems()
            {
                proofMethods.Add(ProofUtil.Apply("rule " +
                                                 ProofUtil.OF("convert_fun_to_list",
                                                     oldRelationData.StateRel + "_def")));
                proofMethods.Add("unfolding " + oldRelationData.StateRelList + "_def ");
                if (oldRelationData.VarsMapped.Any())
                    proofMethods.Add("apply (simp only: list.pred_inject)");
            }

            //prove old relation only has constants/globals in its domain
            ConvertRelPropertyToListElems();
            if (oldRelationData.VarsMapped.Any())
                proofMethods.Add("apply (intro conjI)");
            foreach (var v in oldRelationData.VarsMapped)
                proofMethods.Add("using " + programAccessor.MembershipLemma(v) + " apply simp");
            //trivial obligation 
            proofMethods.Add("apply simp");

            //prove old relation respects the "standard" state relation
            //TODO: here we are looking up values in the state relation for a second time, could make sense to prove it once separately and to then re-use this
            ConvertRelPropertyToListElems();
            if (oldRelationData.VarsMapped.Any())
                proofMethods.Add("unfolding " + stateRelDefName + "_def " + stateRelListDefName + "_def");
            proofMethods.Add("by simp");

            var nstateOldRelU0 = new LemmaDecl(
                "U0_ns_old_rel",
                new TermApp(IsaCommonTerms.TermIdentFromName("nstate_old_rel_states"),
                    boogieContext.varContext,
                    passiveVarContext,
                    oldRelationData.StateRel,
                    normalInitState,
                    u0Set),
                new Proof(
                    proofMethods
                )
            );
            result.Add(nstateOldRelU0);

            var variableClosedTypes = new LemmaDecl(
                "closed_ty_passive_vars",
                ContextElem.CreateWithAssumptions(TermBinary.Eq(IsaBoogieTerm.LookupVarTy(passiveVarContext, x),
                    IsaCommonTerms.SomeOption(tauTerm))),
                IsaBoogieTerm.IsClosedType(IsaBoogieTerm.InstantiateType(boogieContext.rtypeEnv, tauTerm)),
                new Proof(new List<string>
                {
                    "apply (rule lookup_ty_pred[OF assms(1)])",
                    "unfolding " + passiveProgramAccessor.ConstsDecl() + "_def " +
                    passiveProgramAccessor.GlobalsDecl() + "_def",
                    "apply simp",
                    "unfolding " + passiveProgramAccessor.ParamsDecl() + "_def " + passiveProgramAccessor.LocalsDecl() +
                    "_def",
                    "by simp"
                })
            );
            result.Add(variableClosedTypes);

            var u0NonEmpty = new LemmaDecl(
                "U0_non_empty",
                TermBinary.Neq(u0Set, IsaCommonTerms.EmptySet),
                new Proof(
                    new List<string>
                    {
                        "apply (rule init_set_non_empty)",
                        ProofUtil.Apply("erule " + nonEmptyTypesAssmName),
                        ProofUtil.Apply("erule " + variableClosedTypes.Name),
                        "using " + relWellFormed.Name + " apply fastforce",
                        ProofUtil.Apply(ProofUtil.Rule(relWellTypedLemma.Name)),
                        ProofUtil.Apply(ProofUtil.Rule(injectiveLemma.Name)),
                        "apply simp",
                        ProofUtil.Apply(ProofUtil.Rule(constsGlobalsAssmName)),
                        "using " + relWellFormed.Name + " apply fastforce",
                        "using " + programAccessor.GlobalsLocalsDisjointLemma() + " apply auto[1]",
                        "using " + passiveProgramAccessor.GlobalsLocalsDisjointLemma() + " apply auto[1]",
                        "done"
                    })
            );
            result.Add(u0NonEmpty);

            #endregion

            #region max relation

            var maxRelRangeLemma = new LemmaDecl(
                "max_rel_range",
                TermQuantifier.ForAll(
                    new List<Identifier> {xId},
                    null,
                    TermBinary.Implies(
                        IsaCommonTerms.Elem(x, new TermApp(IsaCommonTerms.TermIdentFromName("rel_range"), stateRel)),
                        TermBinary.Le(x, new NatConst(varIds.Any() ? varIds.Last().Item1 : 0)))
                ),
                new Proof(
                    new List<string>
                    {
                        " apply (rule rel_range_fun_to_list)",
                        ProofUtil.Apply(ProofUtil.Simp(stateRelDefName + "_def")),
                        ProofUtil.By(ProofUtil.Simp(stateRelListDefName + "_def"))
                    }
                )
            );

            result.Add(maxRelRangeLemma);

            #endregion

            #region final lemma

            var witness =
                new PassificationWitness(passiveVarContext, null, null, stateRel, null, u0Set, null);

            Term entryBlockId = new NatConst(programAccessor.BlockInfo().BlockIds[cfg.entry]);
            var cfgEntryConclusion = PassificationLemmaManager.CfgLemmaConclusion(boogieContext, witness,
                passiveProgramAccessor, IsaCommonTerms.Inl(entryBlockId), finalState);

            Term u = IsaCommonTerms.TermIdentFromName("u");
            Term mpPrime = IsaCommonTerms.TermIdentFromName("mp'");

            var passiveBoogieContext = new BoogieContextIsa(
                boogieContext.absValTyMap,
                boogieContext.methodContext,
                passiveVarContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv
            );

            var finalLemma = new LemmaDecl(
                PhasesTheories.LocalEndToEndName(),
                TermBinary.Neq(finalState, IsaBoogieTerm.Failure()),
                new Proof(
                    new List<string>
                    {
                        "proof",
                        "assume A1: " + Inner(TermBinary.Eq(finalState, IsaBoogieTerm.Failure())),
                        "have " + Inner(cfgEntryConclusion),
                        ProofUtil.Apply(ProofUtil.Rule(ProofUtil.OF(entryCfgLemma, redAssmName))),
                        "unfolding passive_lemma_assms_2_def",
                        "apply (intro conjI)?",
                        ProofUtil.Apply(ProofUtil.Rule(nstateRelU0.Name)),
                        ProofUtil.Apply(ProofUtil.Rule(nstateOldRelU0.Name)),
                        ProofUtil.Apply(ProofUtil.Rule(relWellTypedLemma.Name)),
                        ProofUtil.Apply(ProofUtil.Rule("init_state_dependent")),
                        "using " + ProofUtil.OF("helper_init_disj", maxRelRangeLemma.Name,
                            programAccessor.GlobalsAtMostMax()),
                        "apply simp",
                        ProofUtil.Apply(ProofUtil.Rule(u0NonEmpty.Name)),
                        ProofUtil.By(ProofUtil.SimpAll(stateRelDefName + "_def", stateRelListDefName + "_def")) + "?",
                        "with A1 obtain u mp' where uElem: " + Inner(IsaCommonTerms.Elem(u, u0Set)) + " and " +
                        "AredPassive:" +
                        Inner(IsaBoogieTerm.RedCFGMulti(
                            passiveBoogieContext,
                            passiveProgramAccessor.CfgDecl(),
                            IsaBoogieTerm.CFGConfigNode(entryBlockId, IsaBoogieTerm.Normal(u)),
                            IsaBoogieTerm.CFGConfig(mpPrime, IsaBoogieTerm.Failure())
                        )),
                        "by (auto simp add: passive_sim_cfg_fail_def)",
                        "from " + ProofUtil.OF(boogieToVcLemma, "AredPassive") + " have " +
                        Inner(TermBinary.Neq(IsaBoogieTerm.Failure(), IsaBoogieTerm.Failure())),
                        " apply rule",
                        "using " + vcAssmName + " apply assumption",
                        ProofUtil.Apply(ProofUtil.Rule(closedAssmName)),
                        ProofUtil.Apply(ProofUtil.Erule(nonEmptyTypesAssmName)),
                        ProofUtil.Apply(ProofUtil.Rule(finterpAssmName)),
                        ProofUtil.Apply(ProofUtil.Rule(ProofUtil.OF("axiom_assm_aux", axiomAssmName))),
                        "using uElem by simp_all",
                        "thus False by simp",
                        "qed"
                    }
                ));

            result.Add(finalLemma);

            #endregion

            return result;
        }

        private static string Inner(Term t)
        {
            return "\"" + t + "\"";
        }

        private ContextElem Context()
        {
            var multiRed = IsaBoogieTerm.RedCFGMulti(
                BoogieContextIsa.CreateWithNewVarContext(
                    boogieContext,
                    new TermTuple(programAccessor.ConstsAndGlobalsDecl(), programAccessor.ParamsAndLocalsDecl())
                ),
                programAccessor.CfgDecl(),
                IsaBoogieTerm.CFGConfigNode(new NatConst(cfg.GetUniqueIntLabel(cfg.entry)),
                    IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNodeOrReturn, finalState)
            );
            var closedAssm = EndToEndAssumptions.ClosednessAssumption(boogieContext.absValTyMap);
            var nonEmptyTypesAssm = EndToEndAssumptions.NonEmptyTypesAssumption(boogieContext.absValTyMap);
            var finterpAssm = IsaBoogieTerm.FunInterpWf(boogieContext.absValTyMap, programAccessor.FunctionsDecl(),
                boogieContext.funContext);
            //TODO constants
            //need to explicitly give type for normal state, otherwise Isabelle won't know that the abstract value type is the same as used in the VC
            var axiomAssm = EndToEndAssumptions.AxiomAssumption(boogieContext, programAccessor, normalInitState);
            var localsAssm = EndToEndAssumptions.LocalStateAssumption(boogieContext,
                IsaCommonTerms.Snd(boogieContext.varContext), normalInitState);
            var globalsAssm = EndToEndAssumptions.GlobalStateAssumption(boogieContext,
                IsaCommonTerms.Fst(boogieContext.varContext), normalInitState);
            var binderEmptyAssm = EndToEndAssumptions.BinderStateEmpty(normalInitState);
            var oldGlobalEqualAssm = EndToEndAssumptions.OldGlobalStateAssumption(normalInitState);

            return
                new ContextElem(GlobalFixedVariables(),
                    new List<Term>
                    {
                        multiRed, vcAssm, closedAssm, nonEmptyTypesAssm, finterpAssm, axiomAssm, localsAssm,
                        globalsAssm, binderEmptyAssm, oldGlobalEqualAssm
                    },
                    new List<string>
                    {
                        redAssmName, vcAssmName, closedAssmName, nonEmptyTypesAssmName, finterpAssmName, axiomAssmName,
                        paramsLocalsAssmName, constsGlobalsAssmName, binderEmptyAssmName, oldGlobalEqualAssmName
                    });
        }

        private IList<Tuple<TermIdent, TypeIsa>> GlobalFixedVariables()
        {
            var absValType = new VarType("a");

            var result = new List<Tuple<TermIdent, TypeIsa>>
            {
                Tuple.Create((TermIdent) boogieContext.absValTyMap, IsaBoogieType.AbstractValueTyFunType(absValType)),
                Tuple.Create((TermIdent) boogieContext.methodContext, IsaBoogieType.ProcContextType()),
                Tuple.Create((TermIdent) boogieContext.funContext, IsaBoogieType.FunInterpType(absValType)),
                Tuple.Create(finalNodeOrReturn, IsaBoogieType.CFGNodeOrReturnType()),
                Tuple.Create(normalInitState, IsaBoogieType.NormalStateType(absValType)),
                Tuple.Create(finalState, IsaBoogieType.StateType(absValType))
            };

            return result;
        }
    }
}