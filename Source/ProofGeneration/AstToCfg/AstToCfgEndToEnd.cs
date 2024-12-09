using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.ASTRepresentation;
using ProofGeneration.PhasesUtil;
using ProofGeneration.Util;
using ProofGeneration.ASTRepresentation;

namespace ProofGeneration.AstToCfg
{
    public class AstToCfgEndToEnd
    {
        private readonly string axiomAssmName = "Axioms";
        private readonly string binderEmptyAssmName = "BinderNs";
        private readonly string closedAssmName = "Closed";
        private readonly string constsGlobalsAssmName = "ConstsGlobal";
        //private readonly TermIdent finalNodeOrReturn = IsaCommonTerms.TermIdentFromName("m'");
        //private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly string finterpAssmName = "FInterp";
        private readonly string nonEmptyTypesAssmName = "NonEmptyTypes";

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("ns");
        private readonly string oldGlobalAssmName = "OldGlobal";
        private readonly string paramsLocalsAssmName = "ParamsLocal";
        private readonly string preconditionsAssmName = "Precondition";

        private readonly string redAssmName = "Red";
        private readonly string vcAssmName = "VC";
        private BoogieContextIsa boogieContext;
        
        private IProgramAccessor beforeCfgProgramAccessor;

        private readonly string varContextName = "\\<Lambda>0";

        //private readonly LemmaDecl entryLemma;

        public IEnumerable<OuterDecl> EndToEndProof(
            string entryBlockAstLemma,
            EndToEndLemmaConfig endToEndLemmaConfig,
            string cfgToDagEndToEndLemma,
            Term vcAssm,
            IProgramAccessor beforeCfgProgramAccessor,
            IProgramAccessor afterCfgProgramAccessor,
            ASTRepr ast,
            AstToCfgProofGenInfo proofGenInfo)
        {
            if (endToEndLemmaConfig == EndToEndLemmaConfig.DoNotGenerate)
            {
              throw new ArgumentException("end-to-end lemma invoked even though disabled");
            }
            
            this.beforeCfgProgramAccessor = beforeCfgProgramAccessor;
            
            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("(M::mbodyCFG proc_context)"),
                IsaCommonTerms.TermIdentFromName(varContextName),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.EmptyList
            );

            var abbrev = new AbbreviationDecl(
                varContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(),
                    new TermTuple(beforeCfgProgramAccessor.ConstsAndGlobalsDecl(), beforeCfgProgramAccessor.ParamsAndLocalsDecl()))
            );
            var result = new List<OuterDecl> {abbrev};
            
            BigBlock bigblock0 = ast.GetBlocksForwards().First();
            string cont0 = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[bigblock0];
            Term cont0Id = IsaCommonTerms.TermIdentFromName(cont0);
            Term stateName = IsaCommonTerms.TermIdentFromName("ns");
            Term initState1 = IsaBoogieTerm.Normal(stateName);

            var kStepBigBlockRed = IsaBoogieTerm.RedBigBlockKStep(
                BoogieContextIsa.CreateWithNewVarContext(
                    boogieContext,
                    new TermTuple(beforeCfgProgramAccessor.ConstsAndGlobalsDecl(), beforeCfgProgramAccessor.ParamsAndLocalsDecl())
                ),
                IsaBoogieTerm.StartConfigTerm(bigblock0, cont0Id, beforeCfgProgramAccessor, initState1),
                IsaBoogieTerm.EndConfigTerm(),
                IsaBoogieTerm.astId(),
                IsaCommonTerms.TermIdentFromName("j")
            );

            var proofSb = new StringBuilder();
            proofSb.AppendLine("proof -");
            proofSb.AppendLine("from " + redAssmName + " obtain j where Aux:" + "\"" + kStepBigBlockRed + "\"");
            proofSb.AppendLine("by (meson rtranclp_imp_relpowp)");
            proofSb.AppendLine("show ?thesis");
            proofSb.AppendLine(ProofUtil.Apply("rule ast_to_cfg_lemmas." + entryBlockAstLemma));
            proofSb.AppendLine("unfolding ast_to_cfg_lemmas_def");
            proofSb.AppendLine("apply (rule FInterp)");
            proofSb.AppendLine("apply (rule Aux)");
            proofSb.AppendLine("apply (rule valid_config_implies_not_failure)");
            proofSb.AppendLine(ProofUtil.Apply("rule " + cfgToDagEndToEndLemma));
            proofSb.AppendLine("apply (simp add: " +
                               beforeCfgProgramAccessor.ParamsDecl() + "_def " + beforeCfgProgramAccessor.LocalsDecl() + "_def " +
                               afterCfgProgramAccessor.ParamsDecl() + "_def " + afterCfgProgramAccessor.LocalsDecl() + "_def)");
            proofSb.AppendLine("using " + vcAssmName + " apply simp");
            proofSb.AppendLine("using " + closedAssmName + " apply simp");
            proofSb.AppendLine("using " + nonEmptyTypesAssmName + " apply simp");
            proofSb.AppendLine(ProofUtil.Apply("rule " + finterpAssmName));
            proofSb.AppendLine("using " + axiomAssmName + " apply simp");
            
            proofSb.AppendLine("using " + preconditionsAssmName + " apply (simp add: " + 
                                                                    beforeCfgProgramAccessor.ParamsDecl() + "_def " + beforeCfgProgramAccessor.LocalsDecl() + "_def " +
                                                                    afterCfgProgramAccessor.ParamsDecl() + "_def " + afterCfgProgramAccessor.LocalsDecl() + "_def " + 
                                                                    beforeCfgProgramAccessor.PreconditionsDecl() + "_def " + afterCfgProgramAccessor.PreconditionsDecl() + "_def)");
            proofSb.AppendLine("using " + paramsLocalsAssmName + " apply (simp add: " + 
                                                                   beforeCfgProgramAccessor.ParamsDecl() + "_def " + beforeCfgProgramAccessor.LocalsDecl() + "_def " +
                                                                   afterCfgProgramAccessor.ParamsDecl() + "_def " + afterCfgProgramAccessor.LocalsDecl() + "_def)");
            proofSb.AppendLine("using " + constsGlobalsAssmName + " apply (simp add: " +
                                                                    beforeCfgProgramAccessor.ParamsDecl() + "_def " + beforeCfgProgramAccessor.LocalsDecl() + "_def " +
                                                                    afterCfgProgramAccessor.ParamsDecl() + "_def " + afterCfgProgramAccessor.LocalsDecl() + "_def)");
            
            proofSb.AppendLine("using " + oldGlobalAssmName + " apply simp");
            proofSb.AppendLine("using " + binderEmptyAssmName + " apply simp");

            proofSb.AppendLine("apply (rule valid_config_implies_satisfied_posts)");
            proofSb.AppendLine(ProofUtil.Apply("rule " + cfgToDagEndToEndLemma));
            proofSb.AppendLine("apply (simp add: " +
                               beforeCfgProgramAccessor.ParamsDecl() + "_def " + beforeCfgProgramAccessor.LocalsDecl() + "_def " +
                               afterCfgProgramAccessor.ParamsDecl() + "_def " + afterCfgProgramAccessor.LocalsDecl() + "_def)");
            //TODO: don't hardcode this
            proofSb.AppendLine("using " + vcAssmName + " apply simp");
            proofSb.AppendLine("using " + closedAssmName + " apply simp");
            proofSb.AppendLine("using " + nonEmptyTypesAssmName + " apply simp");
            proofSb.AppendLine(ProofUtil.Apply("rule " + finterpAssmName));
            proofSb.AppendLine("using " + axiomAssmName + " apply simp");
            
            proofSb.AppendLine("using " + preconditionsAssmName + " apply (simp add: " + 
                               beforeCfgProgramAccessor.ParamsDecl() + "_def " + beforeCfgProgramAccessor.LocalsDecl() + "_def " +
                               afterCfgProgramAccessor.ParamsDecl() + "_def " + afterCfgProgramAccessor.LocalsDecl() + "_def " + 
                               beforeCfgProgramAccessor.PreconditionsDecl() + "_def " + afterCfgProgramAccessor.PreconditionsDecl() + "_def)");
            proofSb.AppendLine("using " + paramsLocalsAssmName + " apply (simp add: " + 
                               beforeCfgProgramAccessor.ParamsDecl() + "_def " + beforeCfgProgramAccessor.LocalsDecl() + "_def " +
                               afterCfgProgramAccessor.ParamsDecl() + "_def " + afterCfgProgramAccessor.LocalsDecl() + "_def)");
            proofSb.AppendLine("using " + constsGlobalsAssmName + " apply (simp add: " +
                               beforeCfgProgramAccessor.ParamsDecl() + "_def " + beforeCfgProgramAccessor.LocalsDecl() + "_def " +
                               afterCfgProgramAccessor.ParamsDecl() + "_def " + afterCfgProgramAccessor.LocalsDecl() + "_def)");
            
            proofSb.AppendLine("using " + oldGlobalAssmName + " apply simp");
            proofSb.AppendLine("using " + binderEmptyAssmName + " apply simp+");
            
            proofSb.AppendLine("done");
            proofSb.AppendLine("qed");

            var helperLemmaName = "end_to_end_theorem_aux_ast";
            
            var helperLemma =
                new LemmaDecl(
                    helperLemmaName,
                    LemmaContext(ast, vcAssm, proofGenInfo),
                    IsaBoogieTerm.AstValidConfiguration(boogieContext, beforeCfgProgramAccessor.PostconditionsDecl()),
                    new Proof(new List<string> {proofSb.ToString()})
                );
            result.Add(helperLemma);

            if (endToEndLemmaConfig == EndToEndLemmaConfig.GenerateForProcedure)
            {
              var assumptions = new List<Term>();

              string contName = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[bigblock0];
              Term contId = IsaCommonTerms.TermIdentFromName(contName);
              Term initStateId = IsaBoogieTerm.Normal(IsaCommonTerms.TermIdentFromName("ns"));

              Term astDecl = ast.GetAstAsTermList(proofGenInfo);
              List<string> continuations = ast.GetMainContinuations(proofGenInfo);
              string continuationsAsString = null;
              foreach (var str in continuations)
              {
                continuationsAsString += str + " ";
              }

              var initAstTerm = new TermApp
              (
                IsaCommonTerms.TermIdentFromName("init_ast"),
                astDecl,
                IsaCommonTerms.TermIdentFromName("ns")
              );

              BoogieContextIsa dummyBoogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName("\\<Lambda>"),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.TermIdentFromName("\\<Omega>")
              );

              var bigBlockMultiRedInitAst = IsaBoogieTerm.RedBigBlockMulti(
                dummyBoogieContext,
                initAstTerm,
                IsaBoogieTerm.EndConfigTerm(),
                IsaBoogieTerm.astId()
              );

              assumptions.Add(bigBlockMultiRedInitAst);

              var bigBlockMultiRed = IsaBoogieTerm.RedBigBlockMulti(
                dummyBoogieContext,
                IsaBoogieTerm.StartConfigTerm(bigblock0, contId, beforeCfgProgramAccessor, initStateId),
                IsaBoogieTerm.EndConfigTerm(),
                IsaBoogieTerm.astId()
              );

              var proofMethods = new List<string>
              {
                "using assms",
                "by (simp add: " + continuationsAsString + ")"
              };

              var initializationLemmaName = "initialization";
              var initializationLemma =
                new LemmaDecl(
                  initializationLemmaName,
                  ContextElem.CreateWithAssumptions(assumptions),
                  bigBlockMultiRed,
                  new Proof(proofMethods)
                );
              result.Add(initializationLemma);

              //transform end to end theorem to a compact representation
              var endToEndLemma =
                new LemmaDecl(
                  "end_to_end_theorem_ast",
                  ContextElem.CreateWithAssumptions(new List<Term> { vcAssm }, new List<string> { "VC" }),
                  ProcedureIsCorrect(
                    beforeCfgProgramAccessor.FunctionsDecl(),
                    IsaCommonTerms.TermIdentFromName(beforeCfgProgramAccessor.ConstsDecl()),
                    IsaCommonTerms.TermIdentFromName(beforeCfgProgramAccessor.UniqueConstsDecl()),
                    IsaCommonTerms.TermIdentFromName(beforeCfgProgramAccessor.GlobalsDecl()),
                    beforeCfgProgramAccessor.AxiomsDecl(),
                    beforeCfgProgramAccessor.ProcDecl()),
                  new Proof(
                    new List<string>
                    {
                      ProofUtil.Apply(ProofUtil.Rule(ProofUtil.OF("end_to_end_util2", helperLemmaName))),
                      "apply (rule initialization)",
                      "unfolding " + beforeCfgProgramAccessor.ProcDeclName() + "_def",
                      "apply assumption " + "using VC apply simp " + " apply assumption+",
                      ProofUtil.By("simp_all add: exprs_to_only_checked_spec_1 exprs_to_only_checked_spec_2 " +
                                   beforeCfgProgramAccessor.ProcDeclName() + "_def " +
                                   beforeCfgProgramAccessor.CfgDeclName() + "_def")
                    }
                  ));

              result.Add(endToEndLemma);
            }

            return result;
        }

        private ContextElem LemmaContext(
            ASTRepr ast,
            Term vcAssm,
            AstToCfgProofGenInfo proofGenInfo
        )
        {
            BigBlock bigblock0 = ast.GetBlocksForwards().First();
            string contName = "cont_" + proofGenInfo.GetMappingCopyBigBlockToIndex()[bigblock0];
            Term contId = IsaCommonTerms.TermIdentFromName(contName);
            Term initStateId = IsaBoogieTerm.Normal(IsaCommonTerms.TermIdentFromName("ns"));
          
            var bigBlockMultiRed = IsaBoogieTerm.RedBigBlockMulti(
                BoogieContextIsa.CreateWithNewVarContext(
                    boogieContext,
                    new TermTuple(beforeCfgProgramAccessor.ConstsAndGlobalsDecl(), beforeCfgProgramAccessor.ParamsAndLocalsDecl())
                ),
                IsaBoogieTerm.StartConfigTerm(bigblock0, contId, beforeCfgProgramAccessor, initStateId),
                IsaBoogieTerm.EndConfigTerm(),
                IsaBoogieTerm.astId()
            );
            var closedAssm = EndToEndAssumptions.ClosednessAssumption(boogieContext.absValTyMap);
            var nonEmptyTypesAssm = EndToEndAssumptions.NonEmptyTypesAssumption(boogieContext.absValTyMap);
            var finterpAssm = IsaBoogieTerm.FunInterpWf(boogieContext.absValTyMap, beforeCfgProgramAccessor.FunctionsDecl(),
                boogieContext.funContext);
            var absValType = new VarType("a");
            //need to explicitly give type for normal state, otherwise Isabelle won't know that the abstract value type is the same as used in the VC
            var axiomAssm = EndToEndAssumptions.AxiomAssumption(boogieContext, beforeCfgProgramAccessor,
                new TermWithExplicitType(normalInitState, IsaBoogieType.NormalStateType(absValType)));
            var presAssm =
                IsaBoogieTerm.ExprAllSat(boogieContext, normalInitState, beforeCfgProgramAccessor.PreconditionsDecl());
            var localsAssm = EndToEndAssumptions.LocalStateAssumption(boogieContext,
                IsaCommonTerms.Snd(boogieContext.varContext), normalInitState);
            var globalsAssm = EndToEndAssumptions.GlobalStateAssumption(boogieContext,
                IsaCommonTerms.Fst(boogieContext.varContext), normalInitState);
            var oldGlobalStateAssm = EndToEndAssumptions.OldGlobalStateAssumption(normalInitState);
            var binderEmptyAssm = EndToEndAssumptions.BinderStateEmpty(normalInitState);

            return
                ContextElem.CreateWithAssumptions(
                    new List<Term>
                    {
                        bigBlockMultiRed, vcAssm, closedAssm, nonEmptyTypesAssm, finterpAssm, axiomAssm,
                        presAssm, localsAssm, globalsAssm, oldGlobalStateAssm, binderEmptyAssm
                    },
                    new List<string>
                    {
                        redAssmName, vcAssmName, closedAssmName, nonEmptyTypesAssmName, finterpAssmName, axiomAssmName,
                        preconditionsAssmName, paramsLocalsAssmName, constsGlobalsAssmName, oldGlobalAssmName,
                        binderEmptyAssmName
                    }
                );
        }

        private static Term ProcedureIsCorrect(Term funDecls, Term constantDecls, Term uniqueConstantDecls, Term globalDecls, Term axioms,
            Term procedure)
        {
            var typeInterpId = new SimpleIdentifier("A");
            return 
                TermQuantifier.MetaAll(
                    new List<Identifier>{typeInterpId},
                    null,
                    new TermApp(
                      IsaCommonTerms.TermIdentFromName("proc_is_correct"),
                      new TermWithExplicitType(new TermIdent(typeInterpId), IsaBoogieType.AbstractValueTyFunType(new VarType("a"))),
                      funDecls,
                      constantDecls,
                      uniqueConstantDecls,
                      globalDecls,
                      axioms,
                      procedure,
                      new TermWithExplicitType(
                        IsaCommonTerms.TermIdentFromName("Ast.proc_body_satisfies_spec"), 
                        new DataType("satisfies_spec_func_type", new VarType("a"))
                      )
                    )
                );
        }
    }
}