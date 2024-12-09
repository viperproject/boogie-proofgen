namespace ProofGeneration.CFGOptimizations;
using System;
using System.Collections.Generic;
using System.Text;
using Isabelle.Ast;
using Isabelle.Util;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.PhasesUtil;
using ProofGeneration.Util;

public class CFGOptimizationsEndToEnd
{
  private readonly string axiomAssmName = "Axioms";
  private readonly string binderEmptyAssmName = "BinderNs";
  private readonly string closedAssmName = "Closed";
  private readonly string constsGlobalsAssmName = "ConstsGlobal";
  private readonly TermIdent finalNodeOrReturn = IsaCommonTerms.TermIdentFromName("m'");
  private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
  private readonly string finterpAssmName = "FInterp";
  private readonly string nonEmptyTypesAssmName = "NonEmptyTypes";

  private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("ns");
  private readonly string oldGlobalAssmName = "OldGlobal";
  private readonly string paramsLocalsAssmName = "ParamsLocal";
  private readonly string preconditionsAssmName = "Precondition";

  private readonly string redAssmName = "Red";
  private readonly string vcAssmName = "VC";
  private BoogieContextIsa boogieContext;
  
  private IProgramAccessor programAccessor;
  

  private readonly string varContextName = "\\<Lambda>0";


  public IEnumerable<OuterDecl> EndToEndProof(
    string entryBlockCfgOptLemma,
    EndToEndLemmaConfig endToEndLemmaConfig,
    Term vcAssm,
    IProgramAccessor beforeOptProgAccess,
    IProgramAccessor afterOptProgAccess,
    IProgramAccessor programAccessor,
    CFGRepr afterOptCFG,
    PhasesTheories phasesTheories,
    string procedureName)
  {
    if (endToEndLemmaConfig == EndToEndLemmaConfig.DoNotGenerate)
    {
      throw new ArgumentException("CFG Optimizations Phase: end-to-end lemma invoked even though disabled");
    }
    
    this.programAccessor = programAccessor;
    boogieContext = new BoogieContextIsa(
      IsaCommonTerms.TermIdentFromName("A"),
      IsaCommonTerms.TermIdentFromName("M"),
      IsaCommonTerms.TermIdentFromName(varContextName),
      IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
      IsaCommonTerms.EmptyList
    );
    
    var abbrev = new AbbreviationDecl(
      varContextName,
      new Tuple<IList<Term>, Term>(new List<Term>(),
        new TermTuple(afterOptProgAccess.ConstsAndGlobalsDecl(), afterOptProgAccess.ParamsAndLocalsDecl()))
    );
    
    var result = new List<OuterDecl> {abbrev};
    
    var kStepRed = IsaBoogieTerm.RedCFGKStep(
      BoogieContextIsa.CreateWithNewVarContext(
        boogieContext,
        new TermTuple(afterOptProgAccess.ConstsAndGlobalsDecl(), afterOptProgAccess.ParamsAndLocalsDecl())
      ),
      beforeOptProgAccess.CfgDecl(),
      IsaBoogieTerm.CFGConfigNode(new NatConst(afterOptCFG.GetUniqueIntLabel(afterOptCFG.entry)),
        IsaBoogieTerm.Normal(normalInitState)),
      IsaCommonTerms.TermIdentFromName("j"),
      IsaBoogieTerm.CFGConfig(finalNodeOrReturn, finalState)
    );
    
    var proofSb = new StringBuilder();
    proofSb.AppendLine("proof -");
    proofSb.AppendLine("from " + redAssmName + " obtain j where Aux:" + "\"" + kStepRed + "\"");
    proofSb.AppendLine("by (meson rtranclp_imp_relpowp)");
    proofSb.AppendLine("show ?thesis");
    proofSb.AppendLine(ProofUtil.Apply("rule " + entryBlockCfgOptLemma));
    proofSb.AppendLine("apply (rule Aux)");
    proofSb.AppendLine("apply (rule allI | rule impI)+");
    proofSb.AppendLine("apply (rule " + phasesTheories.TheoryName(PhasesTheories.Phase.CfgToDag) + ".end_to_end_theorem_aux)");
    proofSb.AppendLine("using assms");
    proofSb.AppendLine("by auto");
    proofSb.AppendLine("qed");
    
    var helperLemmaName = "end_to_end_theorem_aux";
    
    var helperLemma =
      new LemmaDecl(
        helperLemmaName,
        LemmaContext(afterOptCFG, vcAssm, afterOptProgAccess),
        CfgOptLemmaConclusion(boogieContext, afterOptProgAccess.PostconditionsDecl(),
          finalNodeOrReturn, finalState),
        new Proof(new List<string> {proofSb.ToString()})
      );
    result.Add(helperLemma);

    if (endToEndLemmaConfig == EndToEndLemmaConfig.GenerateForProcedure)
    { 
        var endToEndLemma = 
                    new LemmaDecl(
                        "end_to_end_theorem",
                        ContextElem.CreateWithAssumptions(new List<Term> {vcAssm}, new List<string> {"VC"}),
                        IsaBoogieTerm.ProcedureIsCorrectCfg(
                            programAccessor.FunctionsDecl(), 
                            IsaCommonTerms.TermIdentFromName(programAccessor.ConstsDecl()),
                            IsaCommonTerms.TermIdentFromName(programAccessor.UniqueConstsDecl()),
                            IsaCommonTerms.TermIdentFromName(programAccessor.GlobalsDecl()),
                            programAccessor.AxiomsDecl(),
                            IsaCommonTerms.TermIdentFromName(programAccessor.ProcDeclName())),
                        new Proof(
                            new List<string>
                            {
                                ProofUtil.Apply(ProofUtil.Rule(ProofUtil.OF("end_to_end_util",helperLemmaName))),
                                ProofUtil.Apply("assumption"),
                                "using VC apply simp",
                                ProofUtil.Apply("assumption+"),
                                ProofUtil.Apply($"unfold {programAccessor.ProcDeclName()}_def"),
                                ProofUtil.Apply(ProofUtil.Simp(beforeOptProgAccess.PreconditionsDeclName()+"_def", 
                                                                 beforeOptProgAccess.ProcDeclName()+"_def",
                                                                 "exprs_to_only_checked_spec_1")),
                                ProofUtil.Apply(ProofUtil.Simp(beforeOptProgAccess.PostconditionsDeclName()+"_def  ", 
                                                                 beforeOptProgAccess.ProcDeclName()+"_def",
                                                                 "exprs_to_only_checked_spec_2")),
                                ProofUtil.Apply(ProofUtil.Simp()),
                                ProofUtil.Apply(ProofUtil.Simp(beforeOptProgAccess.ProcDeclName() + "_def")),
                                ProofUtil.Apply(ProofUtil.Simp(beforeOptProgAccess.ProcDeclName() + "_def")),
                                ProofUtil.Apply(ProofUtil.Simp(beforeOptProgAccess.ProcDeclName() + "_def")),
                                ProofUtil.Apply(ProofUtil.Simp(beforeOptProgAccess.CfgDeclName() + "_def")),
                                "done"
                            }
                        ) );
        
        result.Add(endToEndLemma);
    }

    return result;
  }
  
  
  private ContextElem LemmaContext(
            CFGRepr cfg,
            Term vcAssm,
            IProgramAccessor afterOptProgAccess
        )
        {   
            var multiRed = IsaBoogieTerm.RedCFGMulti(
                BoogieContextIsa.CreateWithNewVarContext(
                    boogieContext,
                    new TermTuple(afterOptProgAccess.ConstsAndGlobalsDecl(), afterOptProgAccess.ParamsAndLocalsDecl())
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
            var absValType = new VarType("a");
            //need to explicitly give type for normal state, otherwise Isabelle won't know that the abstract value type is the same as used in the VC
            var axiomAssm = EndToEndAssumptions.AxiomAssumption(boogieContext, programAccessor,
                new TermWithExplicitType(normalInitState, IsaBoogieType.NormalStateType(absValType)));
            var presAssm =
                IsaBoogieTerm.ExprAllSat(boogieContext, normalInitState, afterOptProgAccess.PreconditionsDecl());
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
                        multiRed, vcAssm, closedAssm, nonEmptyTypesAssm, finterpAssm, axiomAssm,
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
  
  public static Term CfgOptLemmaConclusion(BoogieContextIsa boogieContext, Term post, Term finalNode,
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
  
}