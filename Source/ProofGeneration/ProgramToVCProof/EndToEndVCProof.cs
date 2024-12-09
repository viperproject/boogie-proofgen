using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using Isabelle.Ast;
using Isabelle.IsaPrettyPrint;
using Isabelle.ML;
using Isabelle.Util;
using Microsoft.Boogie;
using Microsoft.Boogie.ProofGen;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.PhasesUtil;
using ProofGeneration.Util;
using ProofGeneration.VCProofGen;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration.ProgramToVCProof
{
    internal class EndToEndVCProof
    {
        private readonly CFGRepr afterPassificationCfg;
        private readonly string axiomAssmName = "Axioms";
        private readonly string axiomLocaleFact = "axiomLocaleFact";

        private readonly string axiomLocaleName;
        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor;

        private readonly BoogieContextIsa boogieContext;
        private readonly string closedAssmName = "Closed";
        private readonly string constsGlobalsAssmName = "ConstsGlobal";
        private readonly string ctorDeclListName = "ctor_list";
        private readonly string ctorName = "ctor";
        private readonly string entryBlockCorrectLemma;
        private readonly TypePremiseEraserFactory eraserFactory;
        private readonly CFGRepr finalCfg;
        private readonly TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");
        private readonly TermIdent finalState = IsaCommonTerms.TermIdentFromName("s'");
        private readonly string finterpAssmName = "FInterp";
        private readonly BoogieMethodData methodData;
        private readonly string nonEmptyTypesAssmName = "NonEmptyTypes";

        private readonly TermIdent normalInitState = IsaCommonTerms.TermIdentFromName("n_s");
        private readonly TermIdent normalRestrictedState = IsaCommonTerms.TermIdentFromName("?n_s_c");
        private readonly string normalRestrictedStateName = "?n_s_c";
        private readonly string paramsLocalsAssmName = "ParamsLocal";

        private readonly IProgramAccessor programAccessor;
        private readonly PureValueIsaTransformer pureValueIsaTransformer = new PureValueIsaTransformer();
        private readonly string qVarContext = "?\\<Lambda>";
        private readonly string qVarContextConst = "?\\<Lambda>c";
        private readonly string RedAssmName = "Red";
        private readonly IsaUniqueNamer stateCorresNamer = new IsaUniqueNamer();
        private readonly TypeIsaVisitor typeIsaVisitor;

        private readonly IsaUniqueNamer namerForFunctions;

        private readonly IVariableTranslationFactory varTranslationFactory;

        private readonly string vcAssmName = "VC";
        private readonly VcBoogieInfo vcBoogieInfo;

        private readonly VCExpressionGenerator vcExprGen;

        private readonly IEnumerable<Function> vcFunctions;
        private readonly IVCVarFunTranslator vcVarFunTranslator;

        private readonly IDictionary<Axiom, int> axiomIdDict;

        private readonly Func<Axiom, string> axiomToVcLemmaName;

        public EndToEndVCProof(
            BoogieMethodData methodData,
            IProgramAccessor programAccessor,
            IEnumerable<Function> vcFunctions,
            VcBoogieInfo vcBoogieInfo,
            CFGRepr afterPassificationCfg,
            CFGRepr finalCfg,
            string entryBlockCorrectLemma,
            string axiomLocaleName,
            Func<Axiom, string> axiomToVcLemmaName,
            IVariableTranslationFactory varTranslationFactory,
            IVCVarFunTranslator vcVarFunTranslator,
            TypePremiseEraserFactory eraserFactory,
            IsaUniqueNamer namerForFunctions,
            VCExpressionGenerator vcExprGen)
        {
            this.methodData = methodData;
            this.vcFunctions = vcFunctions;
            this.programAccessor = programAccessor;
            this.vcBoogieInfo = vcBoogieInfo;
            this.afterPassificationCfg = afterPassificationCfg;
            this.finalCfg = finalCfg;
            this.entryBlockCorrectLemma = entryBlockCorrectLemma;
            this.axiomLocaleName = axiomLocaleName;
            this.axiomToVcLemmaName = axiomToVcLemmaName;
            this.varTranslationFactory = varTranslationFactory;
            this.vcVarFunTranslator = vcVarFunTranslator;
            this.eraserFactory = eraserFactory;
            this.namerForFunctions = namerForFunctions;
            this.vcExprGen = vcExprGen;
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(varTranslationFactory);
            typeIsaVisitor = new TypeIsaVisitor(varTranslationFactory.CreateTranslation().TypeVarTranslation);

            boogieContext = new BoogieContextIsa(
                IsaCommonTerms.TermIdentFromName("A"),
                IsaCommonTerms.TermIdentFromName("M"),
                IsaCommonTerms.TermIdentFromName("\\<Lambda>"),
                IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
                IsaCommonTerms.EmptyList
            );

            axiomIdDict = new Dictionary<Axiom, int>();
            var count = 0;
            foreach (var axiom in methodData.Axioms)
            {
                axiomIdDict.Add(axiom, count);
                count++;
            }
        }

        private IEnumerable<Variable> ProgramVariables => methodData.AllVariables();

        public IEnumerable<OuterDecl> GenerateProof(out Term vcAssm, out LemmaDecl endToEndLemma)
        {
            var result = new List<OuterDecl>();

            result.AddRange(VCFunDefinitions().Values);
            result.AddRange(FunCorresLemmas().Values);
            result.AddRange(ctorFun(vcBoogieInfo.VcAxiomsInfo));
            result.Add(new DeclareDecl("One_nat_def[simp del]"));
            endToEndLemma = FinalLemma(out vcAssm);
            result.Add(endToEndLemma);
            return result;
        }

        private IDictionary<Function, OuterDecl> VCFunDefinitions()
        {
            return BasicUtil.ApplyFunDict(methodData.Functions, VCFunDefinition);
        }

        //VC function that represents f
        private OuterDecl VCFunDefinition(Function f)
        {
            var uniqueNamer = new IsaUniqueNamer();

            //LHS of function definition "vc_fun boogie_fun arg1 arg2 ... argN = ..." 
            Term funTerm = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(f, f.Name));
            IList<Term> argsLhs = new List<Term> {boogieContext.absValTyMap, funTerm};

            var vcVars = new List<VCExprVar>();
            var varToTerm = new Dictionary<VCExprVar, Term>();
            var vcValueParams = new List<Term>();
            foreach (var v in f.InParams)
            {
                Term vTerm = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(v, v.Name));
                vcValueParams.Add(vTerm);
                var vVcVar = vcExprGen.Variable(v.Name, v.TypedIdent.Type);
                vcVars.Add(vVcVar);
                varToTerm.Add(vVcVar, vTerm);
            }

            TypeUtil.SplitTypeParams(f.TypeParameters,
                f.InParams.Select(v => v.TypedIdent.Type),
                out var _,
                out var implicitTypeVars);

            var extractorTranslator = new TypeExtractorTranslator(boogieContext, varToTerm);
            var boogieTyParams = new List<Term>();
            var typeVarToTerm = new Dictionary<TypeVariable, Term>();
            var eraserProvider = eraserFactory.NewEraser();
            //if there are no type parameters, the axiom builder may be null if the entire program has no polymorphism
            var dummyVar = f.TypeParameters.Any()
                ? vcExprGen.Variable("dummy", eraserProvider.AxiomBuilder.T)
                : null;
            foreach (var typeVar in f.TypeParameters)
            {
                Term typeVarClosedIsa;

                if (implicitTypeVars.Contains(typeVar))
                {
                    var extractor = eraserProvider.BestTypeVarExtractor(
                        typeVar,
                        dummyVar,
                        f.InParams.Select(v => v.TypedIdent.Type).ToList(),
                        vcVars);

                    typeVarClosedIsa = extractorTranslator.TranslateExtractor(extractor);
                }
                else
                {
                    typeVarClosedIsa = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(typeVar, typeVar.Name));
                    argsLhs.Add(typeVarClosedIsa);
                }

                boogieTyParams.Add(IsaBoogieVC.ClosedToTy(typeVarClosedIsa));
                typeVarToTerm.Add(typeVar, typeVarClosedIsa);
            }

            //add values after type variables
            argsLhs.AddRange(vcValueParams);


            /* arguments used to invoke the Boogie function:
             * type parameters => use extractors
             * function values => same as for VC function, except for primitive typed arguments for which one must construct
             * the corersponding Boogie value
             */
            var boogieValParams =
                vcValueParams.Select((p, idx) =>
                {
                    var v = f.InParams[idx];
                    if (TypeUtil.IsPrimitive(v.TypedIdent.Type))
                        return pureValueIsaTransformer.ConstructValue(p, v.TypedIdent.Type);

                    return p;
                }).ToList();

            Term boogieFunApp = new TermApp(funTerm,
                new List<Term> {new TermList(boogieTyParams), new TermList(boogieValParams)});

            //RHS of function definition, case splitting on whether boogie function reduces
            Term res = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName("res", "res"));

            var typeVisitorSubst = new TypeIsaVisitor(new SimpleVarSubstitution<TypeVariable>(typeVarToTerm), true);
            var outputType = f.OutParams[0].TypedIdent.Type;
            var outputTypeIsa = typeVisitorSubst.Translate(outputType);

            var outputValueIfNotReduced = IsaBoogieVC.ValOfClosedTy(boogieContext.absValTyMap, outputTypeIsa);

            Term functionBody = new TermCaseOf(
                boogieFunApp,
                new List<Tuple<Term, Term>>
                {
                    Tuple.Create(IsaCommonTerms.SomeOption(res),
                        TypeUtil.IsPrimitive(outputType)
                            ? pureValueIsaTransformer.DestructValue(res, outputType)
                            : res),
                    Tuple.Create(IsaCommonTerms.NoneOption(),
                        TypeUtil.IsPrimitive(outputType)
                            ? pureValueIsaTransformer.DestructValue(outputValueIfNotReduced, outputType)
                            : outputValueIfNotReduced)
                }
            );

            return new FunDecl(VCFunName(f), null,
                new List<Tuple<IList<Term>, Term>> {Tuple.Create(argsLhs, functionBody)});
        }

        private string VCFunName(Function f)
        {
            return "vc_fun_" + f.Name;
        }

        private IDictionary<Function, LemmaDecl> FunCorresLemmas()
        {
            return BasicUtil.ApplyFunDict(methodData.Functions, FunCorres);
        }

        private LemmaDecl FunCorres(Function f)
        {
            var uniqueNamer = new IsaUniqueNamer();

            Term funTerm = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(f, f.Name));

            #region vc function call

            IList<Term> vcFunArgs = new List<Term> {boogieContext.absValTyMap, funTerm};

            TypeUtil.SplitTypeParams(f.TypeParameters, f.InParams.Select(v => v.TypedIdent.Type),
                out var explicitTypeVars, out var implicitTypeVars);

            vcFunArgs.AddRange(explicitTypeVars.Select(tv =>
                IsaBoogieVC.TyToClosed(IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(tv, tv.Name)))));

            var vcVars = new List<VCExprVar>();
            var varToTerm = new Dictionary<VCExprVar, Term>();
            var vcValueParams = new List<Term>();
            foreach (var v in f.InParams)
            {
                Term vTerm = IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(v, v.Name));
                vcValueParams.Add(vTerm);
                var vVcVar = vcExprGen.Variable(v.Name, v.TypedIdent.Type);
                vcVars.Add(vVcVar);
                varToTerm.Add(vVcVar, vTerm);
            }

            vcFunArgs.AddRange(vcValueParams);

            Term vc_f = IsaCommonTerms.TermIdentFromName(VCFunName(f));
            var vcFunctionCall = new TermApp(vc_f, vcFunArgs);

            #endregion

            #region Boogie function call

            var boogieTypeParams = f.TypeParameters
                .Select(tv => (Term) IsaCommonTerms.TermIdentFromName(uniqueNamer.GetName(tv, tv.Name))).ToList();
            var boogieTypeParamsList = new TermList(boogieTypeParams);
            var boogieValueParams = vcValueParams.Select((p, idx) =>
            {
                var paramType = f.InParams[idx].TypedIdent.Type;
                if (TypeUtil.IsPrimitive(paramType))
                    return pureValueIsaTransformer.ConstructValue(p, f.InParams[idx].TypedIdent.Type);

                return p;
            }).ToList();
            var boogieValueParamsList = new TermList(boogieValueParams);
            var boogieFunctionCall = new TermApp(funTerm, new List<Term> {boogieTypeParamsList, boogieValueParamsList});

            #endregion

            #region lemma assumptions

            var assms = new List<Term>();
            var assmLabels = new List<string>();

            string ClosedAssmLabel(int i)
            {
                return "closed" + i;
            }

            string TypeOfArgAssmLabel(int i)
            {
                return "typeOfArg" + i;
            }

            //funtion interpretation well-formed assumption
            assms.Add(IsaBoogieTerm.FunInterpSingleWf(boogieContext.absValTyMap,
                IsaBoogieTerm.FunDecl(f, varTranslationFactory, namerForFunctions, false), funTerm));
            assmLabels.Add(finterpAssmName);

            //type variables closed assumption
            var closedAssmLabels = new List<string>();
            var closedIdx = 0;
            foreach (var t in boogieTypeParams)
            {
                assms.Add(IsaBoogieTerm.IsClosedType(t));
                assmLabels.Add(ClosedAssmLabel(closedIdx));
                closedAssmLabels.Add(ClosedAssmLabel(closedIdx));
                closedIdx++;
            }

            //type of value arguments assumption
            var typeVariableSubst = new Dictionary<TypeVariable, Term>();
            {
                var idx = 0;
                foreach (var tv in f.TypeParameters)
                {
                    typeVariableSubst.Add(tv, boogieTypeParams[idx]);
                    idx++;
                }
            }

            var typeIsaFuncVisitor = new TypeIsaVisitor(new SimpleVarSubstitution<TypeVariable>(typeVariableSubst));
            var typeOfValAssms = new List<string>();
            {
                var idx = 0;
                foreach (var t in vcValueParams)
                {
                    var paramType = f.InParams[idx].TypedIdent.Type;
                    if (!TypeUtil.IsPrimitive(paramType))
                    {
                        assms.Add(
                            TermBinary.Eq(IsaBoogieTerm.TypeToVal(boogieContext.absValTyMap, t),
                                typeIsaFuncVisitor.Translate(paramType))
                        );
                        assmLabels.Add(TypeOfArgAssmLabel(idx));
                        typeOfValAssms.Add(TypeOfArgAssmLabel(idx));
                    }

                    idx++;
                }
            }

            #endregion

            #region lemma statement

            var outputType = f.OutParams[0].TypedIdent.Type;

            Term ConstructOutputValue(Term rawOutputValue)
            {
                var result = rawOutputValue;
                if (TypeUtil.IsPrimitive(outputType))
                    result = pureValueIsaTransformer.ConstructValue(result, outputType);

                return result;
            }

            Term conclusion = TermBinary.Eq(boogieFunctionCall,
                IsaCommonTerms.SomeOption(ConstructOutputValue(vcFunctionCall)));

            var outputTypeIsa = typeIsaFuncVisitor.Translate(outputType);
            if (!TypeUtil.IsPrimitive(outputType))
            {
                //need to add type information
                var outputValType = IsaBoogieTerm.TypeToVal(boogieContext.absValTyMap, vcFunctionCall);

                Term outputValHasOutputType = TermBinary.Eq(outputValType, outputTypeIsa);
                conclusion = TermBinary.And(conclusion, outputValHasOutputType);
            }

            #endregion

            #region lemma proof

            var zReturnVal = uniqueNamer.GetName("z", "z");
            Term zReturnValTerm = IsaCommonTerms.TermIdentFromName(zReturnVal);

            var proofMethods = new List<string>
            {
                "proof -",
                "from " + typeOfValAssms.SpaceAggregate() + " " + finterpAssmName +
                " obtain " + zReturnVal + " where W:" + IsaPrettyPrinterHelper.Inner(
                    TermBinary.Eq(boogieFunctionCall,
                            IsaCommonTerms.SomeOption(
                                ConstructOutputValue(IsaCommonTerms.TermIdentFromName(zReturnVal))))
                        .ToString()) +
                (!TypeUtil.IsPrimitive(outputType)
                    ? " " +
                      IsaPrettyPrinterHelper.Inner(
                          TermBinary.Eq(IsaBoogieTerm.TypeToVal(boogieContext.absValTyMap, zReturnValTerm),
                              outputTypeIsa).ToString()
                      )
                    : ""),
                "  apply (simp only: fun_interp_single_wf.simps) ",
                "  apply (erule allE[where ?x=" + IsaPrettyPrinterHelper.Inner(boogieTypeParamsList.ToString()) + "])",
                "  apply (simp add: " + closedAssmLabels.SpaceAggregate() + ")",
                "  apply (erule allE[where ?x=" + IsaPrettyPrinterHelper.Inner(boogieValueParamsList.ToString()) +
                "])?",
                (outputType.IsBool ? "using tbool_boolv" : "") + (outputType.IsInt ? "using tint_intv" : "") +
                (outputType.IsReal ? "using treal_realv" : "") +
                " by auto"
            };

            //prove that one can express each implicit type variable using a corresponding extractor
            var extractorTranslator = new TypeExtractorTranslator(boogieContext, varToTerm);
            var eraserProvider = eraserFactory.NewEraser();
            //axiombuilder may be null if program has no polymorphism
            var dummyVar = f.TypeParameters.Any() ? vcExprGen.Variable("dummy", eraserProvider.AxiomBuilder.T) : null;
            var valueParamTypes = f.InParams.Select(v => v.TypedIdent.Type).ToList();

            var explicitTypeVarAssms = "";
            var proofMethodsExtractors = new List<string>();
            {
                var idx = 0;
                foreach (var tv in f.TypeParameters)
                {
                    if (implicitTypeVars.Contains(tv))
                    {
                        var extractor = eraserProvider.BestTypeVarExtractor(
                            tv,
                            dummyVar,
                            valueParamTypes,
                            vcVars
                        );
                        var extractorTerm = extractorTranslator.TranslateExtractor(extractor);

                        var prefix = "moreover from ";
                        if (idx == 0) prefix = "from ";
                        proofMethodsExtractors.Add(
                            prefix + typeOfValAssms.SpaceAggregate() + " have " +
                            " \" " + TermBinary.Eq(boogieTypeParams[idx], IsaBoogieVC.ClosedToTy(extractorTerm)) +
                            "\"" +
                            " using  closed_inv2 " + ClosedAssmLabel(idx) + " by auto"
                        );
                    }
                    else
                    {
                        explicitTypeVarAssms = explicitTypeVarAssms + " " + "closed_inv2_2[OF " + ClosedAssmLabel(idx) +
                                               "]";
                    }

                    idx++;
                }
            }

            proofMethods.AddRange(proofMethodsExtractors);

            proofMethods.Add((proofMethodsExtractors.Count > 1 ? "ultimately " : "from this ") +
                             " show ?thesis " +
                             (typeOfValAssms.Any() || !String.IsNullOrEmpty(explicitTypeVarAssms)
                                 ? "using " + typeOfValAssms.SpaceAggregate() + explicitTypeVarAssms
                                 : "")
            );
            proofMethods.Add("by (simp add: W) qed");


            return new LemmaDecl(FunCorresName(f), ContextElem.CreateWithAssumptions(assms, assmLabels), conclusion,
                new Proof(proofMethods));

            #endregion
        }

        private LemmaDecl FinalLemma(out Term vcAssm)
        {
            var uniqueNamer = new IsaUniqueNamer();
            //adjust declToVCMapping to include vc type declarations
            var typeDeclTranslation = new GenericTypeDeclTranslation(uniqueNamer);
            var declToVCMapping =
                LemmaHelper.DeclToTerm(ProgramVariables, vcFunctions, typeDeclTranslation, uniqueNamer);
            var declIds = declToVCMapping.Values.Select(t => ((TermIdent) t).Id).ToList();
            var absValType = new VarType("a");
            var concretePureTyIsaTransformer = LemmaHelper.ConretePureTyIsaTransformer(absValType);
            var declTypes = declToVCMapping.Keys.Select(nd => concretePureTyIsaTransformer.Translate(nd)).ToList();
            //handle Boogie functions separately, since VC version has different type
            //TODO: find cleaner way to handle this (PassiveLemmaManager also uses such a suboptimal solution)
            foreach (var boogieFun in methodData.Functions)
            {
                var id = new SimpleIdentifier(uniqueNamer.GetName(boogieFun, "vc_" + boogieFun.Name));
                declIds.Add(id);
                declToVCMapping.Add(boogieFun, new TermIdent(id));
                TypeUtil.SplitTypeParams(boogieFun.TypeParameters, boogieFun.InParams.Select(v => v.TypedIdent.Type),
                    out var explicitTypeVars, out _);

                var typeIsa = concretePureTyIsaTransformer.Translate(new Function(null, boogieFun.Name,
                    explicitTypeVars, boogieFun.InParams, boogieFun.OutParams[0]));
                declTypes.Add(typeIsa);
            }

            var vcAssmWithoutAxioms = vcBoogieInfo.VcInst.GetVCObjInstantiation(finalCfg.entry, declToVCMapping);

            var vcAssmWithoutQuant = vcBoogieInfo.VcAxioms.Reverse().Aggregate(vcAssmWithoutAxioms, (current, vcAx) =>
                new TermBinary(vcBoogieInfo.VcInstAxiom.GetVCObjInstantiation(vcAx, declToVCMapping), current,
                    TermBinary.BinaryOpCode.MetaImp));

            /*List<TypeIsa> declTypes = methodData.Functions.Select(f => pureTyIsaTransformer.Translate(f)).ToList();
            declTypes.AddRange(ProgramVariables.Select(v => pureTyIsaTransformer.Translate(v)));*/
            vcAssm = declIds.Any()
                ? TermQuantifier.MetaAll(declIds, declTypes, vcAssmWithoutQuant)
                : vcAssmWithoutQuant;

            var multiRed = IsaBoogieTerm.RedCFGMulti(
                BoogieContextIsa.CreateWithNewVarContext(boogieContext,
                    new TermTuple(programAccessor.ConstsAndGlobalsDecl(), programAccessor.ParamsAndLocalsDecl())),
                programAccessor.CfgDecl(),
                IsaBoogieTerm.CFGConfigNode(
                    new NatConst(afterPassificationCfg.GetUniqueIntLabel(afterPassificationCfg.entry)),
                    IsaBoogieTerm.Normal(normalInitState)),
                IsaBoogieTerm.CFGConfig(finalNode, finalState)
            );
            var closedAssm = EndToEndAssumptions.ClosednessAssumption(boogieContext.absValTyMap);
            var nonEmptyTypesAssm = EndToEndAssumptions.NonEmptyTypesAssumption(boogieContext.absValTyMap);
            var finterpAssm = IsaBoogieTerm.FunInterpWf(boogieContext.absValTyMap, programAccessor.FunctionsDecl(),
                boogieContext.funContext);
            //need to explicitly give type for normal state, otherwise Isabelle won't know that the abstract value type is the same as used in the VC
            var axiomAssm =
                EndToEndAssumptions.AxiomAssumption(boogieContext, programAccessor,
                    new TermWithExplicitType(normalInitState, IsaBoogieType.NormalStateType(absValType)));
            var localsAssm = EndToEndAssumptions.LocalStateAssumption(boogieContext,
                programAccessor.ParamsAndLocalsDecl(), normalInitState);
            var globalsAssm = EndToEndAssumptions.GlobalStateAssumption(boogieContext,
                programAccessor.ConstsAndGlobalsDecl(), normalInitState);

            Term conclusion = new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.Neq);

            var contextElem = ContextElem.CreateWithAssumptions(
                new List<Term>
                    {multiRed, vcAssm, closedAssm, nonEmptyTypesAssm, finterpAssm, axiomAssm, localsAssm, globalsAssm},
                new List<string>
                {
                    RedAssmName, vcAssmName, closedAssmName, nonEmptyTypesAssmName, finterpAssmName, axiomAssmName,
                    paramsLocalsAssmName, constsGlobalsAssmName
                });
            return new LemmaDecl(PhasesTheories.LocalEndToEndName(), contextElem, conclusion, FinalProof());
        }

        private string ctorLemmaName(Type type)
        {
            return ctorName + "_" + type;
        }

        private string ctorLemmaName(TypeCtorDecl decl)
        {
            return ctorName + "_" + decl.Name;
        }

        private List<OuterDecl> ctorFun(IEnumerable<VCAxiomInfo> vcAxiomsInfo)
        {
            var funEquations = new List<Tuple<IList<Term>, Term>>();
            var typeConstrCtorList = new List<Term>();
            var lemmas = new List<LemmaDecl>();

            Term ctorFun = IsaCommonTerms.TermIdentFromName(ctorName);
            Func<Type, Term, int, LemmaDecl> basicTypeLemma = (ty, tyTerm, ctorValue) =>
            {
                return
                    new LemmaDecl(ctorLemmaName(ty),
                        TermBinary.Eq(new TermApp(ctorFun, tyTerm), new IntConst(ctorValue)),
                        new Proof(new List<string> {"by simp"}));
            };

            foreach (var vcAxInfo in vcAxiomsInfo)
                if (vcAxInfo is CtorBasicTypeAxiomInfo ctorBasicAxInfo)
                {
                    if (ctorBasicAxInfo.Type.IsInt)
                    {
                        funEquations.Add(new Tuple<IList<Term>, Term>(
                            new List<Term> {IsaBoogieType.PrimType(IsaBoogieType.IntType(), true)},
                            new IntConst(ctorBasicAxInfo.CtorValue)));
                        lemmas.Add(basicTypeLemma(ctorBasicAxInfo.Type,
                            IsaBoogieType.PrimType(IsaBoogieType.IntType(), true), ctorBasicAxInfo.CtorValue));
                    }
                    else if (ctorBasicAxInfo.Type.IsBool)
                    {
                        funEquations.Add(new Tuple<IList<Term>, Term>(
                            new List<Term> {IsaBoogieType.PrimType(IsaBoogieType.BoolType(), true)},
                            new IntConst(ctorBasicAxInfo.CtorValue)));
                        lemmas.Add(basicTypeLemma(ctorBasicAxInfo.Type,
                            IsaBoogieType.PrimType(IsaBoogieType.BoolType(), true), ctorBasicAxInfo.CtorValue));
                    } 
                    else if (ctorBasicAxInfo.Type.IsReal)
                    {
                        funEquations.Add(new Tuple<IList<Term>, Term>(
                            new List<Term> {IsaBoogieType.PrimType(IsaBoogieType.RealType(), true)},
                            new IntConst(ctorBasicAxInfo.CtorValue)));
                        lemmas.Add(basicTypeLemma(ctorBasicAxInfo.Type,
                            IsaBoogieType.PrimType(IsaBoogieType.RealType(), true), ctorBasicAxInfo.CtorValue));
                    }
                    else
                    {
                        throw new NotImplementedException();
                    }
                }
                else if (vcAxInfo is CtorDeclAxiomInfo ctorDeclAxInfo)
                {
                    typeConstrCtorList.Add(new TermTuple(
                        new StringConst(ctorDeclAxInfo.Decl.Name),
                        new IntConst(ctorDeclAxInfo.CtorValue)));

                    var ids = Enumerable.Range(1, ctorDeclAxInfo.Decl.Arity)
                        .Select(i => (Identifier) new SimpleIdentifier("t" + i)).ToList();
                    var ctorApp =
                        new TermApp(ctorFun,
                            new TermApp(
                                IsaBoogieVC.VCTypeConstructor(ctorDeclAxInfo.Decl.Name, ctorDeclAxInfo.Decl.Arity),
                                ids.Select(id => (Term) new TermIdent(id)).ToList())
                        );
                    var body = TermBinary.Eq(ctorApp, new IntConst(ctorDeclAxInfo.CtorValue));
                    var statement = ids.Any() ? (Term) TermQuantifier.ForAll(ids, null, body) : body;
                    lemmas.Add(new LemmaDecl(ctorLemmaName(ctorDeclAxInfo.Decl), statement,
                        new Proof(new List<string> {"by " + ProofUtil.Simp(ctorDeclListName + "_def")})));
                }

            var def = DefDecl.CreateWithoutArg(ctorDeclListName, new TermList(typeConstrCtorList));

            funEquations.Add(new Tuple<IList<Term>, Term>(
                new List<Term> {IsaCommonTerms.TermIdentFromName("(TConC s _)")},
                IsaCommonTerms.TheOption(new TermApp(IsaCommonTerms.TermIdentFromName("map_of"),
                    new List<Term>
                        {IsaCommonTerms.TermIdentFromName(ctorDeclListName), IsaCommonTerms.TermIdentFromName("s")})
                )));

            var result =
                new List<OuterDecl>
                {
                    def,
                    new FunDecl(ctorName,
                        new ArrowType(IsaBoogieVC.BoogieClosedType(), PrimitiveType.CreateIntType()),
                        funEquations)
                };
            result.AddRange(lemmas);
            return result;
        }

        private Proof FinalProof()
        {
            var sb = new StringBuilder();
            sb.AppendLine("proof -");

            sb.AppendLine("let " + normalRestrictedStateName + " = " +
                          "\"" + IsaBoogieTerm.NstateGlobalRestriction(normalInitState,
                              IsaCommonTerms.TermIdentFromName(programAccessor.ConstsDecl())) + "\"");
            sb.AppendLine("let " + qVarContext + " = " + "\"" + new TermTuple(new List<Term>
            {
                programAccessor.ConstsAndGlobalsDecl(),
                programAccessor.ParamsAndLocalsDecl()
            }) + "\"");
            sb.AppendLine("let " + qVarContextConst + " = " + "\"" + new TermWithExplicitType(new TermTuple(
                new List<Term>
                {
                    IsaCommonTerms.TermIdentFromName(programAccessor.ConstsDecl()),
                    IsaCommonTerms.EmptyList
                }), IsaBoogieType.VarContextType()) + "\"");

            //functions
            foreach (var f in methodData.Functions)
            {
                Term fStringConst = new StringConst(f.Name);
                sb.Append("let " + FunAbbrev(f) + " = ");
                sb.AppendInner("opaque_comp the " + boogieContext.funContext + " " + fStringConst);
                sb.AppendLine();
                sb.Append("have " + InterpMemName(f) + ":");
                sb.AppendInner(
                    new TermBinary(new TermApp(boogieContext.funContext, fStringConst),
                        IsaCommonTerms.SomeOption(IsaCommonTerms.TermIdentFromName(FunAbbrev(f))),
                        TermBinary.BinaryOpCode.Eq).ToString());
                sb.AppendLine();
                sb.AppendLine("apply " + ProofUtil.SimpOnly("opaque_comp_def"));
                sb.AppendLine("by (rule " + ProofUtil.OF(
                        "finterp_member", finterpAssmName, programAccessor.MembershipLemma(f)) + ")"
                );
            }

            //variables
            AppendStateCorres(sb, paramsLocalsAssmName, methodData.InParams, qVarContext, normalInitState,
                StateCorresKind.Local);
            AppendStateCorres(sb, paramsLocalsAssmName, methodData.Locals, qVarContext, normalInitState,
                StateCorresKind.Local);
            AppendStateCorres(sb, constsGlobalsAssmName, methodData.Constants, qVarContext, normalInitState,
                StateCorresKind.Global);
            AppendStateCorres(sb, constsGlobalsAssmName, methodData.GlobalVars, qVarContext, normalInitState,
                StateCorresKind.Global);
            AppendStateCorres(sb,
                ProofUtil.OF("state_typ_wf_const_restr", constsGlobalsAssmName),
                methodData.Constants,
                qVarContextConst,
                normalRestrictedState,
                StateCorresKind.OnlyConst);
            if (methodData.Axioms.Any())
            {
                sb.AppendLine("have " + axiomLocaleFact + ":\"" + AxiomLocaleAssm() + "\"");
                AppendAxiomLocaleAssmProof(sb);
            }

            //conclusion


            sb.Append("show ");
            sb.AppendInner(new TermBinary(finalState, IsaBoogieTerm.Failure(), TermBinary.BinaryOpCode.Neq).ToString());
            sb.AppendLine();

            sb.AppendLine("apply (rule " + ProofUtil.OF(entryBlockCorrectLemma, "_", RedAssmName) + ")");
            sb.AppendLine("apply " + ProofUtil.SimpOnly("passification_def"));
            sb.AppendLine("apply (intro conjI)?");

            foreach (var f in methodData.Functions)
                //TODO: Use stored ML theorems to avoid re-instantiation
                AppendFunctionRelAssmProof(f, sb);

            foreach (var v in ProgramVariables) AppendStateLookupAssmProof(v, sb);

            sb.AppendLine("apply " + ProofUtil.Simp(closedAssmName));
            sb.AppendLine("apply (rule " + vcAssmName + ")");

            AppendVcAxiomsProof(vcBoogieInfo.VcAxiomsInfo, sb);

            /* TODO
            foreach(Axiom ax in methodData.Axioms)
            {
                sb.AppendLine("apply " + ProofUtil.SimpOnly(vcinstAxiom.GetVCObjNameRef(ax) + "_def"));
                sb.AppendLine("apply (rule expr_to_vc[OF " + EvaluationName(ax) + "])");               
                sb.AppendLine("apply(tactic \\<open> b_vc_expr_rel_tac @{context} " + storedFunctionThms + " [] 1 \\<close>)");
            }
            */

            sb.AppendLine("done");
            sb.AppendLine("qed");

            return new Proof(new List<string> {sb.ToString()});
        }

        private void AppendStateLookupAssmProof(Variable v, StringBuilder sb, bool constOnly = false)
        {
            var scName = constOnly ? StateCorresConstName(v) : StateCorresName(v);
            var evalTac = "rule " + ProofUtil.OF("HOL.conjunct1", scName);
            var typeTac = TypeUtil.IsPrimitive(v.TypedIdent.Type)
                ? ""
                : " , rule " + ProofUtil.OF("HOL.conjunct2", scName);
            sb.AppendLine("apply (" + evalTac + typeTac + ")");
        }

        private void AppendFunctionRelAssmProof(Function f, StringBuilder sb)
        {
            sb.AppendLine("apply " + ProofUtil.Simp(InterpMemName(f)));
            sb.AppendLine("apply ((rule allI | rule impI)+)?");
            sb.AppendLine(
                ProofUtil.Apply(
                    ProofUtil.MLTactic("vc_fun_corres_tac " + MLUtil.ContextAntiquotation() + " " +
                                       MLUtil.IsaToMLThm(FunCorresName(f)) + " " +
                                       MLUtil.IsaToMLThm(finterpAssmName) + " " +
                                       MLUtil.IsaToMLThm(programAccessor.MembershipLemma(f)) + " " +
                                       MLUtil.IsaToMLThm(InterpMemName(f)), 1)));
        }

        /// <summary>
        ///     have ax_loc:"axioms_locale A (Find_before_cfg_to_dag_prog.constants_vdecls_Find,[]) Γ ?nsc ?f (vc_fun_f A ?f)
        ///     (convert_val_to_int  (the  (lookup_var  ?Λc ?nsc 0)))"
        /// </summary>
        /// <returns></returns>
        private Term AxiomLocaleAssm()
        {
            var args = new List<Term>
            {
                boogieContext.absValTyMap
            };
            //if no constants, then locale does not depend on variable context or on state
            if (methodData.Constants.Any())
            {
                args.Add(IsaCommonTerms.TermIdentFromName(qVarContextConst));
                args.Add(boogieContext.funContext);
                args.Add(normalRestrictedState);
            }
            else
            {
                args.Add(boogieContext.funContext);
            }


            foreach (var fun in methodData.Functions)
            {
                var boogieFun = IsaCommonTerms.TermIdentFromName(FunAbbrev(fun));
                args.Add(boogieFun);
                args.Add(new TermApp(IsaCommonTerms.TermIdentFromName(VCFunName(fun)),
                    boogieContext.absValTyMap,
                    boogieFun));
            }

            Term varContextConst = IsaCommonTerms.TermIdentFromName(qVarContextConst);

            foreach (var v in methodData.Constants) args.Add(VcVarValue(v, varContextConst, normalRestrictedState));

            return new TermApp(IsaCommonTerms.TermIdentFromName(axiomLocaleName), args);
        }

        private void AppendAxiomLocaleAssmProof(StringBuilder sb)
        {
            sb.AppendLine("unfolding " + axiomLocaleName + "_def");
            sb.AppendLine("apply (intro conjI)");

            foreach (var f in methodData.Functions)
                //TODO: Use stored ML theorems to avoid re-instantiation
                AppendFunctionRelAssmProof(f, sb);

            foreach (var v in methodData.Constants) AppendStateLookupAssmProof(v, sb, true);

            sb.AppendLine("apply " + ProofUtil.Simp(closedAssmName));
            sb.AppendLine("done");
        }

        private void AppendVcAxiomsProof(IEnumerable<VCAxiomInfo> vcAxiomsInfo, StringBuilder sb)
        {
            foreach (var vcAx in vcAxiomsInfo)
            {
                if (!(vcAx is VcBoogieAxiomInfo))
                    sb.AppendLine("unfolding " + vcBoogieInfo.VcInstAxiom.GetVCObjNameRef(vcAx.Expr) + "_def");

                if (vcAx is VcBoogieAxiomInfo vcBoogieAxInfo)
                {
                    //need to sync lookup in full context with constant only context for all lookups that may appear in the axiom
                    var v = new VariableCollector();
                    v.Visit(vcBoogieAxInfo.Axiom.Expr);
                    foreach (var usedVar in v.usedVars)
                        if (usedVar is Constant)
                            /*we only need to apply the substitution if the constant value is already bound in the axiom
                             *otherwise we can directly apply the axiom lemma -> hence apply substitution optionally
                             */
                            sb.AppendLine(ProofUtil.Apply(ProofUtil.Optional(ProofUtil.Repeat("subst " +
                                ProofUtil.OF("lookup_var_const_restr",
                                    programAccessor.GlobalsLocalsDisjointLemma(),
                                    programAccessor.ConstantMembershipLemma(usedVar))))));

                    var axiomEvalTrue =
                        ProofUtil.OF("axioms_sat_mem", programAccessor.MembershipLemma(vcBoogieAxInfo.Axiom),
                            axiomAssmName
                        );

                    sb.AppendLine(ProofUtil.Apply("rule " + ProofUtil.OF(
                            axiomToVcLemmaName(vcBoogieAxInfo.Axiom),
                            axiomLocaleFact,
                            axiomEvalTrue
                        )
                    ));
                }
                else if (vcAx is VcFunctionAxiomInfo vcFunAxInfo)
                {
                    sb.AppendLine(ProofUtil.Apply("fun_output_axiom NonEmptyTypes: " + nonEmptyTypesAssmName));
                    sb.AppendLine("using closed_inv1 " +
                                  ProofUtil.OF("finterp_extract_2",
                                      finterpAssmName,
                                      programAccessor.MembershipLemma(vcFunAxInfo.Function),
                                      InterpMemName(vcFunAxInfo.Function)) + " " +
                                  ProofUtil.Apply("simp")
                    );
                }
                else if (vcAx is VarAxiomInfo varAxiomInfo)
                {
                    if (vcVarFunTranslator.TranslateVCVar(varAxiomInfo.VcVar, out var v))
                        sb.AppendLine(ProofUtil.Apply("var_type_axiom TypeEq: " +
                                                      ProofUtil.OF("HOL.conjunct2", StateCorresName(v))));
                    else
                        throw new ProofGenUnexpectedStateException(GetType(),
                            "Can't translate vc variable to Boogie variable");
                }
                else if (vcAx is CtorBasicTypeAxiomInfo ctorBasicTyAxiomInfo)
                {
                    sb.AppendLine(ProofUtil.Apply("rule " + ctorLemmaName(ctorBasicTyAxiomInfo.Type)));
                }
                else if (vcAx is CtorDeclAxiomInfo ctorDeclAxiomInfo)
                {
                    sb.AppendLine(ProofUtil.Apply("rule " + ctorLemmaName(ctorDeclAxiomInfo.Decl)));
                }
                else if (vcAx is LeftInverseAxiomInfo leftInvInfo)
                {
                    sb.AppendLine(ProofUtil.Apply("rule " +
                                                  IsaBoogieVC.LeftInvLemmaName(leftInvInfo.projectedIdx,
                                                      leftInvInfo.Decl.Arity)));
                }
                else if (vcAx is BasicTypeCastAxiomInfo castAxiomInfo)
                {
                    var isBool = castAxiomInfo.Type.IsBool;
                    var isInt = castAxiomInfo.Type.IsInt;
                    var isReal = castAxiomInfo.Type.IsReal;
                    
                    if (!isBool && !isInt && !isReal)
                        throw new ProofGenUnexpectedStateException(GetType(),
                            "only support int, bool, and reals as built-in types");

                    switch (castAxiomInfo.CastKind)
                    {
                        case TypeCastKind.BoxedOfUnboxed:
                            if (isBool)
                                sb.AppendLine(ProofUtil.Apply("rule bool_inverse_1"));
                            else if (isInt)
                                sb.AppendLine(ProofUtil.Apply("rule int_inverse_1"));
                            else
                                sb.AppendLine(ProofUtil.Apply("rule real_inverse_1"));
                            break;
                        case TypeCastKind.UnboxedOfBoxed:
                            if (isBool)
                                sb.AppendLine(ProofUtil.Apply("rule bool_inverse_2"));
                            else if (isInt)
                                sb.AppendLine(ProofUtil.Apply("rule int_inverse_2"));
                            else
                                sb.AppendLine(ProofUtil.Apply("rule real_inverse_2"));
                            break;
                        case TypeCastKind.TypeOfBoxed:
                            if (isBool)
                                sb.AppendLine(ProofUtil.Apply("rule bool_type"));
                            else if(isInt)
                                sb.AppendLine(ProofUtil.Apply("rule int_type"));
                            else
                                sb.AppendLine(ProofUtil.Apply("rule real_type"));
                            break;
                        default:
                            throw new ArgumentOutOfRangeException();
                    }
                }
            }
        }

        private Term VcVarValue(Variable v, Term varContext, Term normalState)
        {
            var variableTranslation = varTranslationFactory.CreateTranslation().VarTranslation;
            if (variableTranslation.TryTranslateVariableId(v, out var vNatConst, out var _))
            {
                var stateEval = IsaBoogieTerm.LookupVar(varContext, normalState, vNatConst);
                return pureValueIsaTransformer.DestructValue(IsaCommonTerms.TheOption(stateEval), v.TypedIdent.Type);
            }

            throw new ProofGenUnexpectedStateException("Could not translate variable");
        }

        private void AppendStateCorres(StringBuilder sb, string assm, IEnumerable<Variable> vars, string varContext,
            Term normalState, StateCorresKind scKind)
        {
            var variableTranslation = varTranslationFactory.CreateTranslation().VarTranslation;
            foreach (var v in vars)
                if (variableTranslation.TryTranslateVariableId(v, out var vNatConst, out var isBoundVar))
                {
                    var scName = scKind == StateCorresKind.OnlyConst ? StateCorresConstName(v) : StateCorresName(v);
                    sb.Append("from " + assm + " have " + scName + ":");
                    var stateEval = IsaBoogieTerm.LookupVar(IsaCommonTerms.TermIdentFromName(varContext), normalState,
                        vNatConst);
                    var stateEvalRhs = IsaCommonTerms.SomeOption(
                        pureValueIsaTransformer.ConstructValue(
                            pureValueIsaTransformer.DestructValue(
                                IsaCommonTerms.TheOption(stateEval),
                                v.TypedIdent.Type),
                            v.TypedIdent.Type)
                    );
                    Term stateEvalType =
                        TermBinary.Eq(
                            IsaBoogieTerm.TypeToVal(boogieContext.absValTyMap, IsaCommonTerms.TheOption(stateEval)),
                            typeIsaVisitor.Translate(v.TypedIdent.Type));
                    sb.AppendInner(TermBinary.And(TermBinary.Eq(stateEval, stateEvalRhs),
                        stateEvalType).ToString());
                    sb.AppendLine();
                    sb.AppendLine("apply " + ProofUtil.SimpOnly("state_typ_wf_def"));
                    sb.AppendLine(ProofUtil.Apply("erule allE, erule allE, erule impE, rule " +
                                                  ProofUtil.OF("map_of_lookup_vdecls_ty",
                                                      (scKind == StateCorresKind.OnlyConst
                                                          ? programAccessor.ConstantMembershipLemma(v)
                                                          : programAccessor.MembershipLemma(v)))));
                                 
                    if (scKind == StateCorresKind.OnlyConst)
                        sb.AppendLine("apply (subst lookup_var_global_no_locals)+");
                    else if (scKind == StateCorresKind.Global)
                        sb.AppendLine("apply (subst " + ProofUtil.OF("lookup_var_global_disj",
                            programAccessor.GlobalsLocalsDisjointLemma(), programAccessor.MembershipLemma(v)) + ")+");
                    else if (scKind == StateCorresKind.Local)
                        sb.AppendLine("apply (subst " +
                                      ProofUtil.OF("lookup_var_local", programAccessor.MembershipLemma(v)) + ")+");
                    else
                        throw new ProofGenUnexpectedStateException("unexpected state corres kind");

                    sb.AppendLine("by (fastforce dest: tint_intv tbool_boolv treal_realv)");
                }
                else
                {
                    throw new ProofGenUnexpectedStateException("Could not translate variable");
                }
        }

        private string FunAbbrev(Function f)
        {
            return "?" + f.Name;
        }

        private string EvaluationName(Axiom a)
        {
            Contract.Requires(axiomIdDict != null);
            return "ea_" + axiomIdDict[a];
        }

        private string InterpMemName(Function f, bool ML = false)
        {
            return "im_" + f.Name + (ML ? "_ml" : "");
        }

        private string WfName(Function f)
        {
            return "i_" + f.Name;
        }

        private string FunCorresName(Function f, bool ML = false)
        {
            return "vc_" + f.Name + "_corres" + (ML ? "_ml" : "");
        }

        private string StateCorresName(Variable v)
        {
            return "sc_" + stateCorresNamer.GetName(v, v.Name);
        }

        private string StateCorresConstName(Variable v)
        {
            return "sc_const_" + stateCorresNamer.GetName(v, v.Name);
        }

        private enum StateCorresKind
        {
            Local,
            Global,
            OnlyConst
        }
    }
}