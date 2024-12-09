using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.ProgramToVCProof;
using ProofGeneration.Util;

namespace ProofGeneration.BoogieIsaInterface
{
    public enum VarKind
    {
        Constant,
        Global,
        ParamOrLocal
    }

    public class MembershipLemmaManager : IProgramAccessor
    {
        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor;

        private readonly IsaProgramGeneratorConfig config;

        // constants without globals membership
        private readonly IDictionary<Declaration, LemmaDecl> constantMembershipLemmas =
            new Dictionary<Declaration, LemmaDecl>();

        private readonly string consts;
        private readonly string uniqueConsts;
        private readonly string[] constsAndGlobalsDefs;
        private readonly Term constsAndGlobalsList;
        private readonly string constsWfName = "consts_wf";

        private readonly IVariableTranslationFactory factory;
        private readonly string funcsWfName = "funcs_wf";
        private readonly string globals;

        private readonly string globalsLocalsDisjName = "globals_locals_disj";
        private readonly string globalsMaxName = "globals_max";
        private readonly string globalsWfName = "globals_wf";
        private readonly List<LemmaDecl> helperLemmas = new List<LemmaDecl>();
        private readonly IsaBlockInfo isaBlockInfo;
        private readonly IsaBigBlockInfo isaBigBlockInfo;
        private readonly IsaProgramRepr isaProgramRepr;
        private readonly string locals;

        private readonly string localsMinName = "locals_min";
        private readonly string localsWfName = "locals_wf";
        private readonly IDictionary<Variable, LemmaDecl> lookupVarTyLemmas = new Dictionary<Variable, LemmaDecl>();
        private readonly IsaUniqueNamer lookupVarTyNamer = new();

        private readonly IDictionary<Declaration, LemmaDecl>
            membershipLemmas = new Dictionary<Declaration, LemmaDecl>();

        private readonly IsaUniqueNamer membershipNamer = new();
        private readonly string parameters;

        private readonly string[] paramsAndLocalsDefs;

        private readonly Term paramsAndLocalsList;

        private readonly string paramsWfName = "params_wf";

        //defer calls to parent, which are not handled here
        private readonly IProgramAccessor parent;

        private readonly string theoryName;
        private readonly TypeIsaVisitor typeIsaVisitor;
        private readonly string varContextWfName = "var_context_wf";

        //indicates whether this instance or any of its ancestors contains local method information (i.e., parameters, etc...)
        private readonly bool containsLocalInformation = true;

        /* There are two membership lemmas for each constant. So we need two different prefixes for the corresponding names.
           The following prefix is for the constant membership lemma that is declared first and used by the second 
           membership lemma.
         */
        private readonly string separateConstantMembershipLemmaPrefix = "mconst";

        /// <summary>
        /// Initializes a new instance of the <see cref="MembershipLemmaManager"/> class.
        /// Generated instance only has information about global data.
        /// </summary>
        public MembershipLemmaManager (
            IsaGlobalProgramRepr globalProgRepr,
            int globalsMax,
            IVariableTranslationFactory factory,
            string theoryName)
        {
            containsLocalInformation = false;
            this.factory = factory;
            this.theoryName = theoryName;
            typeIsaVisitor = new TypeIsaVisitor(factory.CreateTranslation().TypeVarTranslation);
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(factory);
            
            isaProgramRepr = new IsaProgramRepr(globalProgRepr, null, null, null, null, null, null);
            config = new IsaProgramGeneratorConfig(null, true, true, true, false, SpecsConfig.None, false);

            consts = QualifyAccessName(isaProgramRepr.GlobalProgramRepr.constantsDeclDef);
            uniqueConsts = QualifyAccessName(isaProgramRepr.GlobalProgramRepr.uniqueConstantsDeclDef);
            globals = QualifyAccessName(isaProgramRepr.GlobalProgramRepr.globalsDeclDef);

            constsAndGlobalsDefs =
                new[] {consts + "_def", globals + "_def"};
            constsAndGlobalsList =
                IsaCommonTerms.AppendList(IsaCommonTerms.TermIdentFromName(consts),
                    IsaCommonTerms.TermIdentFromName(globals));
            
            AddMinOrMaxLemma(true, globalsMax, VariableNames(constsAndGlobalsList));
            AddWellFormednessLemmas();
        }

        public MembershipLemmaManager(
            IsaProgramGeneratorConfig config,
            IsaProgramRepr isaProgramRepr,
            IsaBlockInfo isaBlockInfo,
            IsaBigBlockInfo isaBigBlockInfo,
            Tuple<int, int> GlobalsMaxLocalsMin,
            IVariableTranslationFactory factory,
            string theoryName
        )
        {
            parent = config.parentAccessor;
            this.isaProgramRepr = isaProgramRepr;
            this.factory = factory;
            this.theoryName = theoryName;
            this.config = config;
            this.isaBlockInfo = isaBlockInfo;
            this.isaBigBlockInfo = isaBigBlockInfo;
            typeIsaVisitor = new TypeIsaVisitor(factory.CreateTranslation().TypeVarTranslation);
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(factory);
            paramsAndLocalsDefs =
                new[] {isaProgramRepr.paramsDeclDef + "_def", isaProgramRepr.localVarsDeclDef + "_def"};

            parameters = config.generateParamsAndLocals
                ? QualifyAccessName(isaProgramRepr.paramsDeclDef)
                : parent.ParamsDecl();
            locals = config.generateParamsAndLocals
                ? QualifyAccessName(isaProgramRepr.localVarsDeclDef)
                : parent.LocalsDecl();
            paramsAndLocalsList =
                IsaCommonTerms.AppendList(IsaCommonTerms.TermIdentFromName(parameters),
                    IsaCommonTerms.TermIdentFromName(locals));

            consts = config.generateGlobalsAndConstants
                ? QualifyAccessName(isaProgramRepr.GlobalProgramRepr.constantsDeclDef)
                : parent.ConstsDecl();
            uniqueConsts = config.generateGlobalsAndConstants
              ? QualifyAccessName(isaProgramRepr.GlobalProgramRepr.uniqueConstantsDeclDef)
              : parent.UniqueConstsDecl();
            globals = config.generateGlobalsAndConstants
                ? QualifyAccessName(isaProgramRepr.GlobalProgramRepr.globalsDeclDef)
                : parent.GlobalsDecl();

            constsAndGlobalsDefs =
                new[] {consts + "_def", globals + "_def"};
            constsAndGlobalsList =
                IsaCommonTerms.AppendList(IsaCommonTerms.TermIdentFromName(consts),
                    IsaCommonTerms.TermIdentFromName(globals));
            AddDisjointnessLemmas(GlobalsMaxLocalsMin.Item1, GlobalsMaxLocalsMin.Item2);
            AddWellFormednessLemmas();
        }

        public string TheoryName()
        {
            return theoryName;
        }

        public Term FunctionsDecl()
        {
            if (config.generateFunctions)
                return QualifyAccessTerm(isaProgramRepr.GlobalProgramRepr.funcsDeclDef);

            return parent.FunctionsDecl();
        }

        public Term AxiomsDecl()
        {
            if (config.generateAxioms)
                return QualifyAccessTerm(isaProgramRepr.GlobalProgramRepr.axiomsDeclDef);

            return parent.AxiomsDecl();
        }

        public Term ProcDecl()
        {
            return QualifyAccessTerm(isaProgramRepr.procDeclDef);
        }

        public string ProcDeclName()
        {
            return QualifyAccessName(isaProgramRepr.procDeclDef);
        }

        public Term PreconditionsDecl()
        {
            if (config.specsConfig != SpecsConfig.None)
                return QualifyAccessTerm(isaProgramRepr.preconditionsDeclDef);

            return parent.PreconditionsDecl();
        }

        public string PreconditionsDeclName()
        {
            if (config.specsConfig != SpecsConfig.None)
                return QualifyAccessName(isaProgramRepr.preconditionsDeclDef);

            return parent.PreconditionsDeclName();
        }

        public Term PostconditionsDecl()
        {
            if (config.specsConfig != SpecsConfig.None)
                return QualifyAccessTerm(isaProgramRepr.postconditionsDeclDef);

            return parent.PostconditionsDecl();
        }

        public string PostconditionsDeclName()
        {
            if (config.specsConfig != SpecsConfig.None)
                return QualifyAccessName(isaProgramRepr.postconditionsDeclDef);

            return parent.PostconditionsDeclName();
        }

        public Term CfgDecl()
        {
            return QualifyAccessTerm(isaProgramRepr.cfgDeclDef);
        }
        
        public string CfgDeclName()
        {
            return QualifyAccessName(isaProgramRepr.cfgDeclDef);
        }

        public Term ParamsAndLocalsDecl()
        {
            return paramsAndLocalsList;
        }

        public string ParamsDecl()
        {
            return parameters;
        }

        public string LocalsDecl()
        {
            return locals;
        }

        public Term ConstsAndGlobalsDecl()
        {
            return constsAndGlobalsList;
        }

        public string ConstsDecl()
        {
            return consts;
        }

        public string UniqueConstsDecl()
        { 
          return uniqueConsts;
        }

        public string GlobalsDecl()
        {
            return globals;
        }

        public BoogieVariableTranslation VariableTranslation()
        {
            return factory.CreateTranslation();
        }

        public string MembershipLemma(Declaration d)
        {
            if (d is Variable && membershipLemmas.TryGetValue(d, out var result))
                return QualifyAccessName(result.Name);

            if (d is Function && config.generateFunctions)
                return QualifyAccessName(membershipLemmas[d].Name);

            if (d is Axiom && config.generateAxioms)
                return QualifyAccessName(membershipLemmas[d].Name);

            return parent.MembershipLemma(d);
        }

        public string ConstantMembershipLemma(Variable c)
        {
            if (constantMembershipLemmas.TryGetValue(c, out var result))
                return QualifyAccessName(result.Name);

            return parent.ConstantMembershipLemma(c);
        }

        public IsaBlockInfo BlockInfo()
        {
            return isaBlockInfo;
        }
        
        public IsaBigBlockInfo BigBlockInfo()
        {
          return isaBigBlockInfo;
        }

        public string LookupVarDeclLemma(Variable v)
        {
            //the proved lemma contains two statements, the second one is just for the type
            if (lookupVarTyLemmas.TryGetValue(v, out var result))
                return QualifyAccessName(result.Name+"(1)"); 

            return parent.LookupVarDeclLemma(v);
        }

        public string LookupVarTyLemma(Variable v)
        {
            //the proved lemma contains two statements, the first one is for the full declaration value
            if (lookupVarTyLemmas.TryGetValue(v, out var result))
                return QualifyAccessName(result.Name+"(2)"); 

            return parent.LookupVarTyLemma(v);
        }

        public Term VarContext()
        {
            return new TermTuple(constsAndGlobalsList, paramsAndLocalsList);
        }

        public string GlobalsLocalsDisjointLemma()
        {
            return QualifyAccessName(globalsLocalsDisjName);
        }

        public string GlobalsAtMostMax()
        {
            if (config.generateGlobalsAndConstants)
                return QualifyAccessName(globalsMaxName);
            return parent.GlobalsAtMostMax();
        }

        public string LocalsAtLeastMin()
        {
            if (config.generateParamsAndLocals)
            {
                return QualifyAccessName(localsMinName);
            }

            return parent.LocalsAtLeastMin();
        }

        public string VarContextWfTyLemma()
        {
            if(config.generateVarContextWfLemma)
                return QualifyAccessName(varContextWfName);
            else if (CreatesNewVarContext())
                throw new ProofGenUnexpectedStateException("do not have var context well-formedness lemma");
            else
                return parent.VarContextWfTyLemma();
        }

        public string FuncsWfTyLemma()
        {
            if (config.generateFunctions)
                return QualifyAccessName(funcsWfName);

            return parent.FuncsWfTyLemma();
        }

        private Term QualifyAccessTerm(string name)
        {
            return IsaCommonTerms.TermIdentFromName(QualifyAccessName(name));
        }

        private string QualifyAccessName(string name)
        {
            return theoryName + "." + name;
        }

        public IEnumerable<OuterDecl> OuterDecls()
        {
            var result = new List<OuterDecl>();
            result.AddRange(helperLemmas);
            result.AddRange(constantMembershipLemmas.Values);
            result.AddRange(membershipLemmas.Values);
            result.AddRange(lookupVarTyLemmas.Values);
            return result;
        }

        public void AddFunctionMembershipLemmas(IEnumerable<Function> functions, IsaUniqueNamer uniqueNamer)
        {
            AddNamedDeclsMembershipLemmas(functions,
                IsaCommonTerms.TermIdentFromName(isaProgramRepr.GlobalProgramRepr.funcsDeclDef),
                new[] {isaProgramRepr.GlobalProgramRepr.funcsDeclDef+ "_def"},
                d => new StringConst(uniqueNamer.RemoveApostropheInFunc(d.Name)),
                d => IsaBoogieTerm.FunDecl((Function) d, factory, uniqueNamer, false),
                false
            );
        }

        public void AddVariableMembershipLemmas(IEnumerable<Variable> variables, VarKind varKind)
        {
            var varTranslation = factory.CreateTranslation().VarTranslation;
            Func<NamedDeclaration, Term> idOfVar =
                d =>
                {
                    if (varTranslation.TryTranslateVariableId((Variable) d, out var varId, out var isBoundVar) &&
                        !isBoundVar)
                        return varId;
                    throw new ProofGenUnexpectedStateException(typeof(EndToEndVCProof),
                        "Could not retrieve variable id");
                };

            Func<Variable, string> membershipLemmaLookup;
            if (((varKind == VarKind.Constant || varKind == VarKind.Global) && config.generateGlobalsAndConstants) ||
                (varKind == VarKind.ParamOrLocal && config.generateParamsAndLocals) )
            {
                if (varKind == VarKind.Constant)
                    AddNamedDeclsMembershipLemmas(variables,
                        IsaCommonTerms.TermIdentFromName(consts),
                        new[] {consts + "_def"},
                        idOfVar,
                        d => IsaBoogieTerm.VarDeclWithoutName((Variable) d, typeIsaVisitor, basicCmdIsaVisitor.Translate),
                        true);

                string[] defs;
                if (varKind == VarKind.Constant)
                    defs = Array.Empty<string>();
                else
                    defs = varKind == VarKind.Global ? constsAndGlobalsDefs : paramsAndLocalsDefs;

                AddNamedDeclsMembershipLemmas(variables,
                    varKind == VarKind.Constant || varKind == VarKind.Global
                        ? constsAndGlobalsList
                        : paramsAndLocalsList,
                    defs,
                    idOfVar,
                    d => IsaBoogieTerm.VarDeclWithoutName((Variable) d, typeIsaVisitor, basicCmdIsaVisitor.Translate),
                    false);
                membershipLemmaLookup = v => membershipLemmas[v].Name;
            }
            else
            {
                membershipLemmaLookup = v => parent.MembershipLemma(v);
            }

            if (CreatesNewVarContext())
            {
                 //must come after adding membership lemmas (lemmas are looked up)
                 AddLookupVarDeclTyLemmas(variables,
                     idOfVar,
                     d => IsaBoogieTerm.VarDeclTuple((Variable) d, typeIsaVisitor, basicCmdIsaVisitor.Translate),
                     membershipLemmaLookup
                 );
            }
        }

        private string MembershipLemmaPrefix(NamedDeclaration d)
        {
          if (d is Function)
          {
            return "mfun";
          }
          else
          {
            return "mvar";
          }
        }

        private void AddNamedDeclsMembershipLemmas(
            IEnumerable<NamedDeclaration> decls,
            Term sourceList,
            string[] definitions,
            Func<NamedDeclaration, Term> nameOf,
            Func<NamedDeclaration, Term> declOf,
            bool separateConstantLemmas)
        {
            foreach (var d in decls)
            {
                var nameOfDecl = nameOf(d);
                Term lhs = new TermApp(IsaCommonTerms.TermIdentFromName("map_of"), new List<Term> {sourceList, nameOfDecl});
                var rhs = IsaCommonTerms.SomeOption(declOf(d));

                Term statement = TermBinary.Eq(lhs, rhs);
                Proof proof;
                //TODO: get rid of hack of checking whether defs are empty to know whether the already existing constant lookup should be used
                if (definitions.Any())
                    proof = new Proof(new List<string> {"by " + ProofUtil.Simp(definitions)});
                else
                    proof = new Proof(new List<string>
                        {"by " + "(simp add: " + ConstantMembershipName(d, nameOfDecl, separateConstantMembershipLemmaPrefix) + " del: Nat.One_nat_def)"});

                if (!separateConstantLemmas)
                    membershipLemmas.Add(d, new LemmaDecl(MembershipName(d, nameOfDecl, MembershipLemmaPrefix(d)), statement, proof));
                else
                    constantMembershipLemmas.Add(d, new LemmaDecl(ConstantMembershipName(d, nameOfDecl, separateConstantMembershipLemmaPrefix), statement, proof));
            }
        }

        private void AddLookupVarDeclTyLemmas(
            IEnumerable<Variable> vars,
            Func<NamedDeclaration, Term> nameOf,
            Func<NamedDeclaration, Tuple<Term,Term>> declOf,
            Func<Variable, string> getMembershipLemma)
        {
            foreach (var v in vars)
            {
                var nameOfDecl = nameOf(v);
                var (ty, whereClause) = declOf(v);
                var lookupDeclLhs = IsaBoogieTerm.LookupVarDecl(VarContext(), nameOfDecl);
                var lookupDeclRhs = IsaCommonTerms.SomeOption(new TermTuple(ty, whereClause));
                Term lookupDeclStmt = TermBinary.Eq(lookupDeclLhs, lookupDeclRhs);
                
                var lookupTyLhs = IsaBoogieTerm.LookupVarTy(VarContext(), nameOfDecl);
                var lookupTyRhs = IsaCommonTerms.SomeOption(ty);
                Term lookupTyStmt = TermBinary.Eq(lookupTyLhs, lookupTyRhs);
                
                var proof =
                    new Proof(new List<string>
                    {
                        "using " + globalsLocalsDisjName + " " + getMembershipLemma(v),
                        "by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)"
                    });
                lookupVarTyLemmas.Add(v, new LemmaDecl(
                    MembershipName(() => lookupVarTyNamer.GetName(v, "l_" + v.Name), "lvar", nameOfDecl),
                    new List<Term> {lookupDeclStmt, lookupTyStmt},
                    proof)
                );
            }
        }

        public void AddAxiomMembershipLemmas(IEnumerable<Axiom> axioms)
        {
            var axiomSet = IsaCommonTerms.SetOfList(IsaCommonTerms.TermIdentFromName(isaProgramRepr.GlobalProgramRepr.axiomsDeclDef));
            var id = 0;
            foreach (var axiom in axioms)
            {
                var axiomTerm = basicCmdIsaVisitor.Translate(axiom.Expr);
                var elemAssm = IsaCommonTerms.Elem(axiomTerm, axiomSet);

                var proof = new Proof(new List<string> {"by (simp add: " + isaProgramRepr.GlobalProgramRepr.axiomsDeclDef+ "_def)"});
                membershipLemmas.Add(axiom, new LemmaDecl(MembershipName(axiom, id), elemAssm, proof));
                id++;
            }
        }
        
        private string MembershipName(Func<string> normalNameFunc, string membershipPrefix, Term memberTerm)
        {
          if (CommandLineOptions.Clo.UseIdBasedLemmaNaming && memberTerm is NatConst natConst)
          {
            return membershipPrefix + natConst;
          }

          return membershipPrefix + normalNameFunc();
        }

        private string MembershipName(NamedDeclaration d, Term memberTerm, String membershipPrefix)
        {
          var normalNameFunc = () => membershipNamer.GetName(d, d.Name);

          return MembershipName(normalNameFunc, membershipPrefix, memberTerm);
        }

        private string ConstantMembershipName(NamedDeclaration d, Term constId, String membershipPrefix)
        {
            var normalNameFunc = () => membershipNamer.GetName(d, d.Name);
            return MembershipName(normalNameFunc, membershipPrefix, constId);
        }

        private string MembershipName(Axiom a, int id)
        {
            return "ma_" + id;
        }

        private void AddMinOrMaxLemma(bool isGlobal, int bound, Term varNames)
        {
            var xId = new SimpleIdentifier("x");
            var x = new TermIdent(xId);
            var boundHelperLemma =
                new LemmaDecl((isGlobal ? globalsMaxName : localsMinName) + "_aux",
                    TermBinary.Implies(
                        TermBinary.Neq(varNames, IsaCommonTerms.EmptyList),
                        isGlobal
                            ? TermBinary.Le(IsaCommonTerms.SetMax(IsaCommonTerms.SetOfList(varNames)),
                                new NatConst(bound))
                            : TermBinary.Ge(IsaCommonTerms.SetMin(IsaCommonTerms.SetOfList(varNames)),
                                new NatConst(bound))
                    ),
                    new Proof(new List<string>
                    {
                        "unfolding " + (isGlobal ? ConstsDecl() : ParamsDecl()) + "_def " +
                        (isGlobal ? GlobalsDecl() : LocalsDecl()) + "_def",
                        "by simp"
                    })
                );
            helperLemmas.Add(boundHelperLemma);

            var boundLemma =
                new LemmaDecl(isGlobal ? globalsMaxName : localsMinName,
                    TermQuantifier.ForAll(
                        new List<Identifier> {xId},
                        null,
                        TermBinary.Implies(
                            IsaCommonTerms.Elem(x, IsaCommonTerms.SetOfList(varNames)),
                            new TermBinary(x, new NatConst(bound),
                                isGlobal ? TermBinary.BinaryOpCode.Le : TermBinary.BinaryOpCode.Ge)
                        )
                    ),
                    new Proof(new List<string>
                    {
                        "using " + boundHelperLemma.Name + (isGlobal ? " helper_max" : " helper_min"),
                        "by blast"
                    })
                );

            helperLemmas.Add(boundLemma);
        }
        private void AddDisjointnessLemmas(int globalsMax, int localsMin)
        {
            var globalNames = VariableNames(constsAndGlobalsList);
            var localNames = VariableNames(paramsAndLocalsList);

            if (config.generateGlobalsAndConstants) AddMinOrMaxLemma(true, globalsMax, globalNames);

            AddMinOrMaxLemma(false, localsMin, localNames);

            Term statement = TermBinary.Eq(
                IsaCommonTerms.SetInter(IsaCommonTerms.SetOfList(globalNames), IsaCommonTerms.SetOfList(localNames)),
                IsaCommonTerms.EmptySet
            );

            List<string> proofMethods;
            if (globalsMax == localsMin)
                //-> global set is empty
                proofMethods = new List<string>
                {
                    "unfolding " + ConstsDecl() + "_def " + GlobalsDecl() + "_def",
                    "by simp"
                };
            else
                proofMethods = new List<string>
                {
                    "using " + ProofUtil.OF("max_min_disjoint_2", GlobalsAtMostMax(), LocalsAtLeastMin()),
                    "by linarith"
                };
            helperLemmas.Add(
                new LemmaDecl(globalsLocalsDisjName, statement, new Proof(proofMethods))
            );
        }

        private void AddWellFormednessLemmas()
        {
            LemmaDecl WfLemma(string lemmaName, string listDef, Term fun, Term destruct)
            {
                Term wfStmt = new TermApp(IsaCommonTerms.ListAll(
                    IsaCommonTerms.Composition(fun, destruct), IsaCommonTerms.TermIdentFromName(listDef)
                    ));
                return new LemmaDecl(lemmaName, 
                    ContextElem.CreateEmptyContext(), 
                    wfStmt, 
                    new Proof(new List<string> {"unfolding " + listDef + "_def", "by simp"}));
            }

            LemmaDecl WfSnd(string lemmaName, string listDef, Term fun) => WfLemma(lemmaName, listDef, fun, IsaCommonTerms.SndId);

            LemmaDecl WfFstSnd(string lemmaName, string listDef, Term fun) =>
                    WfLemma(lemmaName, listDef, fun, IsaCommonTerms.Composition(IsaCommonTerms.FstId, IsaCommonTerms.SndId));
            
            if (config.generateFunctions)
            {
                helperLemmas.Add(WfSnd(funcsWfName, isaProgramRepr.GlobalProgramRepr.funcsDeclDef,
                    IsaCommonTerms.TermIdentFromName("wf_fdecl")));
            }
            
            Term wfTy0 = new TermApp(IsaCommonTerms.TermIdentFromName("wf_ty"), new NatConst(0));

            if (config.generateVarContextWfLemma)
            {
                //TODO: could share wf lemmas with ancestors in certain cases
                helperLemmas.Add(WfFstSnd(constsWfName, ConstsDecl(), wfTy0));
                helperLemmas.Add(WfFstSnd(globalsWfName, GlobalsDecl(), wfTy0));
                helperLemmas.Add(WfFstSnd(paramsWfName, ParamsDecl(), wfTy0));
                helperLemmas.Add(WfFstSnd(localsWfName, LocalsDecl(), wfTy0));
                
                var xId = new SimpleIdentifier("x");
                var tauId = new SimpleIdentifier("\\<tau>");

                Term tauTerm = new TermIdent(tauId);
                Term xTerm = new TermIdent(xId);
                Term varContextWfStmt = TermQuantifier.ForAll(
                    new List<Identifier> {xId, tauId},
                    null,
                    TermBinary.Implies(
                        TermBinary.Eq(
                            new TermApp(
                                IsaCommonTerms.TermIdentFromName("lookup_var_ty"),
                                new TermTuple(new List<Term> {constsAndGlobalsList, paramsAndLocalsList}), xTerm),
                            IsaCommonTerms.SomeOption(tauTerm)
                        ),
                        new TermApp(wfTy0, tauTerm)
                    ));

                var varContextWf =
                    new LemmaDecl(
                        varContextWfName,
                        ContextElem.CreateEmptyContext(),
                        varContextWfStmt,
                        new Proof(
                            new List<string>
                            {
                                ProofUtil.Apply("rule lookup_ty_pred_2"),
                                ProofUtil.By(ProofUtil.SimpAll(constsWfName, globalsWfName, paramsWfName, localsWfName))
                            }));
                helperLemmas.Add(varContextWf);
            }
        }

        private bool CreatesNewVarContext()
        {
            return (config.generateGlobalsAndConstants || config.generateParamsAndLocals) && containsLocalInformation;
        }

        private Term VariableNames(Term variableDeclarations)
        {
            return IsaCommonTerms.Map(IsaCommonTerms.FstId, variableDeclarations);
        }
    }
}