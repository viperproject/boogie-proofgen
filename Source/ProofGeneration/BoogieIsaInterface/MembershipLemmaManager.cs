﻿using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;
using ProofGeneration.ProgramToVCProof;
using ProofGeneration.Util;

namespace ProofGeneration.BoogieIsaInterface
{
    public enum VarKind
    {
        Constant, Global, ParamOrLocal
    }
    
    public class MembershipLemmaManager : IProgramAccessor
    {
        //defer calls to parent, which are not handled here
        private readonly IProgramAccessor parent;

        private readonly IVariableTranslationFactory factory;
        private readonly TypeIsaVisitor typeIsaVisitor;
        private readonly IsaProgramRepr isaProgramRepr;
        private readonly BasicCmdIsaVisitor basicCmdIsaVisitor;

        private readonly string theoryName;

        private readonly IDictionary<Declaration, LemmaDecl> membershipLemmas = new Dictionary<Declaration, LemmaDecl>();
        // constants without globals membership
        private readonly IDictionary<Declaration, LemmaDecl> constantMembershipLemmas = new Dictionary<Declaration, LemmaDecl>();
        private readonly IDictionary<Variable, LemmaDecl> lookupVarTyLemmas = new Dictionary<Variable, LemmaDecl>();
        private readonly List<LemmaDecl> helperLemmas = new List<LemmaDecl>();
        
        private readonly string[] paramsAndLocalsDefs;
        private readonly string[] constsAndGlobalsDefs;

        private readonly string consts;
        private readonly string globals;
        private readonly string parameters;
        private readonly string locals;

        private readonly Term paramsAndLocalsList;
        private readonly Term constsAndGlobalsList;
        
        private readonly IsaUniqueNamer membershipNamer = new IsaUniqueNamer();
        private readonly IsaUniqueNamer lookupVarTyNamer = new IsaUniqueNamer();

        private readonly string localsMinName = "locals_min";
        private readonly string globalsMaxName = "globals_max";
        
        private readonly string globalsLocalsDisjName = "globals_locals_disj";
        private readonly string funcsWfName = "funcs_wf";
        private readonly string constsWfName = "consts_wf";
        private readonly string globalsWfName = "globals_wf";
        private readonly string paramsWfName = "params_wf";
        private readonly string localsWfName = "locals_wf";
        private readonly string varContextWfName = "var_context_wf";

        private readonly IsaProgramGeneratorConfig config;
        private readonly IsaBlockInfo isaBlockInfo;
        
        public MembershipLemmaManager(
            IsaProgramGeneratorConfig config,
            IsaProgramRepr isaProgramRepr,
            IsaBlockInfo isaBlockInfo,
            Tuple<int, int> GlobalsMaxLocalsMin,
            IVariableTranslationFactory factory,
            string theoryName
        )
        {
            this.parent = config.ParentAccessor;
            this.isaProgramRepr = isaProgramRepr;
            this.factory = factory;
            this.theoryName = theoryName;
            this.config = config;
            this.isaBlockInfo = isaBlockInfo;
            typeIsaVisitor = new TypeIsaVisitor(factory.CreateTranslation().TypeVarTranslation);
            basicCmdIsaVisitor = new BasicCmdIsaVisitor(factory);
            paramsAndLocalsDefs =
                new string[] {isaProgramRepr.paramsDeclDef + "_def", isaProgramRepr.localVarsDeclDef + "_def"};

            parameters = config.GenerateParamsAndLocals
                ? QualifyAccessName(isaProgramRepr.paramsDeclDef)
                : parent.ParamsDecl();
            locals = config.GenerateParamsAndLocals
                ? QualifyAccessName(isaProgramRepr.localVarsDeclDef)
                : parent.LocalsDecl();
            paramsAndLocalsList =
                IsaCommonTerms.AppendList(IsaCommonTerms.TermIdentFromName(parameters),
                                        IsaCommonTerms.TermIdentFromName(locals));
            
            consts = config.GenerateGlobalsAndConstants ? QualifyAccessName(isaProgramRepr.constantsDeclDef) : parent.ConstsDecl();
            globals = config.GenerateGlobalsAndConstants ? QualifyAccessName(isaProgramRepr.globalsDeclDef) : parent.GlobalsDecl(); 
            
            constsAndGlobalsDefs =
                new string[] {consts+ "_def", globals+ "_def"};
            constsAndGlobalsList =
                IsaCommonTerms.AppendList(IsaCommonTerms.TermIdentFromName(consts),
                    IsaCommonTerms.TermIdentFromName(globals));
            AddDisjointnessLemmas(GlobalsMaxLocalsMin.Item1, GlobalsMaxLocalsMin.Item2);
            if (config.GenerateFunctions)
            {
                AddTypingHelperLemmas();
            }
        }
        
        public string TheoryName()
        {
            return theoryName;
        }

        public Term FunctionsDecl()
        {
            if (config.GenerateFunctions)
                return QualifyAccessTerm(isaProgramRepr.funcsDeclDef);
                
            return parent.FunctionsDecl();
        }

        public Term AxiomsDecl()
        {
            if (config.GenerateAxioms)
                return QualifyAccessTerm(isaProgramRepr.axiomsDeclDef);
                
            return parent.AxiomsDecl();
        }

        public Term PreconditionsDecl()
        {
            if (config.GenerateSpecs)
                return QualifyAccessTerm(isaProgramRepr.preconditionsDeclDef);

            return parent.PreconditionsDecl();
        }

        public string PreconditionsDeclName()
        {
            if (config.GenerateSpecs)
                return QualifyAccessName(isaProgramRepr.preconditionsDeclDef);

            return parent.PreconditionsDeclName();
        }

        public Term PostconditionsDecl()
        {
            if (config.GenerateSpecs)
                return QualifyAccessTerm(isaProgramRepr.postconditionsDeclDef);

            return parent.PostconditionsDecl();
        }

        public string PostconditionsDeclName()
        {
            if (config.GenerateSpecs)
                return QualifyAccessName(isaProgramRepr.postconditionsDeclDef);

            return parent.PostconditionsDeclName();
        }
        
        public Term CfgDecl()
        {
            return QualifyAccessTerm(isaProgramRepr.cfgDeclDef);
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

        public string GlobalsDecl()
        {
            return globals;
        }
        
        private Term QualifyAccessTerm(string name)
        {
            return IsaCommonTerms.TermIdentFromName(QualifyAccessName(name));
        }

        private string QualifyAccessName(string name)
        {
            return theoryName + "." + name;
        }
        public string MembershipLemma(Declaration d)
        {
            /* for variables we don't have a fine-grained distinction (which would require knowing whether the variable is
             * global or not) --> TODO use subtype to distinguish */
            if (d is Variable && membershipLemmas.TryGetValue(d, out LemmaDecl result))
                return QualifyAccessName(result.name);
            
            if (d is Function && config.GenerateFunctions)
                return QualifyAccessName(membershipLemmas[d].name);

            if (d is Axiom && config.GenerateAxioms)
                return QualifyAccessName(membershipLemmas[d].name);
                
            return parent.MembershipLemma(d);
        }

        public string ConstantMembershipLemma(Variable c)
        {
            if (constantMembershipLemmas.TryGetValue(c, out LemmaDecl result))
                return QualifyAccessName(result.name);

            return parent.ConstantMembershipLemma(c);
        }

        public IsaBlockInfo BlockInfo()
        {
            return isaBlockInfo;
        }

        public string LookupVarTyLemma(Variable v)
        {
            if (lookupVarTyLemmas.TryGetValue(v, out LemmaDecl result))
                return QualifyAccessName(result.name);

            return parent.LookupVarTyLemma(v);
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

        public void AddFunctionMembershipLemmas(IEnumerable<Function> functions)
        {
            AddNamedDeclsMembershipLemmas(functions,
                IsaCommonTerms.TermIdentFromName(isaProgramRepr.funcsDeclDef),
                new[] { isaProgramRepr.funcsDeclDef + "_def" },
                d => new StringConst(d.Name),
                d => IsaBoogieTerm.FunDecl((Function)d, factory, false),
                true,
                false
                );
        }

        public void AddVariableMembershipLemmas(IEnumerable<Variable> variables, VarKind varKind, bool generateMembershipLemmas)
        {
            var varTranslation = factory.CreateTranslation().VarTranslation;
            Func<NamedDeclaration, Term> idOfVar =
                d =>
                {
                    if (varTranslation.TryTranslateVariableId((Variable) d, out Term varId, out bool isBoundVar) &&
                        !isBoundVar)
                    {
                        return varId;
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException(typeof(EndToEndVCProof),
                            "Could not retrieve variable id");
                    }
                };

            Func<Variable, string> membershipLemmaLookup;
            if (generateMembershipLemmas)
            {
                if (varKind == VarKind.Constant)
                {
                    AddNamedDeclsMembershipLemmas(variables,
                        IsaCommonTerms.TermIdentFromName(consts),
                        new String[] {consts + "_def"},
                        idOfVar,
                        d => IsaBoogieTerm.VarDecl((Variable) d, typeIsaVisitor, false),
                        true,
                        true);
                }

                string[] defs;
                if (varKind == VarKind.Constant)
                {
                    defs = Array.Empty<string>();
                }
                else
                {
                    defs = (varKind == VarKind.Global ? constsAndGlobalsDefs : paramsAndLocalsDefs);
                }

                AddNamedDeclsMembershipLemmas(variables,
                    (varKind == VarKind.Constant || varKind == VarKind.Global) ? constsAndGlobalsList : paramsAndLocalsList,
                    defs,
                    idOfVar,
                    d => IsaBoogieTerm.VarDecl((Variable) d, typeIsaVisitor, false),
                    true,
                    false);
                membershipLemmaLookup = v => membershipLemmas[v].name;
            }
            else
            {
                membershipLemmaLookup = v => parent.MembershipLemma(v);
            }

            //must come after adding membership lemmas (lemmas are looked up)
            AddLookupVarTyLemmas(variables, 
                idOfVar, 
                d => IsaBoogieTerm.VarDecl((Variable) d, typeIsaVisitor, false),
                membershipLemmaLookup
                );
        }

        private void AddNamedDeclsMembershipLemmas(
            IEnumerable<NamedDeclaration> decls,
            Term sourceList,
            string [] definitions,
            Func<NamedDeclaration, Term> nameOf,
            Func<NamedDeclaration, Term> declOf,
            bool useMapOf,
            bool separateConstantLemmas)
        {
            foreach (var d in decls)
            {
                Term lhs = new TermApp(
                    useMapOf ? IsaCommonTerms.TermIdentFromName("map_of") : IsaCommonTerms.TermIdentFromName("nth"),
                    new List<Term> { sourceList, nameOf(d) });
                Term rhs = useMapOf ? IsaCommonTerms.SomeOption(declOf(d)) : declOf(d);

                Term statement = TermBinary.Eq(lhs, rhs);
                Proof proof; 
                //TODO: get rid of hack of checking whether defs are empty to know whether the already existing constant lookup should be used
                if (definitions.Any())
                    proof = new Proof(new List<string> { "by " + ProofUtil.Simp(definitions) });
                else
                    proof = new Proof(new List<string> { "by " + "(simp add: " + ConstantMembershipName(d) + " del: Nat.One_nat_def)" });
                
                if (!separateConstantLemmas)
                {
                    membershipLemmas.Add(d, new LemmaDecl(MembershipName(d), statement, proof));
                }
                else
                {
                    constantMembershipLemmas.Add(d, new LemmaDecl(ConstantMembershipName(d), statement, proof));
                }
            }
        }

        private void AddLookupVarTyLemmas(
            IEnumerable<Variable> vars, 
            Func<NamedDeclaration, Term> nameOf,
            Func<NamedDeclaration, Term> declOf,
            Func<Variable, string> getMembershipLemma)
        {
            foreach (var v in vars)
            {
                Term lhs = IsaBoogieTerm.LookupVarTy(VarContext(), nameOf(v));
                Term rhs = IsaCommonTerms.SomeOption(declOf(v));
                Term statement = TermBinary.Eq(lhs, rhs);
                Proof proof =
                    new Proof(new List<string>
                    {
                        "using " + globalsLocalsDisjName + " " + getMembershipLemma(v),
                        "by (simp add: lookup_var_ty_global_2 lookup_var_ty_local)"
                    });
                lookupVarTyLemmas.Add(v, new LemmaDecl(lookupVarTyNamer.GetName(v, "l_"+v.Name), statement, proof));
            }
        }

        public Term VarContext()
        {
            return new TermTuple(constsAndGlobalsList, paramsAndLocalsList);
        }
        
        public void AddAxiomMembershipLemmas(IEnumerable<Axiom> axioms)
        {
            Term axiomSet = IsaCommonTerms.SetOfList(IsaCommonTerms.TermIdentFromName(isaProgramRepr.axiomsDeclDef));
            int id = 0;
            foreach (var axiom in axioms)
            {
                Term axiomTerm = basicCmdIsaVisitor.Translate(axiom.Expr);
                Term elemAssm = IsaCommonTerms.Elem(axiomTerm, axiomSet);

                Proof proof = new Proof(new List<string> { "by (simp add: " + isaProgramRepr.axiomsDeclDef + "_def)" });
                membershipLemmas.Add(axiom, new LemmaDecl(MembershipName(axiom, id), elemAssm, proof));
                id++;
            }
        }
        
        private string MembershipName(NamedDeclaration d)
        {
            var name = membershipNamer.GetName(d, d.Name);
            if(d is Function)
            {
                return "mfun_" + name;
            } else
            {
                return "m_" + name;
            }
        }

        private string ConstantMembershipName(NamedDeclaration d)
        {
            var name = membershipNamer.GetName(d, d.Name);
            return "mconst_" + name;
        }

        private string MembershipName(Axiom a, int id)
        {
            return "ma_" + id;
        }

        public string GlobalsLocalsDisjointLemma()
        {
            return QualifyAccessName(globalsLocalsDisjName);
        }

        public string GlobalsAtMostMax()
        {
            if (config.GenerateGlobalsAndConstants)
                return QualifyAccessName(globalsMaxName);
            return parent.GlobalsAtMostMax();
        }
        
        public string LocalsAtLeastMin()
        {
            return QualifyAccessName(localsMinName);
        }

        private void AddMinOrMaxLemma(bool isGlobal, int bound, Term varNames)
        {
            var xId = new SimpleIdentifier("x");
            var x = new TermIdent(xId);
            var boundHelperLemma = 
                new LemmaDecl((isGlobal ? globalsMaxName : localsMinName) + "_aux",
                    TermBinary.Implies(
                       TermBinary.Neq(varNames, IsaCommonTerms.EmptyList),  
                       isGlobal ?
                           TermBinary.Le(IsaCommonTerms.SetMax(IsaCommonTerms.SetOfList(varNames)), new NatConst(bound)) :
                           TermBinary.Ge(IsaCommonTerms.SetMin(IsaCommonTerms.SetOfList(varNames)), new NatConst(bound))
                        ), 
                    new Proof(new List<string>
                    {
                        "unfolding " + (isGlobal ? ConstsDecl() : ParamsDecl())+"_def " + (isGlobal ? GlobalsDecl() : LocalsDecl())+"_def",
                        "by simp"
                    })
                    );
            helperLemmas.Add(boundHelperLemma);
            
            var boundLemma = 
                new LemmaDecl(isGlobal ? globalsMaxName : localsMinName,
                    TermQuantifier.ForAll(
                        new List<Identifier> { xId },
                        null,
                        TermBinary.Implies(
                            IsaCommonTerms.Elem(x, IsaCommonTerms.SetOfList(varNames)),
                            new TermBinary(x, new NatConst(bound), isGlobal ? TermBinary.BinaryOpCode.LE : TermBinary.BinaryOpCode.GE)
                            )
                        ),
                    new Proof(new List<string>
                    {
                        "using " + boundHelperLemma.name + (isGlobal ? " helper_max" : " helper_min"),
                        "by blast"
                    })
                    );
            
            helperLemmas.Add(boundLemma);
            
        }
        

        private void AddDisjointnessLemmas(int globalsMax, int localsMin)
        {
            var globalNames = VariableNames(constsAndGlobalsList);
            var localNames = VariableNames(paramsAndLocalsList);
            
            if (config.GenerateGlobalsAndConstants)
            {
                AddMinOrMaxLemma(true, globalsMax, globalNames);
            }
            
            AddMinOrMaxLemma(false, localsMin, localNames);

            Term statement = TermBinary.Eq(
                IsaCommonTerms.SetInter(IsaCommonTerms.SetOfList(globalNames), IsaCommonTerms.SetOfList(localNames)),
                IsaCommonTerms.EmptySet
            );

            List<string> proofMethods;
            if (globalsMax == localsMin)
            {
                //-> global set is empty
                proofMethods = new List<string>
                {
                    "unfolding " + ConstsDecl()+"_def " + GlobalsDecl() +"_def",
                    "by simp"
                };
            }
            else
            {
                proofMethods = new List<string>
                {
                    "using " + LocalsAtLeastMin() + " " + GlobalsAtMostMax(),
                    "by fastforce"
                };
            }
            helperLemmas.Add(
                new LemmaDecl(globalsLocalsDisjName, statement, new Proof(proofMethods))
            );
        }

        public string VarContextWfTyLemma()
        {
            return QualifyAccessName(varContextWfName);
        }

        public string FuncsWfTyLemma()
        {
            return QualifyAccessName(funcsWfName);
        }

        private void AddTypingHelperLemmas()
        {
            Func<string, string, Term, LemmaDecl> WfLemma = 
                (lemmaName, list_def, fun) =>
                {
                    Term wfStmt = 
                        new TermApp(IsaCommonTerms.ListAll(
                            IsaCommonTerms.Composition(fun, IsaCommonTerms.SndId), 
                            IsaCommonTerms.TermIdentFromName(list_def))
                        ); 
                    return 
                        new LemmaDecl(lemmaName, ContextElem.CreateEmptyContext(), wfStmt,
                            new Proof(new List<string>
                            {
                                "unfolding " + list_def + "_def",
                                "by simp"
                            })
                            );
                };
            //TODO: only works if all definitions are defined on the current level (not in a parent)
            helperLemmas.Add(WfLemma(funcsWfName, isaProgramRepr.funcsDeclDef, IsaCommonTerms.TermIdentFromName("wf_fdecl")));
            Term wfTy0 = new TermApp(IsaCommonTerms.TermIdentFromName("wf_ty"), new NatConst(0));
            
            
            helperLemmas.Add(WfLemma(constsWfName,  isaProgramRepr.constantsDeclDef, wfTy0));
            helperLemmas.Add(WfLemma(globalsWfName,  isaProgramRepr.globalsDeclDef, wfTy0));
            helperLemmas.Add(WfLemma(paramsWfName,  isaProgramRepr.paramsDeclDef, wfTy0));
            helperLemmas.Add(WfLemma(localsWfName,  isaProgramRepr.localVarsDeclDef, wfTy0));
            
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
            
            LemmaDecl varContextWf = 
                new LemmaDecl(
                    varContextWfName, 
                    ContextElem.CreateEmptyContext(), 
                    varContextWfStmt, 
                    new Proof(
                        new List<string>()
                        {
                            ProofUtil.Apply("rule lookup_ty_pred_2"),
                            ProofUtil.By(ProofUtil.SimpAll(constsWfName, globalsWfName, paramsWfName, localsWfName))
                        } ));
            helperLemmas.Add(varContextWf);
        }

        private Term VariableNames(Term variableDeclarations)
        {
            return IsaCommonTerms.Map(IsaCommonTerms.FstId, variableDeclarations);
        }

    }
}