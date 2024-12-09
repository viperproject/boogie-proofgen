using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.ProgramToVCProof;
using ProofGeneration.Util;

namespace ProofGeneration
{
    public static class IsaBoogieTerm
    {
        private static readonly TermIdent intVId = IsaCommonTerms.TermIdentFromName("IntV");
        private static readonly TermIdent boolVId = IsaCommonTerms.TermIdentFromName("BoolV");
        private static readonly TermIdent realVId = IsaCommonTerms.TermIdentFromName("RealV");
        private static readonly TermIdent intLitId = IsaCommonTerms.TermIdentFromName("LInt");
        private static readonly TermIdent boolLitId = IsaCommonTerms.TermIdentFromName("LBool");
        private static readonly TermIdent realLitId = IsaCommonTerms.TermIdentFromName("LReal");

        private static readonly TermIdent intToRealId = IsaCommonTerms.TermIdentFromName("IntToReal");
        
        private static readonly TermIdent varId = IsaCommonTerms.TermIdentFromName("Var");
        private static readonly TermIdent bvarId = IsaCommonTerms.TermIdentFromName("BVar");
        private static readonly TermIdent oldVarId = IsaCommonTerms.TermIdentFromName("Old");
        
        private static readonly TermIdent condExpId = IsaCommonTerms.TermIdentFromName("CondExp");

        private static readonly TermIdent lookupVarId = IsaCommonTerms.TermIdentFromName("lookup_var");
        private static readonly TermIdent lookupVarDeclId = IsaCommonTerms.TermIdentFromName("lookup_var_decl");
        private static readonly TermIdent lookupVarTyId = IsaCommonTerms.TermIdentFromName("lookup_var_ty");
        private static readonly TermIdent localStateId = IsaCommonTerms.TermIdentFromName("local_state");
        private static readonly TermIdent globalStateId = IsaCommonTerms.TermIdentFromName("global_state");
        private static readonly TermIdent oldGlobalStateId = IsaCommonTerms.TermIdentFromName("old_global_state");
        private static readonly TermIdent binderStateId = IsaCommonTerms.TermIdentFromName("binder_state");

        private static readonly TermIdent redCfgMultiId = IsaCommonTerms.TermIdentFromName("red_cfg_multi");
        private static readonly TermIdent redCfgKStepId = IsaCommonTerms.TermIdentFromName("red_cfg_k_step");
        private static readonly TermIdent redCmdListId = IsaCommonTerms.TermIdentFromName("red_cmd_list");
        private static readonly TermIdent redBigBlockId = IsaCommonTerms.TermIdentFromName("red_bigblock");
        private static readonly TermIdent redBigBlockKStepId = IsaCommonTerms.TermIdentFromName("red_bigblock_k_step");
        private static readonly TermIdent redBigBlockMultiId = IsaCommonTerms.TermIdentFromName("rtranclp");
        private static readonly TermIdent astValidConfigId = IsaCommonTerms.TermIdentFromName("Ast.valid_configuration");
        private static readonly TermIdent redExprId = IsaCommonTerms.TermIdentFromName("red_expr");
        private static readonly TermIdent normalStateId = IsaCommonTerms.TermIdentFromName("Normal");
        private static readonly TermIdent magicStateId = IsaCommonTerms.TermIdentFromName("Magic");
        private static readonly TermIdent failureStateId = IsaCommonTerms.TermIdentFromName("Failure");

        private static readonly TermIdent outEdgesId = IsaCommonTerms.TermIdentFromName("out_edges");
        private static readonly TermIdent nodeToBlockId = IsaCommonTerms.TermIdentFromName("node_to_block");
        private static readonly TermIdent funInterpWfId = IsaCommonTerms.TermIdentFromName("fun_interp_wf");
        
        private static readonly TermIdent astLoopIhId = IsaCommonTerms.TermIdentFromName("loop_IH");

        private static readonly TermIdent
            funInterpSingleWfId = IsaCommonTerms.TermIdentFromName("fun_interp_single_wf");

        private static readonly TermIdent stateWfId = IsaCommonTerms.TermIdentFromName("state_typ_wf");
        private static readonly TermIdent axiomsSatId = IsaCommonTerms.TermIdentFromName("axioms_sat");
        private static readonly TermIdent exprSatId = IsaCommonTerms.TermIdentFromName("expr_sat");
        private static readonly TermIdent exprAllSatId = IsaCommonTerms.TermIdentFromName("expr_all_sat");

        private static readonly TermIdent typeOfValId = IsaCommonTerms.TermIdentFromName("type_of_val");

        private static readonly TermIdent procCallId = IsaCommonTerms.TermIdentFromName("ProcCall");
        private static readonly TermIdent funCallId = IsaCommonTerms.TermIdentFromName("FunExp");
        
        private static readonly TermIdent forallId = IsaCommonTerms.TermIdentFromName("Forall");
        private static readonly TermIdent existsId = IsaCommonTerms.TermIdentFromName("Exists");
        private static readonly TermIdent forallTypeId = IsaCommonTerms.TermIdentFromName("ForallT");
        private static readonly TermIdent existsTypeId = IsaCommonTerms.TermIdentFromName("ExistsT");

        private static readonly TermIdent closedTypeId = IsaCommonTerms.TermIdentFromName("closed");
        private static readonly TermIdent instTypeId = IsaCommonTerms.TermIdentFromName("instantiate");

        private static readonly TermIdent axiomAssmId = IsaCommonTerms.TermIdentFromName("axiom_assm");

        private static readonly TermIdent nstateGlobRestrId =
            IsaCommonTerms.TermIdentFromName("nstate_global_restriction");

        public static TermIdent ConvertValToBoolId { get; } = IsaCommonTerms.TermIdentFromName("convert_val_to_bool");
        public static TermIdent ConvertValToIntId { get; } = IsaCommonTerms.TermIdentFromName("convert_val_to_int");
        public static TermIdent SematicsProcSpecSatisfied { get; } = IsaCommonTerms.TermIdentFromName("Semantics.proc_body_satisfies_spec");
        public static TermIdent ConvertValToRealId { get; } = IsaCommonTerms.TermIdentFromName("convert_val_to_real");

        //TODO initialize all the default constructors, so that they only need to be allocated once (Val, Var, etc...)

        public static Term ExprFromLiteral(Term lit)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Lit"), new List<Term> {lit});
        }

        public static Term Var(string v)
        {
            Term stringConst = new StringConst(v);
            return new TermApp(IsaCommonTerms.TermIdentFromName("Var"), new List<Term> {stringConst});
        }

        public static Term VariableConstr(int i, bool isBoundVar)
        {
            Contract.Requires(i >= 0);
            Term natConst = new NatConst(i);
            if (!isBoundVar)
                return new TermApp(varId, new List<Term> {natConst});

            return new TermApp(bvarId, new List<Term> {natConst});
        }

        public static Term BVar(int i)
        {
            Contract.Requires(i >= 0);
            Term natConst = new NatConst(i);
            return new TermApp(bvarId, natConst);
        }
        
        public static Term Old(Term body)
        {
            return new TermApp(oldVarId, body);
        }

        public static Term CondExp(Term cond, Term thn, Term els)
        {
          return new TermApp(condExpId, cond, thn, els);
        }

        public static Term Literal(LiteralExpr node)
        {
            if (node.Type.IsBool)
                return BoolLiteral(node.asBool);
            if (node.Type.IsInt)
                return IntLiteral(node.asBigNum);
            if (node.Type.IsReal)
                return RealLiteral(node.asBigDec);
            throw new NotImplementedException();
        }

        public static Term IntLiteral(BigNum num)
        {
            return new TermApp(intLitId, new IntConst(num));
        }

        public static Term IntValConstr()
        {
            return intVId;
        }

        public static Term IntVal(BigNum num)
        {
            Term intConst = new IntConst(num);
            return IntVal(intConst);
        }

        public static Term IntVal(Term i)
        {
            return new TermApp(intVId, new List<Term> {i});
        }

        public static Term BoolLiteral(bool b)
        {
            return new TermApp(boolLitId, new BoolConst(b));
        }

        public static Term BoolValConstr()
        {
            return boolVId;
        }

        public static Term BoolVal(bool b)
        {
            Term boolConst = new BoolConst(b);
            return BoolVal(boolConst);
        }

        public static Term BoolVal(Term b)
        {
            return new TermApp(boolVId, b);
        }
        
        public static Term RealLiteral(BigDec dec)
        {
            return new TermApp(realLitId, new RealConst(dec));
        }

        public static Term RealValConstr()
        {
            return realVId;
        }

        public static Term RealVal(BigDec num)
        {
            Term realConst = new RealConst(num);
            return RealVal(realConst);
        }

        public static Term RealVal(Term r)
        {
            return new TermApp(realVId, new List<Term> {r});
        }

        public static Term LookupVar(Term varContext, Term normalState, Term var)
        {
            return new TermApp(lookupVarId, new List<Term> {varContext, normalState, var});
        }
        
        public static Term LookupVarDecl(Term varContext, Term var)
        {
            return new TermApp(lookupVarDeclId, new List<Term> {varContext, var});
        }

        public static Term LookupVarTy(Term varContext, Term var)
        {
            return new TermApp(lookupVarTyId, new List<Term> {varContext, var});
        }

        public static Term LocalState(Term normalState)
        {
            return new TermApp(localStateId, normalState);
        }

        public static Term GlobalState(Term normalState)
        {
            return new TermApp(globalStateId, normalState);
        }

        public static Term OldGlobalState(Term normalState)
        {
            return new TermApp(oldGlobalStateId, normalState);
        }

        public static Term BinderState(Term normalState)
        {
            return new TermApp(binderStateId, normalState);
        }

        public static Term Assert(Term arg)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assert"), new List<Term> {arg});
        }

        public static Term Assume(Term arg)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assume"), new List<Term> {arg});
        }


        public static Term Assign(Term lhsTerm, Term rhsTerm)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assign"), new List<Term> {lhsTerm, rhsTerm});
        }

        public static Term Assign(IList<Term> lhsTerms, IList<Term> rhsTerms)
        {
            if (lhsTerms.Count != rhsTerms.Count)
                throw new ProofGenUnexpectedStateException(typeof(BasicCmdIsaVisitor),
                    "different number of lhs and rhs");

            IList<Term> results = new List<Term>();
            lhsTerms.ZipDo(rhsTerms, (lhs, rhs) => results.Add(new TermTuple(new List<Term> {lhs, rhs})));

            return new TermApp(IsaCommonTerms.TermIdentFromName("Assign"), new List<Term> {new TermList(results)});
        }

        public static Term Havoc(Term var)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Havoc"), new List<Term> {var});
        }

        public static Term Binop(BinaryOperator.Opcode opcode, Term arg1, Term arg2)
        {
            string bopIsa;

            switch (opcode)
            {
                case BinaryOperator.Opcode.Eq:
                    bopIsa = "Eq";
                    break;
                case BinaryOperator.Opcode.Neq:
                    bopIsa = "Neq";
                    break;
                case BinaryOperator.Opcode.Add:
                    bopIsa = "Add";
                    break;
                case BinaryOperator.Opcode.Sub:
                    bopIsa = "Sub";
                    break;
                case BinaryOperator.Opcode.Mul:
                    bopIsa = "Mul";
                    break;
                case BinaryOperator.Opcode.Div:
                    bopIsa = "Div";
                    break;
                case BinaryOperator.Opcode.RealDiv:
                    bopIsa = "RealDiv";
                    break;
                case BinaryOperator.Opcode.Mod:
                    bopIsa = "Mod";
                    break;
                case BinaryOperator.Opcode.Lt:
                    bopIsa = "Lt";
                    break;
                case BinaryOperator.Opcode.Le:
                    bopIsa = "Le";
                    break;
                case BinaryOperator.Opcode.Gt:
                    bopIsa = "Gt";
                    break;
                case BinaryOperator.Opcode.Ge:
                    bopIsa = "Ge";
                    break;
                case BinaryOperator.Opcode.And:
                    bopIsa = "And";
                    break;
                case BinaryOperator.Opcode.Or:
                    bopIsa = "Or";
                    break;
                case BinaryOperator.Opcode.Imp:
                    bopIsa = "Imp";
                    break;
                case BinaryOperator.Opcode.Iff:
                    bopIsa = "Iff";
                    break;
                default:
                    throw new NotImplementedException();
            }

            var list = new List<Term> {arg1, IsaCommonTerms.TermIdentFromName(bopIsa), arg2};
            return new TermApp(IsaCommonTerms.TermIdentFromName("BinOp"), list);
        }
        
        private static Term Unop(Term unop, Term arg)
        {
            var list = new List<Term> {unop, arg};
            return new TermApp(IsaCommonTerms.TermIdentFromName("UnOp"), list);
        }

        public static Term Unop(UnaryOperator.Opcode opcode, Term arg)
        {
          string uopIsa;

          switch (opcode)
          {
            case UnaryOperator.Opcode.Not:
              uopIsa = "Not";
              break;
            case UnaryOperator.Opcode.Neg:
              uopIsa = "UMinus";
              break;
            default:
              throw new NotImplementedException();
          }

          return Unop(IsaCommonTerms.TermIdentFromName(uopIsa), arg);
        }
        
        public static Term IntToReal(Term intTerm)
        {
          return Unop(intToRealId, intTerm);
        }
        
        //value quantification

        /*
         * if isForall is false, then it must be an existential quantifier
         * */
        public static Term Quantifier(bool isForall, Term boundVarType, Term body)
        {
            return isForall ? Forall(boundVarType, body) : Exists(boundVarType, body);
        }

        public static Term Forall(Term boundVarType, Term body)
        {
            return new TermApp(forallId, new List<Term> {boundVarType, body});
        }

        public static Term Exists(Term boundVarType, Term body)
        {
            return new TermApp(existsId, new List<Term> {boundVarType, body});
        }

        //type quantification

        public static Term TypeQuantifier(bool isForall, Term body)
        {
            return isForall ? ForallType(body) : ExistsType(body);
        }

        public static Term ForallType(Term body)
        {
            return new TermApp(forallTypeId, new List<Term> {body});
        }

        public static Term ExistsType(Term body)
        {
            return new TermApp(existsTypeId, new List<Term> {body});
        }

        public static Term FunCall(string fname, IList<Term> typeArgs, IList<Term> args)
        {
            var wrapTypeArgs = new TermList(typeArgs);
            var wrapArgs = new TermList(args);
            var fnameAndArgs = new List<Term> {new StringConst(fname), wrapTypeArgs, wrapArgs};

            return new TermApp(funCallId, fnameAndArgs);
        }

        public static Term ProcCall(string procname, IList<Term> args, IList<Term> returnVars)
        {
            return new TermApp(procCallId, new StringConst(procname), new TermList(args), new TermList(returnVars));
        }
        
        public static Term MethodASTBody(IList<Term> bigblocks)
        {
          return new TermList(bigblocks);
        }

        public static Term MethodCFGBody(Term entryNode, Term outEdges, Term nodeToBlock)
        {
            var mapping =
                new List<Tuple<string, Term>>
                {
                    Tuple.Create("entry", entryNode),
                    Tuple.Create("out_edges", outEdges),
                    Tuple.Create("node_to_block", nodeToBlock)
                };

            return new TermRecord(mapping);
        }

        public static Term OutEdges(Term cfg, int idx)
        {
            return IsaCommonTerms.ListLookup(new TermApp(outEdgesId, cfg), idx);
        }

        public static Term NodeToBlock(Term cfg, int idx)
        {
            return IsaCommonTerms.ListLookup(new TermApp(nodeToBlockId, cfg), idx);
        }

        public static Term Method(string methodName,
            int numTypeParams,
            Term parameters,
            Term localVars,
            Term modifiedVariables,
            Term pres,
            Term posts,
            Term methodCFGBody)
        {
            var elements =
                new List<Term>
                {
                    new StringConst(methodName),
                    new NatConst(numTypeParams),
                    parameters,
                    localVars,
                    modifiedVariables,
                    new TermTuple(new List<Term> {pres, posts}),
                    methodCFGBody
                };

            return new TermTuple(elements);
        }

        public static Term Program(Term fdecls, Term constantDecls, Term globalDecls, Term axioms, List<Term> mdecls)
        {
            Term mdeclsTerm = new TermList(mdecls);

            return new TermApp(IsaCommonTerms.TermIdentFromName("Program"),
                new List<Term>
                    {new TermList(new List<Term>()), fdecls, constantDecls, globalDecls, axioms, mdeclsTerm});
        }

        public static Term Normal(Term n_s)
        {
            return new TermApp(normalStateId, new List<Term> {n_s});
        }

        public static Term Magic()
        {
            return magicStateId;
        }

        public static Term Failure()
        {
            return failureStateId;
        }

        public static Term RedCmdList(BoogieContextIsa boogieContext, Term cmdList, Term initState, Term finalState)
        {
            return
                new TermApp(redCmdListId,
                    new List<Term>
                    {
                        boogieContext.absValTyMap,
                        boogieContext.methodContext,
                        boogieContext.varContext,
                        boogieContext.funContext,
                        boogieContext.rtypeEnv,
                        cmdList,
                        initState,
                        finalState
                    }
                );
        }
        
        public static Term RedBigBlock(BoogieContextIsa boogieContext, Term startConfig, Term endConfig, Term ast)
        {
          return
            new TermApp(redBigBlockId,
              new List<Term>
              {
                boogieContext.absValTyMap,
                boogieContext.methodContext,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                ast,
                startConfig,
                endConfig
              }
            );
        }
        
        public static Term RedBigBlockKStep(BoogieContextIsa boogieContext, Term startConfig, Term endConfig, Term ast, Term numSteps)
        {
          return
            new TermApp(redBigBlockKStepId,
              new List<Term>
              {
                boogieContext.absValTyMap,
                boogieContext.methodContext,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                ast,
                startConfig,
                numSteps,
                endConfig
              }
            );
        }
        
        public static Term RedBigBlockMulti(BoogieContextIsa boogieContext, Term startConfig, Term endConfig, Term ast)
        {
          IList<Term> bigblockContextList = new List<Term>
          {
            boogieContext.absValTyMap,
            boogieContext.methodContext,
            boogieContext.varContext,
            boogieContext.funContext,
            boogieContext.rtypeEnv,
            ast
          };
          Term redbigBlockTerm = new TermApp(redBigBlockId, bigblockContextList);

          return
            new TermApp(redBigBlockMultiId,
              new List<Term>
              {
                redbigBlockTerm,
                startConfig,
                endConfig
              }
            );
        }
        
        public static Term StartConfigTerm(BigBlock b, Term cont0, IProgramAccessor beforeCfgProgAccess, Term initState1)
        {
          var beforeBigblockDefName = beforeCfgProgAccess.BigBlockInfo().CmdsQualifiedName(b).First();
          Term beforeBigblock = IsaCommonTerms.TermIdentFromName(beforeBigblockDefName);

          IList<Term> startConfigArgs = new List<Term>();
          startConfigArgs.Add(beforeBigblock);
          startConfigArgs.Add(cont0);
          startConfigArgs.Add(initState1);
          
          return new TermTuple(startConfigArgs);
        }
        
        public static Term EndConfigTerm()
        {
          IList<Term> endConfigArgs = new List<Term>();
          endConfigArgs.Add(IsaCommonTerms.TermIdentFromName("reached_bb"));
          endConfigArgs.Add(IsaCommonTerms.TermIdentFromName("reached_cont"));
          endConfigArgs.Add(IsaCommonTerms.TermIdentFromName("reached_state"));
          
          return new TermTuple(endConfigArgs);
        }
        public static Term astId()
        {
          return IsaCommonTerms.TermIdentFromName("T");
        }
        
        public static Term AstValidConfiguration(BoogieContextIsa boogieContext, Term posts)
        {
          return
            new TermApp(astValidConfigId,
              new List<Term>
              {
                boogieContext.absValTyMap,
                boogieContext.varContext,
                boogieContext.funContext,
                boogieContext.rtypeEnv,
                posts,
                IsaCommonTerms.TermIdentFromName("reached_bb"),
                IsaCommonTerms.TermIdentFromName("reached_cont"),
                IsaCommonTerms.TermIdentFromName("reached_state")
              }
            );
        }

        public static Term RedCFGMulti(BoogieContextIsa boogieContext, Term cfg, Term initCFGConfig,
            Term finalCFGConfig)
        {
            return
                new TermApp(redCfgMultiId,
                    new List<Term>
                    {
                        boogieContext.absValTyMap,
                        boogieContext.methodContext,
                        boogieContext.varContext,
                        boogieContext.funContext,
                        boogieContext.rtypeEnv,
                        cfg,
                        initCFGConfig,
                        finalCFGConfig
                    }
                );
        }

        public static Term RedCFGKStep(BoogieContextIsa boogieContext, Term cfg, Term initCFGConfig, Term numSteps,
            Term finalCFGConfig)
        {
            return
                new TermApp(redCfgKStepId,
                    new List<Term>
                    {
                        boogieContext.absValTyMap,
                        boogieContext.methodContext,
                        boogieContext.varContext,
                        boogieContext.funContext,
                        boogieContext.rtypeEnv,
                        cfg,
                        initCFGConfig,
                        numSteps,
                        finalCFGConfig
                    });
        }
        
        public static Term AstToCfgLoopIndHypothesis(BoogieContextIsa astBoogieContext, BoogieContextIsa cfgBoogieContext, Term ast, Term bigblock, Term cont, Term cfgBody, Term blockIndex, Term posts)
        {
          return
            new TermApp(astLoopIhId,
              new List<Term>
              {
                IsaCommonTerms.TermIdentFromName("j"),
                astBoogieContext.absValTyMap,
                astBoogieContext.methodContext,
                //cfgBoogieContext.methodContext,
                astBoogieContext.varContext,
                astBoogieContext.funContext,
                astBoogieContext.rtypeEnv,
                ast,
                bigblock,
                cont,
                cfgBody,
                blockIndex,
                posts,
                IsaCommonTerms.TermIdentFromName("reached_bb"),
                IsaCommonTerms.TermIdentFromName("reached_cont"),
                IsaCommonTerms.TermIdentFromName("reached_state")
              });
        }

        public static Term CFGConfigNode(Term node, Term state)
        {
            return CFGConfig(IsaCommonTerms.Inl(node), state);
        }

        public static Term CFGConfigDone(Term state)
        {
            return CFGConfig(IsaCommonTerms.Inr(IsaCommonTerms.Unit()), state);
        }

        public static Term CFGConfig(Term nodeOrDone, Term state)
        {
            return new TermTuple(new List<Term> {nodeOrDone, state});
        }

        public static Term RedExpr(BoogieContextIsa boogieContext, Term expr, Term state, Term resultValue)
        {
            return
                new TermApp(redExprId,
                    new List<Term>
                    {
                        boogieContext.absValTyMap,
                        boogieContext.varContext,
                        boogieContext.funContext,
                        boogieContext.rtypeEnv,
                        expr,
                        state,
                        resultValue
                    });
        }

        public static Term FunDecl(Function f, IVariableTranslationFactory varTranslationFactory, IsaUniqueNamer uniqueNamer,
            bool includeName = true)
        {
            var typeIsaVisitor = LemmaHelper.FunTypeIsaVisitor(f, varTranslationFactory);

            Term fname = new StringConst(uniqueNamer.RemoveApostropheInFunc(f.Name));
            Term numTypeParams = new NatConst(f.TypeParameters.Count);
            var argTypes = new TermList(f.InParams.Select(v => typeIsaVisitor.Translate(v.TypedIdent.Type)).ToList());
            var retType = typeIsaVisitor.Translate(f.OutParams.First().TypedIdent.Type);
            if (includeName)
                return new TermTuple(new List<Term> {fname, numTypeParams, argTypes, retType});
            return new TermTuple(new List<Term> {numTypeParams, argTypes, retType});
        }
        public static Term VarDeclWithoutName(Variable v, TypeIsaVisitor typeIsaVisitor, Func<Absy, Term> boogieToIsa)
        {
            return VarDecl(v, null, typeIsaVisitor, boogieToIsa);
        }

        /// <summary>
        /// Computes the variable declaration.
        /// </summary>
        /// <param name="v">input variable</param>
        /// <param name="id">id to be used for variable. If it is null, then the id will not be included in the result (in which case
        /// can instead invoke <see cref="VarDeclWithoutName"/>.</param>
        /// <param name="typeIsaVisitor">type isabelle visitor</param>
        /// <param name="boogieToIsa">boogie to isabelle translator</param>
        /// <returns>Variable declaration representation of <paramref name="v"/>.
        ///          The identifier <paramref name="id"/> is excluded if it is null.</returns>
        public static Term VarDecl(Variable v, Term id, TypeIsaVisitor typeIsaVisitor, Func<Absy, Term> boogieToIsa)
        {
            var (vType, vWhereClause) = VarDeclTuple(v, typeIsaVisitor, boogieToIsa);
            
            if (id != null)
                return new TermTuple(new List<Term> {id, vType, vWhereClause});
            
            return new TermTuple(new List<Term> {vType, vWhereClause});
        }
        
        /// <summary>
        /// Returns the properties associated with <paramref name="v"/> in its variable declaration.
        /// The first element of the result tuple is the type and the second element is the where clause.
        /// </summary>
        public static Tuple<Term, Term> VarDeclTuple(Variable v, TypeIsaVisitor typeIsaVisitor, Func<Absy, Term> boogieToIsa)
        {
            var vType = typeIsaVisitor.Translate(v.TypedIdent.Type);
            var vWhereClause = v.TypedIdent.WhereExpr != null
                ? IsaCommonTerms.SomeOption(boogieToIsa(v.TypedIdent.WhereExpr))
                : IsaCommonTerms.NoneOption();
            
            return Tuple.Create(vType, vWhereClause);
       }

        public static Term ConvertValToBool(Term val)
        {
            return new TermApp(ConvertValToBoolId, val);
        }

        public static Term ConvertValToInt(Term val)
        {
            return new TermApp(ConvertValToIntId, val);
        }
        
        public static Term ConvertValToReal(Term val)
        {
            return new TermApp(ConvertValToRealId, val);
        }

        public static Term TypeToVal(Term absValTyMap, Term value)
        {
            return new TermApp(new TermApp(typeOfValId, absValTyMap), value);
        }

        public static Term FunInterpWf(Term absValTyMap, Term fdecls, Term finterp)
        {
            return new TermApp(funInterpWfId, new List<Term> {absValTyMap, fdecls, finterp});
        }

        public static Term FunInterpSingleWf(Function f, Term absValTyMap, Term fTerm,
            IVariableTranslationFactory factory, IsaUniqueNamer uniqueNamer)
        {
            return FunInterpSingleWf(absValTyMap, FunDecl(f, factory, uniqueNamer), fTerm);
        }

        public static Term FunInterpSingleWf(Term absValTyMap, Term fdecl, Term fun)
        {
            return new TermApp(funInterpSingleWfId, new List<Term> {absValTyMap, fdecl, fun});
        }

        public static Term StateWf(Term absValTyMap, Term typeEnv, Term vdecls, Term normalState)
        {
            return new TermApp(stateWfId, new List<Term> {absValTyMap, typeEnv, normalState, vdecls});
        }

        public static Term AxiomSat(Term absValTyMap, Term varContext, Term funContext, Term axioms, Term normalState)
        {
            return new TermApp(axiomsSatId, new List<Term> {absValTyMap, varContext, funContext, normalState, axioms});
        }

        //partial application without expression argument
        public static Term ExprSatPartial(BoogieContextIsa boogieContext, Term normalState)
        {
            return new TermApp(exprSatId,
                new List<Term>
                {
                    boogieContext.absValTyMap, boogieContext.varContext, boogieContext.funContext,
                    boogieContext.rtypeEnv, normalState
                });
        }

        public static Term ExprAllSat(BoogieContextIsa boogieContext, Term normalState, Term exprs)
        {
            return new TermApp(exprAllSatId,
                new List<Term>
                {
                    boogieContext.absValTyMap, boogieContext.varContext, boogieContext.funContext,
                    boogieContext.rtypeEnv, normalState, exprs
                });
        }

        public static Term LiftExprsToCheckedSpecs(Term expressions)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("exprs_to_only_checked_spec"), expressions);
        }

        public static Term AxiomAssm(Term absValTyMap, Term funContext, Term consts, Term normalState, Term axioms)
        {
            return new TermApp(axiomAssmId, absValTyMap, funContext, consts, normalState, axioms);
        }

        public static Term NstateGlobalRestriction(Term normalState, Term vdecls)
        {
            return new TermApp(nstateGlobRestrId, normalState, vdecls);
        }

        public static Term IsClosedType(Term ty)
        {
            return new TermApp(closedTypeId, ty);
        }

        public static Term InstantiateType(Term rtypeEnv, Term ty)
        {
            return new TermApp(instTypeId, rtypeEnv, ty);
        }
        
        public static Term ProcedureIsCorrectCfg(Term funDecls, Term constantDecls, Term uniqueConstants, Term globalDecls, Term axioms,
            Term procedure)
        {
            var typeInterpId = new SimpleIdentifier("A");
            return
              TermQuantifier.MetaAll(
                new List<Identifier> {typeInterpId},
                null,
                new TermApp(
                  IsaCommonTerms.TermIdentFromName("Semantics.proc_is_correct"),
                  //TODO: here assuming that we use "'a" for the abstract value type carrier t --> make t a parameter somewhere 
                  new TermWithExplicitType(new TermIdent(typeInterpId), 
                    IsaBoogieType.AbstractValueTyFunType(new VarType("a"))),
                  funDecls,
                  constantDecls,
                  uniqueConstants,
                  globalDecls,
                  axioms,
                  procedure,
                  IsaBoogieTerm.SematicsProcSpecSatisfied));
        }
        
    }
}