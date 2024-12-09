using System;
using System.Collections;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.ASTRepresentation;
using ProofGeneration.Util;

namespace ProofGeneration
{
  internal class IsaProgramGeneratorForAst
    {
        private MultiCmdIsaVisitor cmdIsaVisitor;
        private BoogieVariableTranslation varTranslation;
        private IVariableTranslationFactory varTranslationFactory;
        
        private readonly string astName = "proc_body";
        private readonly string procDefName = "ast_proc";

        public IProgramAccessor GetIsaProgram(
            string theoryName,
            string procName,
            BoogieMethodData methodData,
            IsaProgramGeneratorConfig config,
            IVariableTranslationFactory varTranslationFactory,
            ASTRepr ast,
            ASTRepr originalAst,
            AstToCfgProofGenInfo proofGenInfo,
            IsaUniqueNamer uniqueNamer,
            out IList<OuterDecl> decls,
            MembershipLemmaConfig membershipLemmaConfig,
            bool onlyGlobalData = false
        )
        {
            this.varTranslationFactory = varTranslationFactory;
            varTranslation = varTranslationFactory.CreateTranslation();
            cmdIsaVisitor = new MultiCmdIsaVisitor(varTranslationFactory);

            decls = new List<OuterDecl>();
            var isaGlobalProgramRepr = new IsaGlobalProgramRepr(
                FunctionDeclarationsName(),
                AxiomDeclarationsName(),
                VariableDeclarationsName("globals"),
                VariableDeclarationsName("constants"),
                "unique_consts"
                );
            var globalsMax = methodData.Constants.Count() + methodData.GlobalVars.Count() - 1;
            // assume single versioning and order on constants, globals, params, locals
            var localsMin = globalsMax + 1;
            if (globalsMax < 0)
                globalsMax = 0;

            MembershipLemmaManager membershipLemmaManager;
            if (onlyGlobalData)
            {
                membershipLemmaManager = new MembershipLemmaManager(
                        isaGlobalProgramRepr, globalsMax, varTranslationFactory, theoryName );
            }
            else
            {
                var bigblockInfo = BigBlockToInfo(theoryName, ast, proofGenInfo);
                var isaProgramRepr = new IsaProgramRepr(
                    isaGlobalProgramRepr,
                    PreconditionDeclarationName(),
                    PostconditionDeclarationName(),
                    VariableDeclarationsName("params"),
                    VariableDeclarationsName("locals"),
                    astName,
                    procDefName);
                membershipLemmaManager = new MembershipLemmaManager(config, isaProgramRepr, null, bigblockInfo,
                Tuple.Create(globalsMax, localsMin), varTranslationFactory, theoryName);
                
                foreach (var decl_list in bigblockInfo.BigBlockDefs.Values)
                {
                  decls.AddRange(decl_list);
                }

                IList<OuterDecl> continuations = getContinuations(originalAst, proofGenInfo);
                decls.AddRange(continuations);

                IList<Term> bigblock_terms = new List<Term>();
                IEnumerable<BigBlock> bigblocks = ast.GetBlocksBackwards();
                foreach (BigBlock b in bigblocks)
                {
                  Term b_term = IsaCommonTerms.TermIdentFromName("bigblock_" + ast.GetUniqueIntLabel(b));
                  if (proofGenInfo.GetMappingCopyBigBlockToMarker()[b])
                  {
                    bigblock_terms.Add(b_term); 
                  }
                }

                bigblock_terms = Enumerable.Reverse(bigblock_terms).ToList();
                var methodBodyAST = IsaBoogieTerm.MethodASTBody(bigblock_terms);

                var methodBodyDecl = GetMethodBodyASTDecl(procName, methodBodyAST);
                decls.AddRange(
                    new List<OuterDecl>
                    {
                       methodBodyDecl
                    });

                if (config.specsConfig != SpecsConfig.None)
                {
                    OuterDecl preconditions;
                    OuterDecl postconditions;

                    if (config.specsConfig == SpecsConfig.AllPreCheckedPost)
                    {
                        preconditions = GetExprListIsa(PreconditionDeclarationName(), methodData.Preconditions.Select(pre => pre.Item1));
                        postconditions = GetExprListIsa(PostconditionDeclarationName(), methodData.Postconditions.Where(post => !post.Item2).Select(post => post.Item1));
                    }
                    else
                    {
                        preconditions = GetExprListIsa(PreconditionDeclarationName(), methodData.Preconditions);
                        postconditions = GetExprListIsa(PostconditionDeclarationName(), methodData.Postconditions);
                    }
                    
                    decls.Add(preconditions);
                    decls.Add(postconditions);
                }

                if(config.generateParamsAndLocals) {
                    decls.Add(GetVariableDeclarationsIsa("params", methodData.InParams));
                    decls.Add(GetVariableDeclarationsIsa("locals", methodData.Locals));
                }
                
                /* membership lemmas might still be added even if the parameter and local variable definitions are not generated
                 * at this point (since the variable context may still be different, which requires other lookup lemmas)
                 */
                if (membershipLemmaConfig.GenerateVariableMembershipLemmas)
                {
                    membershipLemmaManager.AddVariableMembershipLemmas(methodData.InParams, VarKind.ParamOrLocal);
                    membershipLemmaManager.AddVariableMembershipLemmas(methodData.Locals, VarKind.ParamOrLocal);
                }
            }

            if (config.generateAxioms)
            {
                decls.Add(GetAxioms(methodData.Axioms));
                if (membershipLemmaConfig.GenerateAxiomMembershipLemmas)
                {
                  membershipLemmaManager.AddAxiomMembershipLemmas(methodData.Axioms);
                }
            }

            if (config.generateFunctions)
            {
                decls.Add(GetFunctionDeclarationsIsa(methodData.Functions, uniqueNamer));
                if (membershipLemmaConfig.GenerateFunctionMembershipLemmas)
                {
                  membershipLemmaManager.AddFunctionMembershipLemmas(methodData.Functions, uniqueNamer);
                }
            }

            if (config.generateGlobalsAndConstants)
            {
                decls.Add(GetVariableDeclarationsIsa("globals", methodData.GlobalVars));
                decls.Add(GetVariableDeclarationsIsa("constants", methodData.Constants));
            }

            if (membershipLemmaConfig.GenerateVariableMembershipLemmas)
            {
                membershipLemmaManager.AddVariableMembershipLemmas(methodData.GlobalVars, VarKind.Global);
                membershipLemmaManager.AddVariableMembershipLemmas(methodData.Constants, VarKind.Constant);
                decls.AddRange(membershipLemmaManager.OuterDecls());
            }

            if (config.specsConfig != SpecsConfig.None)
            {
                DefDecl methodDef = MethodDefinition(membershipLemmaManager, methodData, config.specsConfig);
                decls.Add(methodDef);
            }

            return membershipLemmaManager;
        }

        private DefDecl GetAxioms(IEnumerable<Axiom> axioms)
        {
            var axiomsExpr = new List<Term>();
            foreach (var ax in axioms)
            {
                var axTerms = cmdIsaVisitor.Translate(ax.Expr);
                if (axTerms.Count != 1)
                    throw new ProofGenUnexpectedStateException(GetType(), "axiom not translated into single term");
                
                axiomsExpr.Add(axTerms.First());
            }

            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(axiomsExpr));

            return new DefDecl(AxiomDeclarationsName(), equation);
        }

        private string AxiomDeclarationsName()
        {
            return "axioms";
        }

        private DefDecl MethodDefinition(IProgramAccessor programAccessor, BoogieMethodData methodData, SpecsConfig specConfig)
        {
            var modifiedVarsTerm = new TermList(
                methodData.ModifiedVars.Select(id =>
                {
                    if (varTranslation.VarTranslation.TryTranslateVariableId(id.Decl, out Term idTerm, out _))
                    {
                        return idTerm;
                    }
                    else
                    {
                        throw new ProofGenUnexpectedStateException("Could not get variable id");
                    }
                }).ToList());
            
            var mapping =
                new List<Tuple<string, Term>>
                {
                    Tuple.Create("proc_ty_args", (Term) new NatConst(methodData.TypeParams.Count())),
                    Tuple.Create("proc_args", (Term) IsaCommonTerms.TermIdentFromName(programAccessor.ParamsDecl())),
                    //TODO: incorporate return values and modified variables
                    Tuple.Create("proc_rets", (Term) IsaCommonTerms.EmptyList),
                    Tuple.Create("proc_modifs", (Term) modifiedVarsTerm),
                    Tuple.Create("proc_pres", specConfig == SpecsConfig.All ?  programAccessor.PreconditionsDecl() : IsaBoogieTerm.LiftExprsToCheckedSpecs(programAccessor.PreconditionsDecl())),
                    Tuple.Create("proc_posts", specConfig == SpecsConfig.All ? programAccessor.PostconditionsDecl() : IsaBoogieTerm.LiftExprsToCheckedSpecs(programAccessor.PostconditionsDecl())),
                    //TODO: support abstract procedures
                    Tuple.Create("proc_body", 
                        IsaCommonTerms.SomeOption(new TermTuple(IsaCommonTerms.TermIdentFromName(programAccessor.LocalsDecl()), programAccessor.CfgDecl())))
                };
            
            Term method = new TermRecord(mapping);

            DefDecl methodDef = DefDecl.CreateWithoutArg(procDefName, IsaBoogieType.AstProcedureType(), method);
            return methodDef;
        }

        private IsaBigBlockInfo BigBlockToInfo(string theoryName, ASTRepr ast, AstToCfgProofGenInfo proofGenInfo)
        {
            var blockToDecl = new Dictionary<BigBlock, IList<DefDecl>>();
            var blockToCounter = new Dictionary<BigBlock, int>();
            
            BigBlockTermBuilder builder = new BigBlockTermBuilder();

            foreach (BigBlock b in ast.GetBlocksBackwards())
            {
                int flag = 0;
                if (proofGenInfo.GetMappingLoopHeadBigBlocktoOrigLoopBigBlock().Keys.Contains(b))
                {
                  flag = 1;
                }
                
                int uniqueIntLabel = ast.GetUniqueIntLabel(b);
                string nameToUse = "bigblock_" + uniqueIntLabel;
                var translatedBigBlock = builder.makeBigBlockTerm(b, proofGenInfo, cmdIsaVisitor, flag, 0, nameToUse, out int updatedNestedBlockTracker);
                
                proofGenInfo.AddBigBlockToIndexPair(b, uniqueIntLabel);
                
                IDictionary<BigBlock, IList<DefDecl>> bb_defs = builder.getBigblockDefDecls();
                foreach(KeyValuePair<BigBlock, IList<DefDecl>> bb_def in bb_defs)
                {
                  if (!blockToDecl.ContainsKey(bb_def.Key))
                  {
                    blockToDecl.Add(bb_def.Key, bb_def.Value); 
                  }
                }
                
                blockToCounter[b] = uniqueIntLabel;
            }

            return new IsaBigBlockInfo(theoryName, blockToCounter, blockToDecl);
        }

        private IList<OuterDecl> getContinuations(ASTRepr originalAst, AstToCfgProofGenInfo proofGenInfo)
        {
          IList<OuterDecl> declsToReturn = new List<OuterDecl>();
          BigBlockTermBuilder builder = new BigBlockTermBuilder();

          //Loop through the big blocks in 'original AST' backwards.
          //The name 'original AST' refers to the fact that the AST is in its original form, as constructed, i.e, it's not 'unrolled'.
          //However, the big blocks inside it are copies. 
          foreach (BigBlock b in originalAst.GetBlocksBackwards())
          {
            BigBlock correspondingBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[b];
            BigBlock successorBigBlockOrig = correspondingBigBlockOrig.successorBigBlock;

            int successorIndex = -1;
            if (successorBigBlockOrig != null)
            {
              BigBlock successorBigBlockCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[successorBigBlockOrig];
              successorIndex = proofGenInfo.GetMappingCopyBigBlockToIndex()[successorBigBlockCopy];
            }

            //This should be the same as big block 'b'? 
            BigBlock correspondingBigBlockCopy = proofGenInfo.GetMappingOrigBigblockToCopyBigblock()[correspondingBigBlockOrig];
            
            //Construct the continuation term, which corresponds to 'b' and which is to be used in the Isabelle proofs later. 
            Term continuation = builder.makeContinuationTerm(correspondingBigBlockCopy, proofGenInfo, successorIndex);
            int bigblockIndex = proofGenInfo.GetMappingCopyBigBlockToIndex()[correspondingBigBlockCopy];
            DefDecl continuationDecl = DefDecl.CreateWithoutArg("cont_" + bigblockIndex, continuation);
            declsToReturn.Add(continuationDecl);

            //Special continuation term, which is used if 'b' contains a WhileCmd.
            DefDecl continuationDeclForUnwrappedBigBlock = null;
            
            if (b.ec is WhileCmd)
            {
              foreach (var pair in proofGenInfo.GetMappingLoopHeadBigBlocktoOrigLoopBigBlock())
              {
                if (pair.Value == correspondingBigBlockOrig)
                {
                  BigBlock unwrapped = pair.Key;
                  
                  Term continuationUnwrapped = builder.makeContinuationTerm(unwrapped, proofGenInfo, successorIndex);
                  int bigblockIndexUnwrapped = proofGenInfo.GetMappingCopyBigBlockToIndex()[unwrapped];
                  continuationDeclForUnwrappedBigBlock = DefDecl.CreateWithoutArg("cont_" + bigblockIndexUnwrapped, continuationUnwrapped);
                }
              }
              
              if (continuationDeclForUnwrappedBigBlock != null)
              {
                declsToReturn.Add(continuationDeclForUnwrappedBigBlock); 
              }
              
              WhileCmd wcmd = (WhileCmd) b.ec;
              ASTRepr body = new ASTRepr(wcmd.Body.BigBlocks);
              
              //recursively construct continuation terms for the body of the while-loop (again from the end to the beginning).
              IList<OuterDecl> bodyConts = getContinuations(body, proofGenInfo);
              declsToReturn.AddRange(bodyConts);
            }
            else if (b.ec is IfCmd)
            {
              IfCmd ifcmd = (IfCmd) b.ec;
              ASTRepr thn = new ASTRepr(ifcmd.thn.BigBlocks);
              
              //recursively construct continuation terms for the body of the thn-branch of the if-statement.
              declsToReturn.AddRange(getContinuations(thn, proofGenInfo));

              if (ifcmd.elseBlock != null)
              {
                ASTRepr elseBlock = new ASTRepr(ifcmd.elseBlock.BigBlocks);
                
                //recursively construct continuation terms for the body of the else-branch of the if-statement.
                declsToReturn.AddRange(getContinuations(elseBlock, proofGenInfo)); 
              }
            }
          }

          return declsToReturn;
        }

        private DefDecl GetFunctionDeclarationsIsa(IEnumerable<Function> functions, IsaUniqueNamer uniqueNamer)
        {
            var fdecls = new List<Term>();
            foreach (var f in functions) fdecls.Add(IsaBoogieTerm.FunDecl(f, varTranslationFactory, uniqueNamer));

            return DefDecl.CreateWithoutArg(FunctionDeclarationsName(), new TermList(fdecls));
        }

        private string FunctionDeclarationsName()
        {
            return "fdecls";
        }

        private string PreconditionDeclarationName()
        {
            return "pres";
        }

        private string PostconditionDeclarationName()
        {
            return "post";
        }

        private DefDecl GetVariableDeclarationsIsa(string varKind, IEnumerable<Variable> variables)
        {
            var typeIsaVisitor = new TypeIsaVisitor(varTranslation.TypeVarTranslation);

            var vdecls = new List<Term>();

            foreach (var v in variables)
            {
                if (varTranslation.VarTranslation.TryTranslateVariableId(v, out var resId, out _))
                {
                    vdecls.Add(IsaBoogieTerm.VarDecl(v, resId, typeIsaVisitor, cmdIsaVisitor.TranslateSingle));
                }
                else
                {
                    throw new ProofGenUnexpectedStateException(GetType(), "Cannot translate variable " + v.Name);
                }
            }

            var equation = new Tuple<IList<Term>, Term>(new List<Term>(), new TermList(vdecls));
            return new DefDecl(VariableDeclarationsName(varKind), IsaBoogieType.VariableDeclsType,
                equation);
        }

        private string VariableDeclarationsName(string varKind)
        {
            return varKind + "_vdecls";
        }
        
        private DefDecl GetExprListIsa(string declName, IEnumerable<Expr> exprs)
        {
            var result = new List<Term>();
            foreach (var expr in exprs)
            {
                var termTuple = cmdIsaVisitor.TranslateSingle(expr);
                result.Add(termTuple);
            }

            return DefDecl.CreateWithoutArg(declName, new TermList(result));
        }

        private DefDecl GetExprListIsa(string declName, IEnumerable<Tuple<Expr,bool>> exprs)
        {
            var result = new List<Term>();
            foreach (var expr in exprs)
            {
                var termTuple = new TermTuple(cmdIsaVisitor.TranslateSingle(expr.Item1), new BoolConst(expr.Item2));
                result.Add(termTuple);
            }

            return DefDecl.CreateWithoutArg(declName, new TermList(result));
        }

        private DefDecl GetMethodBodyASTDecl(string methodName, Term methodBodyAST)
        {
            return DefDecl.CreateWithoutArg(astName, methodBodyAST);
        }

    }
}