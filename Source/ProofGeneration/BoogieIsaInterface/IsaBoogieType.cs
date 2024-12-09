using System.Collections.Generic;
using Isabelle.Ast;
using Isabelle.Util;

namespace ProofGeneration
{
    internal class IsaBoogieType
    {
        private static readonly TermIdent tprimId = IsaCommonTerms.TermIdentFromName("TPrim");
        private static readonly TermIdent tprimClosedId = IsaCommonTerms.TermIdentFromName("TPrimC");
        private static readonly TermIdent tboolId = IsaCommonTerms.TermIdentFromName("TBool");
        private static readonly TermIdent tintId = IsaCommonTerms.TermIdentFromName("TInt");
        private static readonly TermIdent trealId = IsaCommonTerms.TermIdentFromName("TReal");
        private static readonly TermIdent tvarId = IsaCommonTerms.TermIdentFromName("TVar");
        private static readonly TermIdent tconId = IsaCommonTerms.TermIdentFromName("TCon");
        private static readonly TermIdent tconClosedId = IsaCommonTerms.TermIdentFromName("TConC");

        public static TypeIsa VariableDeclsType => IsaCommonTypes.GetDataTypeNoArg("vdecls");

        public static TypeIsa BoogieType()
        {
            return IsaCommonTypes.GetDataTypeNoArg("ty");
        }

        public static Term TVar(int n)
        {
            return new TermApp(tvarId, new NatConst(n));
        }

        public static Term PrimType(Term primType, bool useClosedConstructor = false)
        {
            var id = useClosedConstructor ? tprimClosedId : tprimId;
            return new TermApp(id, primType);
        }

        public static Term BoolType()
        {
            return tboolId;
        }

        public static Term IntType()
        {
            return tintId;
        }
        
        public static Term RealType()
        {
            return trealId;
        }

        public static Term TConType(string constructorName, List<Term> constructorArgs,
            bool useClosedConstructor = false)
        {
            var id = useClosedConstructor ? tconClosedId : tconId;
            return new TermApp(new TermApp(id, new StringConst(constructorName)), new TermList(constructorArgs));
        }

        public static TypeIsa ValType(TypeIsa absValType)
        {
            return new DataType("val", new List<TypeIsa> {absValType});
        }

        public static TypeIsa LitType()
        {
            return new DataType("lit");
        }

        public static TypeIsa AbstractValueTyFunType(TypeIsa absValType)
        {
            return new DataType("absval_ty_fun", new List<TypeIsa> {absValType});
        }

        public static TypeIsa NormalStateType(TypeIsa absValType)
        {
            return new DataType("nstate", new List<TypeIsa> {absValType});
        }

        public static TypeIsa StateType(TypeIsa absValType)
        {
            return IsaCommonTypes.GetDataTypeSingle("state", absValType);
        }

        public static TypeIsa GetCFGNodeType()
        {
            return new DataType("node", new List<TypeIsa>());
        }

        public static TypeIsa CFGNodeOrReturnType()
        {
            return new SumType(GetCFGNodeType(), IsaCommonTypes.GetUnitType());
        }

        public static TypeIsa ProcedureType()
        {
            return new DataType("mbodyCFG procedure");
        }
        
        public static TypeIsa AstProcedureType()
        {
          return new DataType("ast procedure");
        }

        public static TypeIsa GetBlockType()
        {
            return new DataType("block", new List<TypeIsa>());
        }

        public static TypeIsa BoogieFuncInterpType(TypeIsa absValType)
        {
            return new ArrowType(IsaCommonTypes.GetListType(BoogieType()),
                new ArrowType(IsaCommonTypes.GetListType(ValType(absValType)),
                    IsaCommonTypes.GetOptionType(ValType(absValType)))
            );
        }

        public static TypeIsa VnameType()
        {
            return IsaCommonTypes.GetDataTypeNoArg("vname");
        }

        public static TypeIsa FnameType()
        {
            return IsaCommonTypes.GetDataTypeNoArg("fname");
        }

        public static TypeIsa VarContextType()
        {
            return new DataType("var_context", new List<TypeIsa>());
        }

        public static TypeIsa ProcContextType()
        {
            return new DataType("mbodyCFG proc_context", new List<TypeIsa>());
        }

        public static TypeIsa FunInterpType(TypeIsa absValType)
        {
            return new DataType("fun_interp", new List<TypeIsa> {absValType});
        }

        public static TypeIsa RuntimeTypeEnvType()
        {
            return new DataType("rtype_env", new List<TypeIsa>());
        }
    }
}