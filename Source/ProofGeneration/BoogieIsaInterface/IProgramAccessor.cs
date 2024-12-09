using Isabelle.Ast;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;

namespace ProofGeneration.BoogieIsaInterface
{
    public interface IGlobalProgramAccessor
    {
        public string TheoryName();
        public Term FunctionsDecl();
        public Term AxiomsDecl();
        public Term ConstsAndGlobalsDecl();
        public string ConstsDecl();
        public string UniqueConstsDecl();
        public string GlobalsDecl();
        
        /// <summary>
        /// fresh variable translation
        /// </summary>
        public BoogieVariableTranslation VariableTranslation();
    }
    
    public interface IProgramAccessor : IGlobalProgramAccessor
    {
        public Term ProcDecl();
        public string ProcDeclName();
        public Term PreconditionsDecl();
        public string PreconditionsDeclName();
        public Term PostconditionsDecl();
        public string PostconditionsDeclName();
        public Term CfgDecl();
        public string CfgDeclName();
        
        /// <summary>
        /// params + local variables
        /// </summary>
        public Term ParamsAndLocalsDecl();

        /// <summary>
        /// globals + constant variables
        /// </summary>
        public string ParamsDecl();
        public string LocalsDecl();
        public Term VarContext();

        public IsaBlockInfo BlockInfo();

        public IsaBigBlockInfo BigBlockInfo();
        
        public string MembershipLemma(Declaration d);

        /// <summary>
        /// Does not take global variables into account.
        /// </summary>
        public string ConstantMembershipLemma(Variable c);

        public string GlobalsLocalsDisjointLemma();
        
        public string GlobalsAtMostMax();
        
        public string LocalsAtLeastMin();
        
        public string FuncsWfTyLemma();
        
        public string VarContextWfTyLemma();
        
        public string LookupVarDeclLemma(Variable v);
        
        public string LookupVarTyLemma(Variable v);
    }
}