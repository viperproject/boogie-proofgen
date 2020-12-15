﻿using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.BoogieIsaInterface
{
    public interface IProgramAccessor
    {
        public string TheoryName();

        public Term FunctionsDecl();
        public Term AxiomsDecl();
        public Term CfgDecl();

        //params + local variables
        public Term ParamsAndLocalsDecl();

        //globals + constant variables
        public Term ConstsAndGlobalsDecl();

        public string ConstsDecl();
        public string GlobalsDecl();

        public Term VarContext();

        public string MembershipLemma(Declaration d);

        public string GlobalsLocalsDisjointLemma();

        public string LookupVarTyLemma(Variable v);
    }
}