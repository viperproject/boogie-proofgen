using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface
{
    public class BoogieGlobalData
    {
        public BoogieGlobalData(IEnumerable<Function> functions, IEnumerable<Axiom> axioms,
            IEnumerable<Variable> globalVars, IEnumerable<Constant> constants)
        {
            Functions = functions;
            Axioms = axioms;
            GlobalVars = globalVars;
            Constants = constants;
        }

        public IEnumerable<Function> Functions { get; }
        public IEnumerable<Axiom> Axioms { get; }
        public IEnumerable<Variable> GlobalVars { get; }
        public IEnumerable<Constant> Constants { get; }

        public static BoogieGlobalData CreateEmpty()
        {
            return new BoogieGlobalData(new List<Function>(), new List<Axiom>(), new List<Variable>(),
                new List<Constant>());
        }
    }
}