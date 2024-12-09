using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace ProofGeneration.BoogieIsaInterface.VariableTranslation
{
    internal class DeBruijnFixedVarTranslation : IFixedVariableTranslation<Variable>
    {
        private readonly IDictionary<Variable, int> globalsMapping;
        private readonly IDictionary<Variable, int> paramsAndLocalMapping;

        public DeBruijnFixedVarTranslation(BoogieMethodData methodData, bool globalsBeforeLocals = true)
        {
            paramsAndLocalMapping = new Dictionary<Variable, int>();
            globalsMapping = new Dictionary<Variable, int>();

            var id = 0;

            void AddVarsToMapping(IEnumerable<Variable> vars, IDictionary<Variable, int> dict)
            {
                foreach (var v in vars)
                {
                    if (dict.ContainsKey(v))
                        throw new ProofGenUnexpectedStateException(GetType(), "duplicate variables");
                    dict.Add(v, id);
                    id++;
                }
            }

            //order important
            if (globalsBeforeLocals)
            {
                AddVarsToMapping(methodData.Constants, globalsMapping);
                AddVarsToMapping(methodData.GlobalVars, globalsMapping);
                AddVarsToMapping(methodData.InParams, paramsAndLocalMapping);
                AddVarsToMapping(methodData.Locals, paramsAndLocalMapping);
            }
            else
            {
                AddVarsToMapping(methodData.InParams, paramsAndLocalMapping);
                AddVarsToMapping(methodData.Locals, paramsAndLocalMapping);
                AddVarsToMapping(methodData.Constants, globalsMapping);
                AddVarsToMapping(methodData.GlobalVars, globalsMapping);
            }
        }

        public int VariableId(Variable variable)
        {
            if (paramsAndLocalMapping.TryGetValue(variable, out var localResult)) return localResult;
            if (globalsMapping.TryGetValue(variable, out var globalResult)) return globalResult;

            throw new ProofGenUnexpectedStateException(GetType(), "cannot find variable " + variable);
        }


        public string OutputMapping()
        {
            return
                "constants and globals: " + Environment.NewLine +
                string.Join(Environment.NewLine, globalsMapping) + Environment.NewLine +
                " params and locals:" + Environment.NewLine +
                string.Join(Environment.NewLine, paramsAndLocalMapping);
        }
    }
}