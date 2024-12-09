using System;
using System.Collections.Generic;
using ProofGeneration.PhasesUtil;

namespace ProofGeneration
{
    /// <summary>
    ///     Used to indicate which proofs should be generated.
    /// </summary>
    public class ProofGenConfig
    {
      
      private IDictionary<PhasesTheories.Phase, bool> generatePhaseProof;

      private List<PhasesTheories.Phase> phases = new List<PhasesTheories.Phase>
      {
        PhasesTheories.Phase.AstToCfg,
        PhasesTheories.Phase.CfgOptimizations,
        PhasesTheories.Phase.CfgToDag,
        PhasesTheories.Phase.Passification,
        PhasesTheories.Phase.Vc
      };

      private void UpdatePhaseDict<V>(IDictionary<PhasesTheories.Phase, V> dict, PhasesTheories.Phase key, V value)
      {
        if (!phases.Contains(key))
        {
          throw new ArgumentException("Unexpected phase " + key);
        }

        dict[key] = value;
      }
      
      private void UpdatePhaseProofFlag(PhasesTheories.Phase phase, bool flag)
      {
        UpdatePhaseDict(generatePhaseProof, phase, flag);
      }

      private bool GetPhaseProofFlag(PhasesTheories.Phase phase)
      {
        return generatePhaseProof[phase];
      }

      private ProofGenConfig AllOptions(bool enabled)
      {
        generatePhaseProof = new Dictionary<PhasesTheories.Phase, bool>();

        foreach (var phase in phases)
        {
          generatePhaseProof.Add(phase, enabled);
        }
        
        return this;
      }
      
      public ProofGenConfig AllOptionsEnabled()
      {
        return AllOptions(true);
      }
        
      public ProofGenConfig AllOptionsDisabled()
      {
        return AllOptions(false);
      }
        
      public bool GenerateAstCfgE2E(bool deadVarsElim) => 
        GenerateAstCfgProof && (!deadVarsElim && GenerateCfgDagE2E); //currently do not produce E2E if dead variables are eliminated 

      public bool GenerateCfgDagE2E => GenerateCfgDagProof && GeneratePassifE2E;

      public bool GeneratePassifE2E => GeneratePassifProof && GenerateVcE2E;

      public bool GenerateVcE2E => GenerateVcProof;

      public bool GenerateAstCfgProof => GetPhaseProofFlag(PhasesTheories.Phase.AstToCfg);
      public ProofGenConfig SetAstCfgProof(bool flag)
      {
        UpdatePhaseProofFlag(PhasesTheories.Phase.AstToCfg, flag);
        return this;
      }

      public bool GenerateCfgOptProof(bool optimizationsHaveAnEffect) =>
        optimizationsHaveAnEffect && GetPhaseProofFlag(PhasesTheories.Phase.CfgOptimizations);

      public ProofGenConfig SetCfgOptProof(bool flag)
      {
        UpdatePhaseProofFlag(PhasesTheories.Phase.CfgOptimizations, flag);
        return this;
      }

      public bool GenerateCfgDagProof => GetPhaseProofFlag(PhasesTheories.Phase.CfgToDag);
      public ProofGenConfig SetCfgDagProof(bool flag)
      {
        UpdatePhaseProofFlag(PhasesTheories.Phase.CfgToDag, flag);
        return this;
      }

      public bool GeneratePassifProof => GetPhaseProofFlag(PhasesTheories.Phase.Passification);
      public ProofGenConfig SetPassifProof(bool flag)
      {
        UpdatePhaseProofFlag(PhasesTheories.Phase.Passification, flag);
        return this;
      }

      public bool GenerateVcProof => GetPhaseProofFlag(PhasesTheories.Phase.Vc);
      
      public ProofGenConfig SetVcProof(bool flag)
      {
        UpdatePhaseProofFlag(PhasesTheories.Phase.Vc, flag);
        return this;
      }

      /** Program Generation Getters */
      
      public bool GenerateBeforeAstCfgProg => GenerateAstCfgProof; 

      public bool GenerateUnoptimizedCfgProg(bool optimizationsHaveAnEffect)
      {
        return optimizationsHaveAnEffect && GenerateAstCfgProof ||
               GenerateCfgOptProof(optimizationsHaveAnEffect);
      }

      public bool GenerateBeforeCfgDagProg(bool optimizationsHaveAnEffect)
      {
        return (!optimizationsHaveAnEffect && GenerateAstCfgProof) || //directly connect AST to CFG before CfgToDag if there are no optimizations
               GenerateCfgOptProof(optimizationsHaveAnEffect) ||  
               GenerateCfgDagProof;
      }

      public bool GenerateBeforePassiveProg => GenerateCfgDagProof || GeneratePassifProof;
      public bool GeneratePassifiedProg => GeneratePassifProof || GenerateVcProof;
      
    }
}