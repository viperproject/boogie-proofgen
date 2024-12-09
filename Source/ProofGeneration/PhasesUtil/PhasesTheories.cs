namespace ProofGeneration.PhasesUtil
{
    public class PhasesTheories
    {
        public enum Phase
        {
            Vc,
            Passification,
            CfgToDag,
            CfgOptimizations,
            AstToCfg
        }

        private readonly string astToCfgTheoryName;
        private readonly string cfgToDagTheoryName;
        private readonly string passificationTheoryName;
        private readonly string CfgOptimizationsTheoryName;

        private readonly string vcPhaseTheoryName;


        public PhasesTheories(string prefix)
        {
            vcPhaseTheoryName = prefix + "_vcphase_proof";
            passificationTheoryName = prefix + "_passification_proof";
            cfgToDagTheoryName = prefix + "_cfgtodag_proof";
            CfgOptimizationsTheoryName = prefix + "_cfgoptimizations_proof";
            astToCfgTheoryName = prefix + "_asttocfg_proof";
        }

        public string TheoryName(Phase phase)
        {
            switch (phase)
            {
                case Phase.Vc:
                    return vcPhaseTheoryName;
                case Phase.Passification:
                    return passificationTheoryName;
                case Phase.CfgToDag:
                    return cfgToDagTheoryName;
                case Phase.CfgOptimizations:
                    return CfgOptimizationsTheoryName;
                case Phase.AstToCfg:
                    return astToCfgTheoryName;
                default:
                    throw new ProofGenUnexpectedStateException("unknown phase");
            }
        }

        public static string LocalEndToEndName()
        {
            return "end_to_end";
        }

        public string EndToEndLemmaName(Phase phase, bool qualify)
        {
            //TODO: don't hardcode "glue_proof"
            var localName = phase == Phase.Passification ? "glue_proof." + LocalEndToEndName() : LocalEndToEndName();
            return MaybeQualifiedName(TheoryName(phase), localName, qualify);
        }

        private string MaybeQualifiedName(string theory, string name, bool qualify)
        {
            return qualify ? theory + "." + name : name;
        }

        public static EndToEndLemmaConfig EndToEndConfig(bool generateEndToEndTheorem, Phase currentPhase, Phase phaseWithProcEndToEnd)
        {
          if (!generateEndToEndTheorem)
          {
            return EndToEndLemmaConfig.DoNotGenerate;
          }

          if (currentPhase == phaseWithProcEndToEnd)
          {
            return EndToEndLemmaConfig.GenerateForProcedure;
          }

          return EndToEndLemmaConfig.GenerateForEntryBlock;
        }
        
    }
}