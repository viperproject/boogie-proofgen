namespace ProofGeneration;

public class MembershipLemmaConfig
{

  public bool GenerateAxiomMembershipLemmas
  {
    get;
  }
  
  public bool GenerateFunctionMembershipLemmas
  {
    get;
  }

  public bool GenerateVariableMembershipLemmas
  {
    get;
  }

  public MembershipLemmaConfig(bool generateAxiomMembershipLemmas, bool generateFunctionMembershipLemmas, bool generateVariableMembershipLemmas)
  { 
    GenerateAxiomMembershipLemmas = generateAxiomMembershipLemmas;
    GenerateFunctionMembershipLemmas = generateFunctionMembershipLemmas;
    GenerateVariableMembershipLemmas = generateVariableMembershipLemmas;
  }

}