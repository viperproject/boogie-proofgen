using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Linq;
using System.Runtime.Serialization.Formatters.Binary;

namespace Microsoft.Boogie
{
  public static class AstToCfgProofGenInfoManager
  {
    private static IDictionary<Implementation, AstToCfgProofGenInfo> implToProofGenInfo;
    private static AstToCfgProofGenInfo currentProofGenInfo;

    public static IDictionary<Implementation, AstToCfgProofGenInfo> GetImplToProofGenInfo()
    {
      return implToProofGenInfo ??= new Dictionary<Implementation, AstToCfgProofGenInfo>();
    }
    
    public static AstToCfgProofGenInfo GetCurrentProofGenInfo()
    {
      return currentProofGenInfo ??= new AstToCfgProofGenInfo();
    }
    
    public static void SetCurrentProofGenInfo(AstToCfgProofGenInfo proofGenInfo)
    {
      currentProofGenInfo = proofGenInfo;
    }
  }
}