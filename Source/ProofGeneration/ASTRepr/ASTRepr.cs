using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;

namespace ProofGeneration.ASTRepresentation
{
    public class ASTRepr
    {
        private readonly IList<BigBlock> bigblocks;
        
        public ASTRepr(IList<BigBlock> bigblocks)
        {
            this.bigblocks = bigblocks;
        }

        public int NumOfBlocks()
        {
            return bigblocks.Count;
        }

        public bool ContainsBlock(BigBlock b)
        {
            return bigblocks.Contains(b);
        }
        
        public int GetUniqueIntLabel(BigBlock b)
        {
          for (var i = 0; i < bigblocks.Count; i++)
          {
            if (bigblocks[i] == b)
            {
              return i;
            }
          }

          return -1;
        }

        public TermList GetAstAsTermList(AstToCfgProofGenInfo proofGenInfo)
        {
          IList<Term> terms = new List<Term>();
          for (var i = 0; i < bigblocks.Count; i++)
          {
            if (proofGenInfo.GetMappingCopyBigBlockToMarker()[bigblocks[i]])
            {
              Term bb = IsaCommonTerms.TermIdentFromName("bigblock_" + i);
              terms.Add(bb); 
            }
          }

          return new TermList(terms);
        }
        
        public List<string> GetMainContinuations(AstToCfgProofGenInfo proofGenInfo)
        {
          List<string> strings = new List<string>();
          for (var i = 0; i < bigblocks.Count; i++)
          {
            if (proofGenInfo.GetMappingCopyBigBlockToMarker()[bigblocks[i]])
            {
              string cont = "cont_" + i + "_def";
              strings.Add(cont); 
            }
          }

          return strings;
        }

        public IEnumerable<BigBlock> GetBlocksForwards()
        {
            for (var i = 0; i < bigblocks.Count; i++)
                yield return bigblocks[i];
        }

        public IEnumerable<BigBlock> GetBlocksBackwards()
        {
            for (var i = bigblocks.Count - 1; i >= 0; i--)
                yield return bigblocks[i];
        }
    }
}