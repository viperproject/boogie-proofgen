using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using ProofGenUtil;

namespace ProofGeneration.CFGRepresentation
{
    public class CFGRepr
    {
        private Block[] blocks; //make sure that I can change that from readonly
        public readonly Block entry;
        private readonly IDictionary<Block, int> labeling;
        private readonly IDictionary<Block, IList<Block>> outgoingBlocks;

        //TODO: make this more robust

        /// <param name="outgoingBlocks">successor relationship.</param>
        /// <param name="labeling">
        ///     labeling must give topological order from 0 to num_of_blocks-1, if the CFG is acyclic:
        ///     label(block1) is larger than label(block2) if there is a path from block1 to block2.
        /// </param>
        /// <param name="entry">entry block of CFG.</param>
        public CFGRepr(IDictionary<Block, IList<Block>> outgoingBlocks, IDictionary<Block, int> labeling, Block entry)
        {
            Contract.Requires(labeling.Count == labeling.Values.Count && labeling.Values.Count == outgoingBlocks.Count);
            Contract.Requires(labeling.Values.Min() == 0);
            Contract.Requires(labeling.Values.Max() == outgoingBlocks.Count - 1);

            blocks = new Block[outgoingBlocks.Count];

            foreach (var kv in labeling) blocks[kv.Value] = kv.Key;

            this.outgoingBlocks = outgoingBlocks;
            this.labeling = labeling;
            this.entry = entry;
        }

        public IEnumerable<Block> GetSuccessorBlocks(Block b)
        {
            return outgoingBlocks[b];
        }

        public int NumOfSuccessors(Block b)
        {
            return outgoingBlocks[b].Count;
        }

        /// <summary>
        ///     Returns a unique integer identifier for the input block and if the CFG is acylic, ensures that
        ///     label(block1) is larger than label(block2) if there is a path from block1 to block2.
        /// </summary>
        public int GetUniqueIntLabel(Block b)
        {
            return labeling[b];
        }

        public int NumOfBlocks()
        {
            return blocks.Length;
        }

        public bool ContainsBlock(Block b)
        {
            return outgoingBlocks.ContainsKey(b);
        }

        public IEnumerable<Block> GetBlocksBackwards()
        {
            for (var i = 0; i < blocks.Length; i++)
                yield return blocks[i];
        }

        public IEnumerable<Block> GetBlocksForwards()
        {
            for (var i = blocks.Length - 1; i >= 0; i--)
                yield return blocks[i];
        }
        
        
        //TODO: Check if this is correct
        public CFGRepr(CFGRepr other)
        {
          // Copy blocks array
          blocks = new Block[other.blocks.Length];
          Array.Copy(other.blocks, blocks, other.blocks.Length);

          // Copy outgoingBlocks dictionary
          outgoingBlocks = new Dictionary<Block, IList<Block>>();
          foreach (var kvp in other.outgoingBlocks)
          {
            outgoingBlocks.Add(kvp.Key, new List<Block>(kvp.Value));
          }
          
        
          // Copy labeling dictionary
          labeling = new Dictionary<Block, int>();
          foreach (var kvp in other.labeling)
          {
            labeling.Add(kvp.Key, kvp.Value);
          }
          

          // Copy entry block
          entry = other.entry;
        }
        
        public CFGRepr Copy()
        {
          return new CFGRepr(this);
        }

        public void DeleteBackedges(IDictionary<Block, IList<Block>> BlockToLoops, IDictionary<Block, Block> selfLoops)
        {
          foreach (Block b in blocks)
          {
            List<Block> Backedges = new List<Block>();
            if (BlockToLoops.ContainsKey(b))
            {
              if (ProgramToVCProof.LemmaHelper.FinalStateIsMagic(b))
              {
                foreach (Block succ in GetSuccessorBlocks(b))
                {
                  Backedges.Add(succ);
                }
                foreach (Block toRemove in Backedges)
                {
                  toRemove.Predecessors.Remove(b);
                  outgoingBlocks[b].Remove(toRemove);
                }
              }
              else
              {
                foreach (Block succ in GetSuccessorBlocks(b))
                {
                  if (BlockToLoops[b].Contains(succ))
                  {
                    Backedges.Add(succ);
                  } 
                }
                foreach (Block toRemove in Backedges)
                {
                  toRemove.Predecessors.Remove(b);
                  outgoingBlocks[b].Remove(toRemove);
                }
                
              }

            }

            if (selfLoops.ContainsKey(b))
            {
              outgoingBlocks[b].Remove(b);
              b.Predecessors.Remove(b);
            }
          }
        }
        
        

        
        
    }
}