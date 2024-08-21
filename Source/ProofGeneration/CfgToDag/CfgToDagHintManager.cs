using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using ProofGeneration.Util;

namespace ProofGeneration.CfgToDag
{
    public class CfgToDagHintManager
    {
        private readonly IDictionary<Block, List<Block>> backedgeNodeToLoopHead = new Dictionary<Block, List<Block>>();

        private readonly IDictionary<Block, Block> beforeDagToOrig;

        private readonly IDictionary<Block, LoopHeadHint> loopHeadHints = new Dictionary<Block, LoopHeadHint>();

        //maps backedge nodes which are not present before the CFG-to-DAG to the corresponding loop head
        private readonly IDictionary<Block, Block> newBackedgeNodesToLoopHead = new Dictionary<Block, Block>();
        
        //maps nodes before entry to loop which are not present before CFG-to-DAG to the corresponding loop head
        private readonly IDictionary<Block, Block> newPreLoopNodesToLoopHead = new Dictionary<Block, Block>();
        
        private readonly IDictionary<Block, Block> origToBeforeDag;

        private IDictionary<Block, Block> _afterDagToOrig;

        public CfgToDagHintManager(Graph<Block> graph, IDictionary<Block, Block> beforeDagToOrig)
        {
            this.beforeDagToOrig = beforeDagToOrig;
            origToBeforeDag = beforeDagToOrig.InverseDict();

            foreach (var loopHead in graph.Headers)
            foreach (var block in graph.BackEdgeNodes(loopHead))
                if (backedgeNodeToLoopHead.TryGetValue(origToBeforeDag[block], out var loopHeads))
                    loopHeads.Add(origToBeforeDag[loopHead]);
                else
                    backedgeNodeToLoopHead.Add(origToBeforeDag[block], new List<Block> {origToBeforeDag[loopHead]});
        }

        public IDictionary<Block, Block> AfterDagToOrig
        {
            set => _afterDagToOrig = value;
        }

        public bool TryIsBackedgeNode(Block block, out List<Block> loopHeadBlock)
        {
            return backedgeNodeToLoopHead.TryGetValue(block, out loopHeadBlock);
        }

        public void AddHint(Block block, LoopHeadHint hint)
        {
            loopHeadHints.Add(block, hint);
        }

        /// <param name="newBackedgeBlock">backedge block that is newly added in the CFG-to-DAG phase.</param>
        /// <param name="loopHead">corresponding loop head.</param>
        public void AddNewBackedgeBlock(Block newBackedgeBlock, Block loopHead)
        {
            newBackedgeNodesToLoopHead.Add(newBackedgeBlock, loopHead);
        }
        
        /// <param name="newPreLoopEntryBlock">pre loop entry block that is newly added in the CFG-to-DAG phase.</param>
        /// <param name="loopHead">corresponding loop head</param>
        public void AddNewPreLoopEntryBlock(Block newPreLoopEntryBlock, Block loopHead)
        {
            newPreLoopNodesToLoopHead.Add(newPreLoopEntryBlock, loopHead);
        }

        public bool IsNewBackedgeBlock(Block afterDagBlock, out LoopHeadHint loopHeadHint)
        {
            return IsNewBackedgeBlock(afterDagBlock, out _, out loopHeadHint);
        }

        public bool IsNewBackedgeBlock(Block afterDagBlock, out Block beforeDagLoopHead, out LoopHeadHint loopHeadHint)
        {
            if (newBackedgeNodesToLoopHead.TryGetValue(_afterDagToOrig[afterDagBlock], out var loopHeadOrig))
            {
                if (loopHeadHints.TryGetValue(loopHeadOrig, out loopHeadHint))
                {
                    loopHeadHint = loopHeadHints[loopHeadOrig];
                    beforeDagLoopHead = origToBeforeDag[loopHeadOrig];
                    return true;
                }

                throw new ProofGenUnexpectedStateException("Cannot find loop head for new backedge node.");
            }

            loopHeadHint = null;
            beforeDagLoopHead = null;
            return false;
        }
        
        public bool IsNewPreLoopEntryBlock(Block afterDagBlock)
        {
          return newPreLoopNodesToLoopHead.ContainsKey(_afterDagToOrig[afterDagBlock]);
        }

        public bool IsLoopHead(Block beforeDagBlock, out LoopHeadHint hint)
        {
            return loopHeadHints.TryGetValue(beforeDagToOrig[beforeDagBlock], out hint);
        }

        public LoopHeadHint GetLoopHead(Block beforeDagBlock)
        {
            return loopHeadHints[beforeDagToOrig[beforeDagBlock]];
        }
    }
}