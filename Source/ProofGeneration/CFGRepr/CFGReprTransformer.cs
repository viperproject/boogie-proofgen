using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Reflection;
using Microsoft.Boogie;
using ProofGeneration.Util;

namespace ProofGeneration.CFGRepresentation
{
    public static class CFGReprTransformer
    {
        private static readonly MethodInfo CloneMethod =
            typeof(object).GetMethod("MemberwiseClone", BindingFlags.NonPublic | BindingFlags.Instance);

        /// <summary>
        ///     Create CFG representation as <see cref="CFGRepr" /> of <paramref name="impl" />.
        /// </summary>
        /// <param name="impl">Input implementation.</param>
        /// <param name="config">Configuration specifying how to create representation.</param>
        /// <param name="newToOldBlocks">
        ///     Mapping from original to copied blocks if <paramref name="config" /> specifies blocks to
        ///     be copied.
        /// </param>
        /// <param name="newVarsFromDesugaring">
        ///     New local variables obtained from desugared commands if <paramref name="config" />
        ///     specifies calls to be desugared.
        /// </param>
        /// <returns>CFG Representation of implementation.</returns>
        /// <exception cref="ArgumentException"> Calls can only be desugared if blocks are specified to be copied.</exception>
        public static CFGRepr GetCfgRepresentation(
            Implementation impl,
            CFGReprConfig config,
            out IDictionary<Block, Block> newToOldBlocks,
            out List<Variable> newVarsFromDesugaring)
        {
            Contract.Requires(impl != null);
            Contract.Ensures(config.GenerateBlockCopy && newToOldBlocks != null ||
                             !config.GenerateBlockCopy && newToOldBlocks == null);
            if (!config.GenerateBlockCopy && config.DesugarCalls)
                throw new ArgumentException("Cannot desugar calls without generating copy of blocks");

            var predecessorMap = ComputePredecessors(impl.Blocks);
            IList<Block> blocksToConvert;
            Func<Block, List<Block>> predecessorFunc;

            if (config.GenerateBlockCopy)
            {
                blocksToConvert = CopyBlocks(impl.Blocks, predecessorMap, config.DesugarCalls,
                    config.DeepCopyCmdPred, out newVarsFromDesugaring);

                var newToOldInternal = new Dictionary<Block, Block>();
                blocksToConvert.ZipDo(impl.Blocks, (bNew, bOld) => newToOldInternal.Add(bNew, bOld));
                newToOldBlocks = newToOldInternal;
                predecessorFunc = b => b.Predecessors;
            }
            else
            {
                newVarsFromDesugaring = new List<Variable>();
                blocksToConvert = impl.Blocks;
                newToOldBlocks = null;
                predecessorFunc = b => predecessorMap[b];
            }

            AlternateCFGRepr(blocksToConvert, out var entryBlock, predecessorFunc, out var outgoingBlocks);
            IDictionary<Block, int> labeling;
            if (config.IsAcyclic)
            {
                labeling = GetTopologicalLabeling(blocksToConvert);
            }
            else
            {
                labeling = new Dictionary<Block, int>();
                var idx = 0;
                foreach (var b in blocksToConvert)
                {
                    labeling.Add(b, idx);
                    idx++;
                }
            }

            return new CFGRepr(outgoingBlocks, labeling, entryBlock);
        }

        private static void AlternateCFGRepr(
            IList<Block> blocks,
            out Block entryBlock,
            Func<Block, List<Block>> predecessorFunc,
            out IDictionary<Block, IList<Block>> outgoingBlocks)
        {
            entryBlock = null;
            outgoingBlocks = new Dictionary<Block, IList<Block>>();

            foreach (var block in blocks)
            {
                if (predecessorFunc(block).Count == 0)
                {
                    if (entryBlock != null)
                        throw new ProofGenUnexpectedStateException(typeof(CFGReprTransformer), "no unique CFG entry");
                    entryBlock = block;
                }

                var curOutgoing = new List<Block>();

                if (block.TransferCmd is GotoCmd gotoCmd) curOutgoing.AddRange(gotoCmd.labelTargets);

                outgoingBlocks.Add(block, curOutgoing);
            }

            if (entryBlock == null)
                throw new ProofGenUnexpectedStateException(typeof(CFGReprTransformer), "no CFG entry");
        }


        /// <summary>
        ///     Copy from <see cref="Implementation" />. We compute predecessors ourselves, since at certain points the
        ///     predecessors property for blocks is not in-sync with the CFG (and we do not want to adjust the Boogie
        ///     objects).
        /// </summary>
        private static Dictionary<Block, List<Block>> ComputePredecessors(IEnumerable<Block> blocks)
        {
            var predecessors = new Dictionary<Block, List<Block>>();
            foreach (var b in blocks) predecessors.Add(b, new List<Block>());

            foreach (var b in blocks)
            {
                var gtc = b.TransferCmd as GotoCmd;
                if (gtc != null)
                {
                    Contract.Assert(gtc.labelTargets != null);
                    foreach (var /*!*/ dest in gtc.labelTargets)
                    {
                        Contract.Assert(dest != null);
                        predecessors[dest].Add(b);
                    }
                }
            }

            return predecessors;
        }

        public static IDictionary<Block, int> GetTopologicalLabeling(IList<Block> blocks)
        {
            Contract.Requires(blocks != null);
            Contract.Ensures(blocks.Count == Contract.Result<IDictionary<Block, int>>().Count);
            Contract.Ensures(Contract.Result<IDictionary<Block, int>>().Values.Min() == 0 &&
                             Contract.Result<IDictionary<Block, int>>().Values.Max() == blocks.Count - 1);

            //adusted code from VC.cs
            var dag = GraphUtil.GraphFromBlocks(blocks, true);
            var sortedNodes = dag.TopologicalSort();
            Contract.Assert(sortedNodes != null);

            var retLabels = new Dictionary<Block, int>();

            var curLabel = 0;
            foreach (var block in sortedNodes)
            {
                retLabels.Add(block, curLabel);
                curLabel++;
            }

            return retLabels;
        }

        /// <summary>
        ///     Makes a shallow copy of <paramref name="blocks" />. The predecessors of <paramref name="blocks" /> is set
        ///     correctly.
        /// </summary>
        private static IList<Block> CopyBlocks(
            IList<Block> blocks,
            Dictionary<Block, List<Block>> predecessorMap,
            bool desugarCalls,
            Predicate<Cmd> deepCopyCmdPred,
            out List<Variable> newVarsFromDesugaring)
        {
            //shallow copy of each block + update edges to copied blocks + deep copy of cmds if specified
            //TODO:  need to make sure this is sufficient
            IDictionary<Block, Block> oldToNewBlock = new Dictionary<Block, Block>();

            IList<Block> copyBlocks = new List<Block>();

            newVarsFromDesugaring = new List<Variable>();

            //don't copy variables, since proof generation assumes sharing of variable identities
            Func<Cmd, Cmd> copyCmd = cmd =>
                deepCopyCmdPred(cmd)
                    ? cmd.Copy(t => t != typeof(IdentifierExpr) && t != typeof(TypeVariable) && t != typeof(QKeyValue))
                    : (Cmd) CloneMethod.Invoke(cmd, null);

            foreach (var b in blocks)
            {
                var copyCmds = new List<Cmd>();
                foreach (var cmd in b.Cmds)
                    if (cmd is SugaredCmd sugaredCmd && desugarCalls)
                    {
                        var stateCmd = sugaredCmd.Desugaring as StateCmd;
                        newVarsFromDesugaring.AddRange(stateCmd.Locals);
                        foreach (var desugaredCmd in stateCmd.Cmds) copyCmds.Add(copyCmd(desugaredCmd));
                    }
                    else
                    {
                        copyCmds.Add(copyCmd(cmd));
                    }

                var copyBlock = (Block) CloneMethod.Invoke(b, null);
                copyBlock.Cmds = copyCmds;
                copyBlock.Predecessors = predecessorMap[b];

                copyBlocks.Add(copyBlock);
                oldToNewBlock.Add(b, copyBlock);
            }

            //make sure block references are updated accordingly
            foreach (var copyBlock in copyBlocks)
            {
                if (copyBlock.TransferCmd is GotoCmd gtc)
                {
                    var newSuccessors = gtc.labelTargets.Select(succ => oldToNewBlock[succ]).ToList();
                    var gotoCmdCopy = (GotoCmd) CloneMethod.Invoke(gtc, null);
                    gotoCmdCopy.labelTargets = newSuccessors;
                    copyBlock.TransferCmd = gotoCmdCopy;
                }
                else
                {
                    copyBlock.TransferCmd = (TransferCmd) CloneMethod.Invoke(copyBlock.TransferCmd, null);
                }

                if (copyBlock.Predecessors != null)
                    copyBlock.Predecessors = copyBlock.Predecessors.Select(succ => oldToNewBlock[succ]).ToList();
            }

            return copyBlocks;
        }
    }
}