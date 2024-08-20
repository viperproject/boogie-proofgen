using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Reflection;
using System.Runtime.InteropServices.ComTypes;
using ProofGenUtil;

using Core;

namespace Microsoft.Boogie
{
  public enum BranchIndicator
  {
    NoGuard,
    GuardHolds,
    GuardFails,
    LoopBody
  }

  /// <summary>
  /// A class used to collect information needed for the generation of the AST-to-CFG part of the validation certificate for a Boogie procedure.
  /// </summary>
  public class AstToCfgProofGenInfo
  {
    /// The original <see cref = "StmtList"/> object, which contains the original list of <see cref ="BigBlock" /> objects, which is Boogie's internal AST representation.
    private StmtList stmtList;

    private List<Variable> _unoptimizedLocalVars;

    public List<Variable> UnoptimizedLocalVars
    {
      get => _unoptimizedLocalVars;
      set => _unoptimizedLocalVars = value;
    }

    private bool _eliminatedDeadVars = false;

    public bool EliminatedDeadVars
    {
      get => _eliminatedDeadVars;
      set => _eliminatedDeadVars = value;
    }
    
    private IList<Block> unoptimizedBlocks;
    
    private List<Variable> newVarsAfterDesugaringinCFGBlocks;

    /// A list of copies of the <see cref="BigBlock"/> objects in <see cref="stmtList"/>.
    private IList<BigBlock> originalAst;

    /// A list containing the same <see cref ="BigBlock"/> objects, which are in <see cref ="originalAst"/> with all nested BigBlocks explicitly added.
    private IList<BigBlock> bigblocksBeforeNamingAnonymous;

    private IDictionary<Block, Block> mappingOrigBlocktoUnoptimizedCopy;

    // Dictionaries used to keep track of relations between different kinds of blocks. 
    private IDictionary<BigBlock, Block> mappingOrigBigBlockToOrigBlock;
    private IDictionary<BigBlock, BigBlock> mappingCopyBigblockToOrigBigblock;
    private IDictionary<BigBlock, BigBlock> mappingOrigBigblockToCopyBigblock;
    
    /** A dictionary mapping a 'LoopHead' BigBlock to a tuple of two BigBlocks.
      * A LoopHead is a special BigBlock that is a copy, has an empty list of simpleCmds and a <see cref="WhileCmd"/> as a <see cref="StructuredCmd"/>.
      * The key is the LoopHead.
      * The value is the original BigBlock the LoopHead Big Block was created from.
      */
    private IDictionary<BigBlock, BigBlock> mappingLoopHeadBigBlocktoOrigLoopBigBlock;
    
    // A marker set to false indicates that a BigBlock is nested in another BigBlock.
    private IDictionary<BigBlock, bool> mappingCopyBigBlockToMarker;
    
    /** The first hint is a guard (possibly null) that needs to be taken care of in the global lemma that's to be generated.
      * The second hint is a BranchIndicator that indicates how that needs to be done. */
    private IDictionary<BigBlock, (Expr, BranchIndicator)> mappingBigBlockToHints;

    // Map a BigBlock (copy) to the unique integer label (index) of its corresponding Term object (Term object definition is in InnerAst.cs).
    private IDictionary<BigBlock, int> mappingCopyBigBlockToIndex;

    // Map a BigBlock (original) to the Loop BigBlock (original) it's nested into.
    private IDictionary<BigBlock, BigBlock> mappingBigBlockToOrigLoopBigBlock;
    
    // List of BigBlocks added after a loop if that loop is the end of the procedure or if that loop has no successors.
    // I've never encountered an instance where this list contains more than one element, i.e, this doesn't need to be a list in our setting.
    // However, this depends on when successor Big Blocks are computed.
    // If successor BigBlocks were to be computed after the check on line 886 in AbsyCmd.cs is done,
    // then this list will contain a BigBlock corresponding to every loop. 
    private IList<BigBlock> loopEndingBlocks;

    private List<Variable> newVarsFromDesugaring;

    private bool optimizationsDone;

    public void InstantiateVars()
    {
      originalAst = new List<BigBlock>();
      bigblocksBeforeNamingAnonymous = new List<BigBlock>();

      mappingCopyBigBlockToMarker = new Dictionary<BigBlock, bool>();

      mappingOrigBigBlockToOrigBlock = new Dictionary<BigBlock, Block>();
      mappingCopyBigblockToOrigBigblock = new Dictionary<BigBlock, BigBlock>();
      mappingOrigBigblockToCopyBigblock = new Dictionary<BigBlock, BigBlock>();
      mappingLoopHeadBigBlocktoOrigLoopBigBlock = new Dictionary<BigBlock, BigBlock>();

      mappingBigBlockToHints = new Dictionary<BigBlock, (Expr, BranchIndicator)>();
      mappingCopyBigBlockToIndex = new Dictionary<BigBlock, int>();

      mappingBigBlockToOrigLoopBigBlock = new Dictionary<BigBlock, BigBlock>();
      newVarsFromDesugaring = new List<Variable>();

      loopEndingBlocks = new List<BigBlock>();
    }

    public void SetStmtList(StmtList stmtList)
    {
      this.stmtList = stmtList;
    }

    public StmtList GetStmtList()
    {
      return stmtList;
    }
    
    public void SetUnoptimizedBlocks(IList<Block> blocks)
    {
      unoptimizedBlocks = blocks;
    }

    public void SetOptimizationsFlag()
    {
      optimizationsDone = true;
    }

    public bool GetOptimizationsFlag()
    {
      return optimizationsDone;
    }
    
    public IList<Block> GetUnoptimizedBlocks()
    {
      return unoptimizedBlocks;
    }

    public void SetNewVarsCFG(List<Variable> newVars)
    {
      newVarsAfterDesugaringinCFGBlocks = newVars;
    }

    public List<Variable> GetNewVarsCFG()
    {
      return newVarsAfterDesugaringinCFGBlocks;
    }

    public IList<BigBlock> GetBigBlocks()
    {
      return bigblocksBeforeNamingAnonymous;
    }

    public IList<BigBlock> GetOriginalAst()
    {
      return originalAst;
    }

    public IDictionary<Block, Block> GetMappingOrigBlockToUnoptimizedCopy()
    {
      return mappingOrigBlocktoUnoptimizedCopy;
    }

    public IDictionary<BigBlock, bool> GetMappingCopyBigBlockToMarker()
    {
      return mappingCopyBigBlockToMarker;
    }

    public IDictionary<BigBlock, Block> GetMappingOrigBigBlockToOrigBlock()
    {
      return mappingOrigBigBlockToOrigBlock;
    }

    public IDictionary<BigBlock, BigBlock> GetMappingCopyBigblockToOrigBigblock()
    {
      return mappingCopyBigblockToOrigBigblock;
    }

    public IDictionary<BigBlock, BigBlock> GetMappingOrigBigblockToCopyBigblock()
    {
      return mappingOrigBigblockToCopyBigblock;
    }

    public IDictionary<BigBlock, BigBlock> GetMappingLoopHeadBigBlocktoOrigLoopBigBlock()
    {
      return mappingLoopHeadBigBlocktoOrigLoopBigBlock;
    }

    public IDictionary<BigBlock, (Expr, BranchIndicator)> GetMappingCopyBigBlockToHints()
    {
      return mappingBigBlockToHints;
    }

    public IDictionary<BigBlock, BigBlock> GetMappingBigBlockToLoopBigBlock()
    {
      return mappingBigBlockToOrigLoopBigBlock;
    }

    public IDictionary<BigBlock, int> GetMappingCopyBigBlockToIndex()
    {
      return mappingCopyBigBlockToIndex;
    }

    public IList<BigBlock> GetloopEndingBlocks()
    {
      return loopEndingBlocks;
    }

    public List<Variable> GetNewVarsFromDesugaring()
    {
      return newVarsFromDesugaring;
    }

    public void MakeOriginalAst(StmtList stmtList)
    {
      foreach (var bb in stmtList.BigBlocks)
      {
        BigBlock copy = mappingOrigBigblockToCopyBigblock[bb];
        originalAst.Add(copy);
      }
    }

    public void AddToOriginalAst(BigBlock b)
    {
      originalAst.Add(b);
    }

    /// <summary>
    /// Add a BigBlock to the <see cref="bigblocksBeforeNamingAnonymous"/> list and recursively add its nested BigBlocks.
    /// </summary>
    public void AddBigBlockBeforeNamingAnonymous(BigBlock b, bool marker, BigBlock parentBigBlockOrig,
      BigBlock parentBigBlockCopy, BranchIndicator branchIndicator)
    {
      BigBlock copy = null;
      switch (branchIndicator)
      {
        case BranchIndicator.NoGuard:
          
          //If the elseBlock field of an <see cref="IfCmd"/> is null, initialize it to a <see cref="StmtList"/> with one 'empty' BigBlock.
          FillEmptyElseBranches(b);
          
          copy = CopyBigBlock(b);
          mappingCopyBigblockToOrigBigblock.Add(copy, b);
          mappingOrigBigblockToCopyBigblock.Add(b, copy);
          mappingCopyBigBlockToMarker.Add(copy, marker);
          bigblocksBeforeNamingAnonymous.Add(copy);
          break;

        case BranchIndicator.GuardHolds:
        {
          IfCmd ifcmd = (IfCmd) parentBigBlockOrig.ec;
          int position = ifcmd.thn.BigBlocks.IndexOf(b);

          IfCmd ifcmdCopy = (IfCmd) parentBigBlockCopy.ec;
          BigBlock currentBigBlockCopy = ifcmdCopy.thn.BigBlocks[position];

          mappingCopyBigblockToOrigBigblock.Add(currentBigBlockCopy, b);
          mappingOrigBigblockToCopyBigblock.Add(b, currentBigBlockCopy);
          mappingCopyBigBlockToMarker.Add(currentBigBlockCopy, marker);
          bigblocksBeforeNamingAnonymous.Add(currentBigBlockCopy);

          copy = currentBigBlockCopy;
          break;
        }
        case BranchIndicator.GuardFails:
        {
          IfCmd ifcmd = (IfCmd) parentBigBlockOrig.ec;
          int position = ifcmd.elseBlock.BigBlocks.IndexOf(b);

          IfCmd ifcmdCopy = (IfCmd) parentBigBlockCopy.ec;
          BigBlock currentBigBlockCopy = ifcmdCopy.elseBlock.BigBlocks[position];

          mappingCopyBigblockToOrigBigblock.Add(currentBigBlockCopy, b);
          mappingOrigBigblockToCopyBigblock.Add(b, currentBigBlockCopy);
          mappingCopyBigBlockToMarker.Add(currentBigBlockCopy, marker);
          bigblocksBeforeNamingAnonymous.Add(currentBigBlockCopy);

          copy = currentBigBlockCopy;
          break;
        }
        case BranchIndicator.LoopBody:
        {
          WhileCmd wcmd = (WhileCmd) parentBigBlockOrig.ec;
          int position = wcmd.Body.BigBlocks.IndexOf(b);

          WhileCmd wcmdCopy = (WhileCmd) parentBigBlockCopy.ec;
          BigBlock currentBigBlockCopy = wcmdCopy.Body.BigBlocks[position];

          mappingCopyBigblockToOrigBigblock.Add(currentBigBlockCopy, b);
          mappingOrigBigblockToCopyBigblock.Add(b, currentBigBlockCopy);
          mappingCopyBigBlockToMarker.Add(currentBigBlockCopy, marker);
          bigblocksBeforeNamingAnonymous.Add(currentBigBlockCopy);

          copy = currentBigBlockCopy;
          break;
        }
        default:
          throw new ArgumentOutOfRangeException(nameof(branchIndicator), branchIndicator,
            "Unknown or Uninitialized Branch Indicator");
      }

      if (b.ec is IfCmd)
      {
        IfCmd ifcmd = (IfCmd) b.ec;
        foreach (BigBlock bb in ifcmd.thn.BigBlocks)
        {
          AddBigBlockBeforeNamingAnonymous(bb, false, b, copy, BranchIndicator.GuardHolds);
        }

        if (ifcmd.elseBlock != null)
        {
          foreach (BigBlock bb in ifcmd.elseBlock.BigBlocks)
          {
            AddBigBlockBeforeNamingAnonymous(bb, false, b, copy, BranchIndicator.GuardFails);
          }
        }
      }
      else if (b.ec is WhileCmd)
      {
        BigBlock simpleCmdsRemoved = new BigBlock(copy.tok, copy.LabelName, new List<Cmd>(), copy.ec, copy.tc);

        /*
         * This is a special case where the newly created LoopHead BigBlock is mapped to itself.
         * One could alternatively store the 'simpleCmdsRemoved' BigBlocks in a separate list but
         * then one would need an additional if-statement or a for-loop to access that list during the creation of continuations
         * and later on proofs.
         */
        mappingCopyBigblockToOrigBigblock.Add(simpleCmdsRemoved, simpleCmdsRemoved);
        mappingOrigBigblockToCopyBigblock.Add(simpleCmdsRemoved, simpleCmdsRemoved);
        
        mappingLoopHeadBigBlocktoOrigLoopBigBlock.Add(simpleCmdsRemoved, b);
        bigblocksBeforeNamingAnonymous.Add(simpleCmdsRemoved);
        mappingCopyBigBlockToMarker.Add(simpleCmdsRemoved, false);

        WhileCmd whilecmd = (WhileCmd) b.ec;
        foreach (BigBlock bb in whilecmd.Body.BigBlocks)
        {
          AddBigBlockBeforeNamingAnonymous(bb, false, b, copy, BranchIndicator.LoopBody);
        }
      }
    }

    public void AddBigBlockToLoopPair(BigBlock b0, BigBlock b1)
    {
      mappingBigBlockToOrigLoopBigBlock.Add(b0, b1);

      if (b0.ec is IfCmd ifcmd)
      {
        foreach (var thenBb in ifcmd.thn.BigBlocks)
        {
          AddBigBlockToLoopPair(thenBb, b1);
        }

        if (ifcmd.elseBlock != null)
        {
          foreach (var elseBb in ifcmd.elseBlock.BigBlocks)
          {
            AddBigBlockToLoopPair(elseBb, b1);
          }
        }
      }
    }

    public void AddBigBlockToBlockPair(BigBlock b0, Block b1)
    {
      mappingOrigBigBlockToOrigBlock.Add(b0, b1);
    }

    public void AddBigBlockToHintsPair(BigBlock b, (Expr, BranchIndicator) tuple)
    {
      mappingBigBlockToHints.Add(b, (tuple.Item1, tuple.Item2));
    }

    public void AddBigBlockToIndexPair(BigBlock b, int index)
    {
      mappingCopyBigBlockToIndex.Add(b, index);
    }

    /// <summary>
    ///   Make a copy of a BigBlock. The <see cref="Cmd"/> objects in its simpleCmds field and in the simpleCmds fields of its nested BigBlocks are not copied.
    /// </summary>
    public BigBlock CopyBigBlock(BigBlock b)
    {
      StructuredCmd ecCopy = null;
      if (b.ec is IfCmd)
      {
        IfCmd @if = (IfCmd) b.ec;

        IList<BigBlock> thenCopy = new List<BigBlock>();
        foreach (BigBlock bb in @if.thn.BigBlocks)
        {
          thenCopy.Add(CopyBigBlock(bb));
        }

        StmtList thenCopyStmts = new StmtList(thenCopy, @if.thn.EndCurly);

        IList<BigBlock> elseCopy = new List<BigBlock>();
        StmtList elseCopyStmts;
        if (@if.elseBlock == null)
        {
          elseCopyStmts = new StmtList(elseCopy, new Token());
        }
        else
        {
          foreach (BigBlock bb in @if.elseBlock.BigBlocks)
          {
            elseCopy.Add(CopyBigBlock(bb));
          }

          elseCopyStmts = new StmtList(elseCopy, @if.elseBlock.EndCurly);
        }

        ecCopy = new IfCmd(@if.tok, @if.Guard, thenCopyStmts, @if.elseIf, elseCopyStmts);
      }
      else if (b.ec is WhileCmd)
      {
        WhileCmd @while = (WhileCmd) b.ec;

        IList<BigBlock> bodyCopy = new List<BigBlock>();
        foreach (BigBlock bb in @while.Body.BigBlocks)
        {
          bodyCopy.Add(CopyBigBlock(bb));
        }

        StmtList bodyCopyStmts = new StmtList(bodyCopy, @while.Body.EndCurly);
        ecCopy = new WhileCmd(@while.tok, @while.Guard, @while.Invariants, bodyCopyStmts);
      }
      else
      {
        ecCopy = b.ec;
      }

      var copyCmds = new List<Cmd>();
      var newVarsFromDesugaring = new List<Variable>();
      foreach (var cmd in b.simpleCmds)
      {
        copyCmds.Add(cmd);
      }

      GetNewVarsFromDesugaring().AddRange(newVarsFromDesugaring);
      String nameCopy = b.LabelName != null ? "''" + b.LabelName + "''" : null;
      return new BigBlock(b.tok, nameCopy, copyCmds, ecCopy, b.tc);
    }

    /// <summary>
    ///   If the elseBlock field of an <see cref="IfCmd"/> is null, initialize it to a <see cref="StmtList"/> with one 'empty' BigBlock.
    ///   This is done, so that the AST-to-CFG part of the proof generation can properly generate a proof. 
    /// </summary>
    private void FillEmptyElseBranches(BigBlock b)
    {
      if (b.ec is IfCmd ifcmd)
      {
        foreach (var thenBb in ifcmd.thn.BigBlocks)
        {
          FillEmptyElseBranches(thenBb);
        }

        if (ifcmd.elseIf == null && ifcmd.elseBlock == null)
        {
          IList<BigBlock> emptyElseBranch = new List<BigBlock>();
          BigBlock emptyElseBranchBigBlock = new BigBlock(Token.NoToken, null, new List<Cmd>(), null, null);
          emptyElseBranch.Add(emptyElseBranchBigBlock);

          emptyElseBranchBigBlock.successorBigBlock = b.successorBigBlock;

          ifcmd.elseBlock = new StmtList(emptyElseBranch, Token.NoToken);
        }

        if (ifcmd.elseBlock != null)
        {
          foreach (var elseBb in ifcmd.elseBlock.BigBlocks)
          {
            FillEmptyElseBranches(elseBb);
          }
        }
      }
      else if (b.ec is WhileCmd wcmd)
      {
        foreach (var bodyBb in wcmd.Body.BigBlocks)
        {
          FillEmptyElseBranches(bodyBb);
        }
      }
    }

    public void RecordLoopDoneBlock(BigBlock loopDoneBigBlock)
    {
      loopEndingBlocks.Add(loopDoneBigBlock);
    }

    private bool InBigBlock(BigBlock bigBlockToBeChecked, BigBlock possibleContainerBigBlock)
    {
      if (possibleContainerBigBlock.ec is WhileCmd wcmd)
      {
        if (wcmd.Body.BigBlocks.Contains(bigBlockToBeChecked))
        {
          return true;
        }

        foreach (var bodyBb in wcmd.Body.BigBlocks)
        {
          if (InBigBlock(bigBlockToBeChecked, bodyBb))
          {
            return true;
          }
        }
      }
      else if (possibleContainerBigBlock.ec is IfCmd ifcmd)
      {
        if (ifcmd.thn.BigBlocks.Contains(bigBlockToBeChecked) ||
            ifcmd.elseBlock.BigBlocks.Contains(bigBlockToBeChecked))
        {
          return true;
        }

        foreach (var thenBb in ifcmd.thn.BigBlocks)
        {
          if (InBigBlock(bigBlockToBeChecked, thenBb))
          {
            return true;
          }
        }

        if (ifcmd.elseBlock != null)
        {
          foreach (var elseBb in ifcmd.elseBlock.BigBlocks)
          {
            if (InBigBlock(bigBlockToBeChecked, elseBb))
            {
              return true;
            }
          }
        }
      }

      return false;
    }
    
    private static readonly MethodInfo CloneMethod =
      typeof(object).GetMethod("MemberwiseClone", BindingFlags.NonPublic | BindingFlags.Instance);
    
    public IList<Block> CopyBlocks(
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
                ? ProofGenUtil.ObjectExtensions.Copy(cmd, t => t != typeof(IdentifierExpr) && t != typeof(TypeVariable) && t != typeof(QKeyValue))
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

        mappingOrigBlocktoUnoptimizedCopy = oldToNewBlock;
        return copyBlocks;
    }
    
    /// <summary>
    ///     Copy from <see cref="Implementation" />. We compute predecessors ourselves, since at certain points the
    ///     predecessors property for blocks is not in-sync with the CFG (and we do not want to adjust the Boogie
    ///     objects).
    /// </summary>
    public Dictionary<Block, List<Block>> ComputePredecessors(IEnumerable<Block> blocks)
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

    public void CreateBlockPairingWithHints(BigBlock bigblock, Block block, BranchIndicator branchIndicator, Expr guard)
    {
      if (!GetMappingOrigBigBlockToOrigBlock().ContainsKey(bigblock))
      {
        AddBigBlockToBlockPair(bigblock, block);

        if (!GetMappingCopyBigBlockToHints().ContainsKey(bigblock))
        {
          AddBigBlockToHintsPair(bigblock, (guard, branchIndicator)); 
        }
      }
    }
    
  }
}