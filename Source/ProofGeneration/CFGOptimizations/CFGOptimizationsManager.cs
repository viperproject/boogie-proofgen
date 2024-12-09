using Isabelle.Ast;
using ProofGeneration.BoogieIsaInterface;
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.PhasesUtil;
using ProofGeneration.Util;
using ProofGenUtil;


namespace ProofGeneration.CFGOptimizations;

public class CfgOptimizationsManager
{
  
  public static Theory CfgOptProof(
    PhasesTheories phasesTheories,
    EndToEndLemmaConfig endToEndLemmaConfig,
    CFGRepr beforeOptimizations,
    CFGRepr afterOptimizations,
    IDictionary<Block, Block> beforeToAfter, // mapping from current block to target block
    IProgramAccessor beforeOptCfgProgAccess, //before CFG optimizations
    IProgramAccessor afterOptCfgProgAccess, //after CFG optimizationsList
    IDictionary<Block, BlockCoalescingInfo> ListCoalescedBlocks, 
    IDictionary<Block, Block> CoalescedBlocksToTarget,
    IDictionary<Block, IList<Block>> beforeDagBlockToLoops,
    Term vcAssm,
    string procedureName,
    bool generateCfgDagProof,
    IDictionary<Block, Block> selfLoops)
  {
    IDictionary<Block, Block> afterToBefore = beforeToAfter.ToDictionary(x => x.Value, x => x.Key);
    IDictionary<Block, IList<Block>> beforeOptBlockToLoops = new Dictionary<Block, IList<Block>>();
    Block coalescedAfterBlock = new Block();
    ISet<Block> loopHeadsSet = new HashSet<Block>();
    IDictionary<Block, Block> selfLoopsNew = new Dictionary<Block, Block>();
    
    
    foreach (Block beforeBlock in beforeOptimizations.GetBlocksForwards())
    {
      if (beforeToAfter.ContainsKey(beforeBlock))
      {
        IList<Block> temp = new List<Block>();
        foreach (Block loopHeader in beforeDagBlockToLoops[beforeToAfter[beforeBlock]])
        {
          temp.Add(afterToBefore[loopHeader]);
          loopHeadsSet.Add(afterToBefore[loopHeader]);
        }
        beforeOptBlockToLoops.Add(beforeBlock, temp);
        if (selfLoops.ContainsKey(beforeToAfter[beforeBlock]))
        {
          selfLoopsNew.Add(beforeBlock, beforeBlock);
          loopHeadsSet.Add(beforeBlock);
        }
      }
      else if (CoalescedBlocksToTarget.ContainsKey(beforeBlock)) {
        coalescedAfterBlock = CoalescedBlocksToTarget[beforeBlock];
        List<Block> temp = new List<Block>();
        foreach (Block loopHeader in beforeDagBlockToLoops[coalescedAfterBlock])
        {
          temp.Add(afterToBefore[loopHeader]);
          loopHeadsSet.Add(afterToBefore[loopHeader]);
        }

        foreach (Block afterSucc in afterOptimizations.GetSuccessorBlocks(
                   CoalescedBlocksToTarget[beforeBlock]))
        {
          if (beforeDagBlockToLoops[coalescedAfterBlock].Count < beforeDagBlockToLoops[afterSucc].Count)
          {
            temp.Add(afterToBefore[CoalescedBlocksToTarget[beforeBlock]]);
            loopHeadsSet.Add(afterToBefore[CoalescedBlocksToTarget[beforeBlock]]);
            break;
          }
        }
        if (selfLoops.ContainsKey(coalescedAfterBlock))
        {
          temp.Add(afterToBefore[coalescedAfterBlock]);
          loopHeadsSet.Add(afterToBefore[coalescedAfterBlock]);
        }
        beforeOptBlockToLoops.Add(beforeBlock, temp);

      }
    }
    
    
    var varContextName = "\\<Lambda>";

    var funContextWfName = "Wf_Fun";
    
    var boogieContext = new BoogieContextIsa(
      IsaCommonTerms.TermIdentFromName("A"),
      IsaCommonTerms.TermIdentFromName("M"),
      IsaCommonTerms.TermIdentFromName(varContextName),
      IsaCommonTerms.TermIdentFromName("\\<Gamma>"),
      IsaCommonTerms.TermIdentFromName("\\<Omega>"));


    var lemmaManager = new CFGOptimizationsLemmaManager(
      beforeOptCfgProgAccess,
      afterOptCfgProgAccess,
      beforeOptimizations,
      afterOptimizations,
      funContextWfName,
      boogieContext,
      beforeToAfter);

    var lemmaNamer = new IsaUniqueNamer();
    var outerDecls = new List<OuterDecl>();
    
    
    outerDecls.Add(new DeclareDecl("Nat.One_nat_def[simp del]"));


    CFGRepr beforeOptimizationsCopy = beforeOptimizations.Copy();
    beforeOptimizationsCopy.DeleteBackedges(beforeOptBlockToLoops, selfLoopsNew);

    List<Block> topoOrder = new List<Block>();
    TopologicalOrder(topoOrder, beforeOptimizationsCopy);
    topoOrder.Reverse();

    foreach (var beforeBlock in topoOrder)
    {

      if (loopHeadsSet.Contains(beforeBlock) && CoalescedBlocksToTarget.ContainsKey(beforeBlock)) //In this case we have a coalesced loop head
      {
        coalescedAfterBlock = CoalescedBlocksToTarget[beforeBlock];
        var globalBlock = lemmaManager.LoopHeadCoalesced(beforeBlock, coalescedAfterBlock,
          bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
          bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer),
          beforeOptBlockToLoops[beforeBlock], ListCoalescedBlocks);
        outerDecls.Add(globalBlock);
      } 
      else if (loopHeadsSet.Contains(beforeBlock)) //normal Loop Head
      {
        var globalBlock = lemmaManager.LoopHeadNotCoalesced(beforeBlock, beforeToAfter[beforeBlock], bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops, beforeOptBlockToLoops[beforeBlock], loopHeadsSet);
        outerDecls.Add(globalBlock);
      }
      else if (CoalescedBlocksToTarget.ContainsKey(beforeBlock)) //in this case we have block coalescing
      {
        if (ProgramToVCProof.LemmaHelper.FinalStateIsMagic(beforeBlock)) //Pruning of Unreachable Blocks Coalesced
        {
          coalescedAfterBlock = CoalescedBlocksToTarget[beforeBlock];
          var pruningCoalesced = lemmaManager.HybridBlockLemmaPruning(beforeBlock, coalescedAfterBlock,
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
          outerDecls.Add(pruningCoalesced);
        }
        else if (beforeToAfter.ContainsKey(beforeBlock)) //Head of coalesced blocks
        {
          Block afterBlock = beforeToAfter[beforeBlock];
          var head = lemmaManager.HybridBlockLemma(beforeBlock, afterBlock,
            beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault(),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock],
            ListCoalescedBlocks);
          outerDecls.Add(head);
          var convertGlobalBlock = lemmaManager.ConvertHybridToGlobal(beforeBlock, afterBlock,
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock],
            ListCoalescedBlocks);
          outerDecls.Add(convertGlobalBlock);
        }
        else if (ListCoalescedBlocks[beforeBlock].coalescedBlocks.Count == ListCoalescedBlocks[beforeBlock].idx + 1) //tail of coalesced blocks
        {
          coalescedAfterBlock = CoalescedBlocksToTarget[beforeBlock];
          
          var tail = lemmaManager.HybridBlockLemmaTail(beforeBlock, coalescedAfterBlock,
            bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), 
            beforeOptBlockToLoops, beforeOptBlockToLoops[beforeBlock], loopHeadsSet);
          outerDecls.Add(tail);
        }
        else //in Between Block
        {
          coalescedAfterBlock = CoalescedBlocksToTarget[beforeBlock];
          var inBetweenBlock = lemmaManager.HybridBlockLemma(beforeBlock, coalescedAfterBlock,
            beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault(),
            bigblock => GetHybridBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops[beforeBlock],
            ListCoalescedBlocks);
          outerDecls.Add(inBetweenBlock);
        }
      }
      else //no block coalescing
      {
        if (beforeToAfter.Keys.Contains(beforeBlock))
        {
          Block afterBlock = beforeToAfter[beforeBlock];
          if (ProgramToVCProof.LemmaHelper.FinalStateIsMagic(beforeBlock)) //If there is an assume or assert false statement in the block
          {
            var pruning = lemmaManager.GlobalBlockLemmaPruningNotCoalesced(beforeBlock, afterBlock, GetGlobalBlockLemmaName(beforeBlock, lemmaNamer), beforeOptBlockToLoops[beforeBlock]);
            outerDecls.Add(pruning);
          }
          else //otherwhise we just need to apply the normal global block lemma. Assumption: Global Block Lemma holds for all successors
          {
            var globalBlock = lemmaManager.GlobalBlockLemma(beforeBlock, afterBlock, bigblock => GetGlobalBlockLemmaName(bigblock, lemmaNamer), beforeOptBlockToLoops, beforeOptBlockToLoops[beforeBlock], loopHeadsSet);
            outerDecls.Add(globalBlock);
          }
        }
      }
    }

    var entryLemma = lemmaManager.EntryLemma("entry_lemma",
      GetGlobalBlockLemmaName(beforeOptimizations.entry, lemmaNamer), beforeOptimizations.entry,
      afterOptimizations.entry);
    outerDecls.Add(entryLemma);
    if (endToEndLemmaConfig != EndToEndLemmaConfig.DoNotGenerate)
    {
      var endToEndManager = new CFGOptimizationsEndToEnd();
      var endToEndDecls = endToEndManager.EndToEndProof(
        "entry_lemma",
        endToEndLemmaConfig,
        vcAssm,
        beforeOptCfgProgAccess,
        afterOptCfgProgAccess,
        beforeOptCfgProgAccess,
        afterOptimizations,
        phasesTheories,
        procedureName
      );
      outerDecls.AddRange(endToEndDecls);
    }


    List<string> importTheories = new List<string>
    {
      "Boogie_Lang.Semantics", "Boogie_Lang.Util", "Boogie_Lang.CFGOptimizationsLoop",
      afterOptCfgProgAccess.TheoryName(),
      beforeOptCfgProgAccess.TheoryName()
    };
    if (generateCfgDagProof)
    {
      importTheories.Add(phasesTheories.TheoryName(PhasesTheories.Phase.CfgToDag));
    }
    
    
    return new Theory(
      phasesTheories.TheoryName(PhasesTheories.Phase.CfgOptimizations),
      importTheories,
      outerDecls
    ); 
  }
  
  private static string GetGlobalBlockLemmaName(Block b, IsaUniqueNamer namer)
  {
    return "global_block_lemma_" + namer.GetName(b, "block_" + b.Label);
  }
  
  private static string GetHybridBlockLemmaName(Block b, IsaUniqueNamer namer)
  {
    return "hybrid_block_lemma_" + namer.GetName(b, "block_" + b.Label);
  }

  
  
  
  
  
  

  private static void TopologicalOrder(List<Block> topoOrder, CFGRepr beforeOptimizationsCopy)
  {
    Dictionary<Block, int> inDegree = new Dictionary<Block, int>();
    foreach (var b in beforeOptimizationsCopy.GetBlocksForwards())
    {
      inDegree.Add(b, b.Predecessors.Count());
    }
    
    Queue<Block> q = new Queue<Block>();
    foreach (var b in beforeOptimizationsCopy.GetBlocksForwards())
    {
      if (inDegree[b] == 0)
      {
        q.Enqueue(b);
      }
    }

    while (q.Count > 0)
    {
      Block u = q.Dequeue();
      topoOrder.Add(u);
      foreach (var b in beforeOptimizationsCopy.GetSuccessorBlocks(u))
      {
        if (--inDegree[b] == 0)
        {
          q.Enqueue(b);
        }
      }
      
    }
    
    
  }

  
}