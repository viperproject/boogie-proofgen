using Isabelle.Ast;
using ProofGeneration.BoogieIsaInterface;
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;


namespace ProofGeneration.CFGOptimizations;

public class CFGOptimizationsLemmaManager
{
  private readonly IProgramAccessor beforeOptProgAccess;
  private readonly IProgramAccessor afterOptProgAccess;
  private readonly CFGRepr beforeOptimizations;
  private readonly CFGRepr afterOptimizations;
  private readonly string funContextWfName;
  private readonly IDictionary<Block, Block> beforeToAfterBlock;
  private readonly BoogieContextIsa boogieContext;
  public CFGOptimizationsLemmaManager(
    IProgramAccessor beforeOptProgAccess,
    IProgramAccessor afterOptProgAccess,
    CFGRepr beforeOptimizations,
    CFGRepr afterOptimizations,
    string funContextWfName,
    BoogieContextIsa boogieContext,
    IDictionary<Block, Block> beforeToAfterBlock
  )
  {
    this.beforeOptProgAccess = beforeOptProgAccess;
    this.afterOptProgAccess = afterOptProgAccess;
    this.beforeOptimizations = beforeOptimizations;
    this.afterOptimizations = afterOptimizations;
    this.funContextWfName = funContextWfName;
    this.boogieContext = boogieContext;
    this.beforeToAfterBlock = beforeToAfterBlock;
  }

  public LemmaDecl GlobalBlockLemmaPruningNotCoalesced( //Pruning of unreachable blocks where no coalescing happened
    Block beforeBlock,
    Block afterBlock,
    string blockLemmaName,
    IList<Block> Loops)
  {
    
    var proofMethods = new List<string>
    {
      "apply (rule pruning_not_coalesced_loop)",
      "apply (rule " + beforeOptProgAccess.BlockInfo().OutEdgesMembershipLemma(beforeBlock) + ")",
      "apply (rule " + afterOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterBlock) + ")",
      "apply (rule " + beforeOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(beforeBlock) + ")",
      "apply (unfold " + beforeOptProgAccess.BlockInfo().CmdsQualifiedName(beforeBlock) + "_def)",
      "apply simp",
      "apply (unfold " + afterOptProgAccess.BlockInfo().CmdsQualifiedName(afterBlock) + "_def)",
      "apply simp"
    };
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() == 0)
    {
      proofMethods.Add("by (rule " + afterOptProgAccess.BlockInfo().OutEdgesMembershipLemma(afterBlock) + ")");
    }
    else
    {
      proofMethods.Add("by simp");
    }
    
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }

    Term conclusion = getConclusion(loopHeads, "global_block_lemma_loop", beforeBlock, afterBlock, beforeOptProgAccess,
      afterOptProgAccess, false, null);


    var blockLemma = new LemmaDecl(
      blockLemmaName, 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl GlobalBlockLemma( //normal global block lemma where the global block lemma needs to hold for all successors
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> blockLemmaName,
    IDictionary<Block, IList<Block>> beforeOptBlockToLoops,
    IList<Block> Loops,
    ISet<Block> loopHeadsSet)
  {
    
    
    
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    var function = new List<string>();
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (beforeToAfterBlock.Keys.Contains(succ))
      {
        Block succAfter = beforeToAfterBlock[succ];
        function.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[succ] + "," + afterOptProgAccess.BlockInfo().BlockIds[succAfter] + ")");
      }
    }
    var proofMethods = new List<string>
    {
      "apply (rule loopBlock_global_block[where ?f = \"the \\<circ> map_of [" + string.Join(",", function) + "]\"])",
      "apply (rule " + beforeOptProgAccess.BlockInfo().OutEdgesMembershipLemma(beforeBlock) + ")",
      "apply simp"
    };
    int countCases = 0;
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (loopHeadsSet.Contains(succ)  && Loops.Contains(succ))
      {
        countCases = countCases + 1;
      }
    }

    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1 && beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() - countCases > 1) 
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (Loops.Count == 0)
      {
        proofMethods.Add("apply (rule " + blockLemmaName(succ) + ")");
      }
      else if (!(loopHeadsSet.Contains(succ) && Loops.Contains(succ)))
      {
        var loopHeadsSucc = new List<string>();
        foreach (Block loop in beforeOptBlockToLoops[succ])
        {
          loopHeadsSucc.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
        }
        proofMethods.Add("apply(rule exI[where ?x = \"{" + string.Join(",", loopHeadsSucc) + "}\"])");
        proofMethods.Add("apply simp");
        proofMethods.Add("apply (rule " +blockLemmaName(succ) + ")");
      }
      
      
    }
    proofMethods.Add("apply simp");
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 0)
    {
      proofMethods.Add("apply (unfold " + afterOptProgAccess.BlockInfo().OutEdgesMembershipLemma(afterBlock) + ")");
    }
      
      
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1)
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      proofMethods.Add("apply simp");
    }
    
    proofMethods.Add("apply (rule " + afterOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterBlock) + ")");
    proofMethods.Add("apply (rule " + beforeOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(beforeBlock) + ")");
    proofMethods.Add("apply (unfold " + afterOptProgAccess.BlockInfo().CmdsQualifiedName(afterBlock) + "_def " +
                                     beforeOptProgAccess.BlockInfo().CmdsQualifiedName(beforeBlock) + "_def)");
    proofMethods.Add("apply simp");
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() == 0)
    {
      proofMethods.Add("by (rule " + afterOptProgAccess.BlockInfo().OutEdgesMembershipLemma(afterBlock) + ")");
    }
    else
    {
      proofMethods.Add("by simp");
    }
    
    Term conclusion = getConclusion(loopHeads, "global_block_lemma_loop", beforeBlock, afterBlock, beforeOptProgAccess,
      afterOptProgAccess, false, null);
      
    var blockLemma = new LemmaDecl(
      blockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }
  public LemmaDecl HybridBlockLemmaTail( //show the hybrid block lemma for the tail of coalesced blocks
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> GlobalblockLemmaName,
    Func<Block, string> HybridblockLemmaName,
    IDictionary<Block, IList<Block>> beforeOptBlockToLoops,
    IList<Block> Loops,
    ISet<Block> loopHeadsSet)
  {
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    var function = new List<string>();
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (beforeToAfterBlock.Keys.Contains(succ))
      {
        Block succAfter = beforeToAfterBlock[succ];
        function.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[succ] + "," + afterOptProgAccess.BlockInfo().BlockIds[succAfter] + ")");
      }
    }

    var proofMethods = new List<string>
    {

      "apply (rule loopBlock_global_block_hybrid[where ?f = \"the \\<circ> map_of [" + string.Join(",", function) + "]\"])",
      "apply (rule " + beforeOptProgAccess.BlockInfo().OutEdgesMembershipLemma(beforeBlock) + ")",
      "apply simp"
    };
    int countCases = 0;
    
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (loopHeadsSet.Contains(succ) && Loops.Contains(succ))
      {
        countCases++;
      }
    }

    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1 && beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() - countCases > 1) 
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (Loops.Count == 0)
      {
        proofMethods.Add("apply (rule " + GlobalblockLemmaName(succ) + ")");
      }
      else if (!(loopHeadsSet.Contains(succ) && Loops.Contains(succ)))
      {
        var loopHeadsSucc = new List<string>();
        foreach (Block loop in beforeOptBlockToLoops[succ])
        {
          loopHeadsSucc.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
        }
        proofMethods.Add("apply(rule exI[where ?x = \"{" + string.Join(",", loopHeadsSucc) + "}\"])");
        proofMethods.Add("apply simp");
        proofMethods.Add("apply (rule " + GlobalblockLemmaName(succ) + ")");
      }
    }
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 0)
    {
      proofMethods.Add("apply simp");
      proofMethods.Add("apply (unfold " + afterOptProgAccess.BlockInfo().OutEdgesMembershipLemma(afterBlock) + ")");
    }
    
    proofMethods.Add("apply simp");
    
    proofMethods.Add("apply (unfold " + beforeOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(beforeBlock) + " " + beforeOptProgAccess.BlockInfo().CmdsQualifiedName(beforeBlock) + "_def)");
    proofMethods.Add("apply simp");
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() == 0)
    {
      proofMethods.Add("by (rule " + afterOptProgAccess.BlockInfo().OutEdgesMembershipLemma(afterBlock) + ")");
    }
    else
    {
      proofMethods.Add("by simp");
    }
    List<String> listCoalescedBlocks = new List<String>();
    listCoalescedBlocks.Add(beforeOptProgAccess.BlockInfo().CmdsQualifiedName(beforeBlock));
    
    
    Term conclusion = getConclusion(loopHeads, "hybrid_block_lemma_loop", beforeBlock, afterBlock, beforeOptProgAccess,
      afterOptProgAccess, true, listCoalescedBlocks);
    
    
    var blockLemma = new LemmaDecl(
      HybridblockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl HybridBlockLemma( //extend hybrid block lemma
    Block beforeBlock,
    Block afterBlock,
    Block succ,
    Func<Block, string> HybridblockLemmaName,
    IList<Block> Loops,
    IDictionary<Block, BlockCoalescingInfo> ListCoalescedBlocks)
  {
    var proofMethods = new List<string>
    {
      "apply (rule extend_hybrid_global_block_lemma_loop)",
      "apply (rule " + HybridblockLemmaName(succ) + ")",
      "apply (rule " + beforeOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(beforeBlock) + ")",
      "apply (rule " + beforeOptProgAccess.BlockInfo().OutEdgesMembershipLemma(beforeBlock) + ")",
      "by simp"
    };
    
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    int i = ListCoalescedBlocks[beforeBlock].idx;
    List<Block> coalescedBlocks = ListCoalescedBlocks[beforeBlock].coalescedBlocks;

    List<String> listCoalescedBlocks = new List<String>();
    foreach (Block current in coalescedBlocks.GetRange(i, coalescedBlocks.Count - i))
    {
      listCoalescedBlocks.Add(beforeOptProgAccess.BlockInfo().CmdsQualifiedName(current));
    }

    
    
    Term conclusion = getConclusion(loopHeads, "hybrid_block_lemma_loop", beforeBlock, afterBlock, beforeOptProgAccess,
      afterOptProgAccess, true, listCoalescedBlocks);
    
    var blockLemma = new LemmaDecl(
      HybridblockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl ConvertHybridToGlobal( //show the hybrid block lemma for the head of coalesced blocks
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> GlobalblockLemmaName,
    Func<Block, string> HybridblockLemmaName,
    IList<Block> Loops,
    IDictionary<Block, BlockCoalescingInfo> ListCoalescedBlocks)
  {
    var proofMethods = new List<string>
    {
      "apply (rule convert_hybrid_global_block_lemma_loop)",
      "apply (rule " + HybridblockLemmaName(beforeBlock) + ")"
    };
    
    int i = ListCoalescedBlocks[beforeBlock].idx;
    List<Block> coalescedBlocks = ListCoalescedBlocks[beforeBlock].coalescedBlocks;
    List<String> listCoalescedBlocks = new List<String>();
    foreach (Block current in coalescedBlocks.GetRange(i, coalescedBlocks.Count - i))
    {
      listCoalescedBlocks.Add(beforeOptProgAccess.BlockInfo().CmdsQualifiedName(current));
    }
    

    foreach (string b in listCoalescedBlocks)
    {
      proofMethods.Add("apply (unfold " + b + "_def)");
    }
    proofMethods.Add("apply (unfold " + afterOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterBlock) + " " + afterOptProgAccess.BlockInfo().CmdsQualifiedName(afterBlock) + "_def)");
    proofMethods.Add("by simp");
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    
    Term conclusion = getConclusion(loopHeads, "global_block_lemma_loop", beforeBlock, afterBlock, beforeOptProgAccess,
      afterOptProgAccess, false, null);
    
    var blockLemma = new LemmaDecl(
      GlobalblockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl HybridBlockLemmaPruning( //Pruning of unreachable blocks with block coalescing
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> blockLemmaName,
    IList<Block> Loops)
  {
    var proofMethods = new List<string>
    {
      "apply (rule pruning_coalesced_loop)",
      "apply (rule " + afterOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterBlock) + ")",
      "apply (unfold " + beforeOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(beforeBlock) + ")",
      "apply (unfold " + beforeOptProgAccess.BlockInfo().CmdsQualifiedName(beforeBlock) + "_def)",
      "apply simp",
      "apply simp",
      "apply (unfold " + afterOptProgAccess.BlockInfo().CmdsQualifiedName(afterBlock) + "_def)",
      "apply simp"
    };
    proofMethods.Add("apply (unfold " + afterOptProgAccess.BlockInfo().OutEdgesMembershipLemma(afterBlock) + ")");
    proofMethods.Add("apply (unfold " + beforeOptProgAccess.BlockInfo().OutEdgesMembershipLemma(beforeBlock) + ")");
    proofMethods.Add("by simp");
    
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    
    List<string> listCoalescedBlocks = new List<string>();
    listCoalescedBlocks.Add(beforeOptProgAccess.BlockInfo().CmdsQualifiedName(beforeBlock));

    Term conclusion = getConclusion(loopHeads, "hybrid_block_lemma_loop", beforeBlock, afterBlock, beforeOptProgAccess,
      afterOptProgAccess, true, listCoalescedBlocks);
    
    var blockLemma = new LemmaDecl(
      blockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl LoopHeadNotCoalesced( //Loop Head uncoalesced
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> blockLemmaName,
    IDictionary<Block, IList<Block>> beforeOptBlockToLoops,
    IList<Block> Loops,
    ISet<Block> loopHeadsSet)
  {
    
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }
    
    var function = new List<string>();
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (beforeToAfterBlock.Keys.Contains(succ))
      {
        Block succAfter = beforeToAfterBlock[succ];
        function.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[succ] + "," + afterOptProgAccess.BlockInfo().BlockIds[succAfter] + ")");
      }
    }
    var proofMethods = new List<string>
    {
      "apply (rule loopHead_global_block[where ?f = \"the \\<circ> map_of [" + string.Join(",", function) + "]\"])",
      "apply (rule " + beforeOptProgAccess.BlockInfo().OutEdgesMembershipLemma(beforeBlock) + ")",
      "apply simp"
    };
    
    int countCases = 0;
    
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (loopHeadsSet.Contains(succ) && Loops.Contains(succ))
      {
        countCases++;
      }
    }

    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1 && beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() - countCases > 1) 
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      if (!(loopHeadsSet.Contains(succ) && Loops.Contains(succ)))
      {
        var loopHeadsSucc = new List<string>();
        foreach (Block loop in beforeOptBlockToLoops[succ])
        {
          loopHeadsSucc.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
        }
        proofMethods.Add("apply(rule exI[where ?x = \"{" + string.Join(",", loopHeadsSucc) + "}\"])");
        proofMethods.Add("apply simp");
        proofMethods.Add("apply (rule " + blockLemmaName(succ) + ")");
      }

    }
    proofMethods.Add("apply simp");
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 0)
    {
      proofMethods.Add("apply (unfold " + afterOptProgAccess.BlockInfo().OutEdgesMembershipLemma(afterBlock) + ")");
    }
      
      
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() > 1)
    {
      proofMethods.Add("apply (intro conjI)");
    }
    foreach (Block succ in beforeOptimizations.GetSuccessorBlocks(beforeBlock))
    {
      proofMethods.Add("apply simp");
    }
    proofMethods.Add("apply (rule " + afterOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterBlock) + ")");
    proofMethods.Add("apply (rule " + beforeOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(beforeBlock) + ")");
    proofMethods.Add("apply (unfold "+ afterOptProgAccess.BlockInfo().CmdsQualifiedName(afterBlock) + "_def " + beforeOptProgAccess.BlockInfo().CmdsQualifiedName(beforeBlock) + "_def)");
    proofMethods.Add("apply simp");
    if (beforeOptimizations.GetSuccessorBlocks(beforeBlock).Count() == 0)
    {
      proofMethods.Add("by (rule " + afterOptProgAccess.BlockInfo().OutEdgesMembershipLemma(afterBlock) + ")");
    }
    else
    {
      proofMethods.Add("by simp");
    }
    
    Term conclusion = getConclusion(loopHeads, "global_block_lemma_loop", beforeBlock, afterBlock, beforeOptProgAccess,
      afterOptProgAccess, false, null);
      
    var blockLemma = new LemmaDecl(
      blockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl LoopHeadCoalesced( //Loop Head coalesced
    Block beforeBlock,
    Block afterBlock,
    Func<Block, string> GlobalblockLemmaName,
    Func<Block, string> HybridblockLemmaName,
    IList<Block> Loops,
    IDictionary<Block, BlockCoalescingInfo> ListCoalescedBlocks)
  {
    var loopHeads = new List<string>();
    foreach (Block loop in Loops)
    {
      loopHeads.Add("(" + beforeOptProgAccess.BlockInfo().BlockIds[loop] + "," + afterOptProgAccess.BlockInfo().BlockIds[beforeToAfterBlock[loop]] + ")");
    }

    var proofMethods = new List<string>
    {
      "apply (rule loopHead_global_block_hybrid)",
      "apply (rule " + beforeOptProgAccess.BlockInfo().OutEdgesMembershipLemma(beforeBlock) + ")",
      "apply (rule " + ProofUtil.OF("hybrid_block_lemma_loop_eq_loop_heads", 
        HybridblockLemmaName(beforeOptimizations.GetSuccessorBlocks(beforeBlock).FirstOrDefault())) + ")",
      "apply blast",
      "apply (rule " + beforeOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(beforeBlock) + ")",
      "apply (rule " + afterOptProgAccess.BlockInfo().BlockCmdsMembershipLemma(afterBlock) + ")",
      "apply (unfold " + afterOptProgAccess.BlockInfo().CmdsQualifiedName(afterBlock) +"_def)"
    };

    int i = ListCoalescedBlocks[beforeBlock].idx;
    List<Block> coalescedBlocks = ListCoalescedBlocks[beforeBlock].coalescedBlocks;
    foreach (Block current in coalescedBlocks.GetRange(i, coalescedBlocks.Count - i))
    {
     proofMethods.Add("apply (unfold " + beforeOptProgAccess.BlockInfo().CmdsQualifiedName(current) + "_def)"); 
    }
    proofMethods.Add("by simp");
    
    
    
    Term conclusion = getConclusion(loopHeads, "global_block_lemma_loop", beforeBlock, afterBlock, beforeOptProgAccess,
      afterOptProgAccess, false, null);
      
    var blockLemma = new LemmaDecl(
      GlobalblockLemmaName(beforeBlock), 
      conclusion,
      new Proof(proofMethods));
    return blockLemma;
  }

  public LemmaDecl EntryLemma(string entryLemmaName, string globalBlockLemmaEntryBlockName, Block beforeEntryBlock,
    Block afterEntryBlock)
  {
    Term numSteps = IsaCommonTerms.TermIdentFromName("j");
    Term normalInitState1 = IsaCommonTerms.TermIdentFromName("ns1");
    TermIdent finalNode = IsaCommonTerms.TermIdentFromName("m'");
    Term finalState = IsaCommonTerms.TermIdentFromName("s'");
    var redCfg = IsaBoogieTerm.RedCFGKStep(
      boogieContext,
      beforeOptProgAccess.CfgDecl(),
      IsaBoogieTerm.CFGConfigNode(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeEntryBlock]),
        IsaBoogieTerm.Normal(normalInitState1)),
      numSteps,
      IsaBoogieTerm.CFGConfig(finalNode, finalState));
    
    var finalNodeId2 = new SimpleIdentifier("m2'");
    var finalStateId2 = new SimpleIdentifier("s2'");
    var tarVer = cfgOptTargetVerifies(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterEntryBlock]),
      normalInitState1, finalNodeId2, finalStateId2);
    
    
    var assumptions = new List<Term> {redCfg};
    assumptions.Add(tarVer);
    
    return new LemmaDecl(
      entryLemmaName,
      ContextElem.CreateWithAssumptions(assumptions),
      CFGOptimizationsEndToEnd.CfgOptLemmaConclusion(boogieContext, afterOptProgAccess.PostconditionsDecl(), finalNode, finalState),
      new Proof(new List<string>
      {
        "using " + globalBlockLemmaEntryBlockName,
        "unfolding global_block_lemma_loop_def",
        "using assms(1) assms(2) by blast"
      })
    );
    
  }
  
  private Term cfgOptTargetVerifies(
    Term initialStateNode,
    Term initialNormalState,
    Identifier finalNodeId2,
    Identifier finalStateId2
  )
  {
    Term finalNode2 = new TermIdent(finalNodeId2);
    Term finalState2 = new TermIdent(finalStateId2);

    Func<IList<Identifier>, IList<TypeIsa>, Term, TermQuantifier> forallConstructor;
    Func<Term, Term, TermBinary> impliesConstructor;
    forallConstructor = TermQuantifier.ForAll;
    impliesConstructor = TermBinary.Implies;
    
    return
      forallConstructor(
        new List<Identifier> {finalNodeId2, finalStateId2},
        null,
        impliesConstructor(
          IsaBoogieTerm.RedCFGMulti(boogieContext,
            afterOptProgAccess.CfgDecl(),
            IsaBoogieTerm.CFGConfigNode(
              initialStateNode, IsaBoogieTerm.Normal(initialNormalState)
            ),
            IsaBoogieTerm.CFGConfig(finalNode2, finalState2)
          ),
          CFGOptimizationsEndToEnd.CfgOptLemmaConclusion(boogieContext, afterOptProgAccess.PostconditionsDecl(), finalNode2, finalState2))
      );
  }

  public static Term getConclusion(List<string> loopHeads, string name, Block beforeBlock, Block afterBlock, IProgramAccessor beforeOptProgAccess, IProgramAccessor afterOptProgAccess, bool isHybridBlock, List<String> listCoalescedBlocks)
  {
    var loopHeadsSet = new TermSet(loopHeads.Select(lh => IsaCommonTerms.TermIdentFromName(lh)));
    
    var varContextName = "\\<Lambda>";
    IList<Term> terms = new List<Term>();
    terms.Add(IsaCommonTerms.TermIdentFromName("A"));
    terms.Add(IsaCommonTerms.TermIdentFromName("M"));
    terms.Add(IsaCommonTerms.TermIdentFromName(varContextName));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Gamma>"));
    terms.Add(IsaCommonTerms.TermIdentFromName("\\<Omega>"));
    terms.Add(beforeOptProgAccess.CfgDecl());
    terms.Add(afterOptProgAccess.CfgDecl());
    terms.Add(new NatConst(beforeOptProgAccess.BlockInfo().BlockIds[beforeBlock]));
    terms.Add(new NatConst(afterOptProgAccess.BlockInfo().BlockIds[afterBlock]));
    if (isHybridBlock)
    {
      var listCoalescedBlocksTerm = listCoalescedBlocks.Aggregate<String, Term>(IsaCommonTerms.EmptyList,
        (x, y) => IsaCommonTerms.AppendList(x, IsaCommonTerms.TermIdentFromName(y)));
      terms.Add(listCoalescedBlocksTerm);
    }
    terms.Add(loopHeadsSet);
    terms.Add(afterOptProgAccess.PostconditionsDecl());
    Term conclusion = new TermApp(IsaCommonTerms.TermIdentFromName(name), terms);
    return conclusion;
  }
  
}

