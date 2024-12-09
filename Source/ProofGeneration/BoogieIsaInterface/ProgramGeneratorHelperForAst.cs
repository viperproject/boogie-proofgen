using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.Serialization.Formatters.Binary;
using System.Xml;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;

namespace ProofGeneration
{
    internal class BigBlockTermBuilder
    {
      private IDictionary<BigBlock, IList<DefDecl>> bigBlocksDefDecls;

      public BigBlockTermBuilder()
      {
        bigBlocksDefDecls = new Dictionary<BigBlock, IList<DefDecl>>();
      }

      public IDictionary<BigBlock, IList<DefDecl>> getBigblockDefDecls()
      {
        return bigBlocksDefDecls;
      }

      public Term makeBigBlockTerm(BigBlock b, AstToCfgProofGenInfo proofGenInfo, MultiCmdIsaVisitor cmdIsaVisitor, int flag, int nestedBlockTracker, string nameToUse, 
                                   out int updatedNestedBlockTracker)
      {
          var bigblock_term = IsaCommonTerms.TermIdentFromName("BigBlock");
          IList<Term> bigblock_args = new List<Term>();

          Term name_option;
          name_option = b.LabelName == null ? IsaCommonTerms.NoneOption() : IsaCommonTerms.SomeOption(IsaCommonTerms.TermIdentFromName(b.LabelName));
          
          bigblock_args.Add(name_option);

          var translatedCmds = cmdIsaVisitor.Translate(b.simpleCmds);
          TermList cmdsList = new TermList(translatedCmds);
          
          bigblock_args.Add(cmdsList);

          Term structure_option = makeStructuredCmdTerm(b, proofGenInfo, cmdIsaVisitor, nestedBlockTracker + 1, flag, nameToUse, 
                                                        out int updatedTrackerAfterStr);
          bigblock_args.Add(structure_option);

          Term transfer_option = null;
          if (b.tc is null)
          {
            transfer_option = IsaCommonTerms.NoneOption();
          }
          else if (b.tc is GotoCmd)
          {
            GotoCmd _goto = (GotoCmd) b.tc;
            List<String> target_names = _goto.labelNames;
            IList<Term> goto_arg_terms = new List<Term>();
            foreach (String target in target_names)
            {
              TermIdent target_term = IsaCommonTerms.TermIdentFromName(target);
              goto_arg_terms.Add(target_term);
            }
            TermIdent goto_ident = IsaCommonTerms.TermIdentFromName("Goto");
            Term arg_for_option = new TermApp(goto_ident, goto_arg_terms);
            transfer_option = IsaCommonTerms.SomeOption(arg_for_option);
          }
          else if (b.tc is ReturnCmd)
          {
            Term arg_for_option = IsaCommonTerms.TermIdentFromName("Return");
            transfer_option = IsaCommonTerms.SomeOption(arg_for_option);
          }
          bigblock_args.Add(transfer_option);

          IList<DefDecl> bb_decls = new List<DefDecl>();
          Term bigblock = new TermApp(bigblock_term, bigblock_args);

          if (nestedBlockTracker == 0)
          {
            DefDecl bigblock_def = DefDecl.CreateWithoutArg(nameToUse, bigblock);
            bb_decls.Add(bigblock_def);
            bigBlocksDefDecls.Add(b, bb_decls);
          }

          updatedNestedBlockTracker = updatedTrackerAfterStr;
          return bigblock; 
      }

      public Term makeStructuredCmdTerm(BigBlock b, AstToCfgProofGenInfo proofGenInfo, MultiCmdIsaVisitor cmdIsaVisitor, int nestedBlockTracker, int flag, string nameToUse, 
                                        out int updatedNestedBlockTracker)
      {
        Term strCmdTermOption = null;
        if (b.ec == null)
        {
          strCmdTermOption = IsaCommonTerms.NoneOption();
        }
        else if (b.ec is IfCmd)
        {
          IfCmd _if = (IfCmd) b.ec;
          Term if_term = IsaCommonTerms.TermIdentFromName("ParsedIf");

          Expr guard = _if.Guard;
          Term guard_term = null;
          if (guard is null)
          {
            guard_term = IsaCommonTerms.NoneOption();
          }
          else
          {
            guard_term = IsaCommonTerms.SomeOption(cmdIsaVisitor.TranslateSingle(guard));
          }
          
          IList<BigBlock> then_branch = _if.thn.BigBlocks;
          IList<Term> then_branch_bigblock_terms = new List<Term>();
          foreach (BigBlock bb in then_branch)
          {
            Term translated_bb = makeBigBlockTerm(bb, proofGenInfo, cmdIsaVisitor, 0, nestedBlockTracker, nameToUse, 
                                                  out int updatedTrackerAfterBlock);
            
            foreach (var pair in bigBlocksDefDecls)
            {
              if (pair.Value.First().Equation.Item2.ToString() == translated_bb.ToString() && 
                  proofGenInfo.GetMappingCopyBigBlockToIndex()[pair.Key] == proofGenInfo.GetMappingCopyBigBlockToIndex()[bb])
              {
                translated_bb = IsaCommonTerms.TermIdentFromName(pair.Value.First().Name);
                break;
              }
            }
            
            then_branch_bigblock_terms.Add(translated_bb);
            nestedBlockTracker = updatedTrackerAfterBlock + 1;
          }
          Term then_branch_term = new TermList(then_branch_bigblock_terms);
          
          IList<BigBlock> else_branch = _if.elseBlock.BigBlocks;
          IList<Term> else_branch_bigblock_terms = new List<Term>();
          foreach (BigBlock bb in else_branch)
          {
            Term translated_bb = makeBigBlockTerm(bb, proofGenInfo, cmdIsaVisitor, 0, nestedBlockTracker, nameToUse, 
                                                  out int updatedTrackerAfterBlock);

            foreach (var pair in bigBlocksDefDecls)
            {
              if (pair.Value.First().Equation.Item2.ToString() == translated_bb.ToString() && 
                  proofGenInfo.GetMappingCopyBigBlockToIndex()[pair.Key] == proofGenInfo.GetMappingCopyBigBlockToIndex()[bb])
              {
                translated_bb = IsaCommonTerms.TermIdentFromName(pair.Value.First().Name);
                break;
              }
            }
            
            else_branch_bigblock_terms.Add(translated_bb);
            nestedBlockTracker = updatedTrackerAfterBlock + 1;
          }
          Term else_branch_term = new TermList(else_branch_bigblock_terms);

          IList<Term> if_args_list = new List<Term>();
          if_args_list.Add(guard_term);
          if_args_list.Add(then_branch_term);
          if_args_list.Add(else_branch_term);

          strCmdTermOption = IsaCommonTerms.SomeOption(new TermApp(if_term, if_args_list));
        }
        else if (b.ec is WhileCmd)
        {
          WhileCmd _while = (WhileCmd) b.ec;
          Term wrapper = IsaCommonTerms.TermIdentFromName("WhileWrapper");
          Term while_term = IsaCommonTerms.TermIdentFromName("ParsedWhile");

          Expr guard = _while.Guard;
          Term guard_term = null;
          if (guard is null)
          {
            guard_term = IsaCommonTerms.NoneOption();
          }
          else
          {
            guard_term = IsaCommonTerms.SomeOption(cmdIsaVisitor.TranslateSingle(guard));
          }

          IList<PredicateCmd> invariants = _while.Invariants;
          IList<Term> inv_terms = new List<Term>();
          foreach (PredicateCmd inv in invariants)
          {
            Term translated_inv = cmdIsaVisitor.TranslateSingle(inv.Expr);
            inv_terms.Add(translated_inv);
          }
          Term invs_as_term = new TermList(inv_terms);
          
          IList<BigBlock> bodyBigBlocks = _while.Body.BigBlocks;
          IList<Term> body_bigblock_terms = new List<Term>();
          foreach (BigBlock bb in bodyBigBlocks)
          {
            Term translated_bb = makeBigBlockTerm(bb, proofGenInfo, cmdIsaVisitor, 0, nestedBlockTracker, nameToUse, 
                                                  out int updatedTrackerAfterBlock);
            
            foreach (var pair in bigBlocksDefDecls)
            {
              if (pair.Value.First().Equation.Item2.ToString() == translated_bb.ToString() && 
                  proofGenInfo.GetMappingCopyBigBlockToIndex()[pair.Key] == proofGenInfo.GetMappingCopyBigBlockToIndex()[bb])
              {
                translated_bb = IsaCommonTerms.TermIdentFromName(pair.Value.First().Name);
                break;
              }
            }
            
            body_bigblock_terms.Add(translated_bb);
            nestedBlockTracker = updatedTrackerAfterBlock + 1;
          }
          Term body_term = new TermList(body_bigblock_terms);
          
          IList<Term> while_args_list = new List<Term>();
          while_args_list.Add(guard_term);
          while_args_list.Add(invs_as_term);
          while_args_list.Add(body_term);

          Term unwrapped_str_loc = new TermApp(while_term, while_args_list);
          strCmdTermOption = IsaCommonTerms.SomeOption(flag == 1 ? unwrapped_str_loc : new TermApp(wrapper, unwrapped_str_loc));
        }
        else if (b.ec is BreakCmd)
        {
          BreakCmd _break = (BreakCmd) b.ec;
          Term label = IsaCommonTerms.TermIdentFromName(_break.Label);
          Term break_term = IsaCommonTerms.TermIdentFromName("ParsedBreak");
          Term strCmdTerm = new TermApp(break_term, label);
          
          strCmdTermOption = IsaCommonTerms.SomeOption(strCmdTerm);
        }

        updatedNestedBlockTracker = nestedBlockTracker;
        return strCmdTermOption;
      }

      public Term makeContinuationTerm(BigBlock b, AstToCfgProofGenInfo proofGenInfo, int successorIndex)
      {
        Term continuationTerm;
        Term continuationStart;
        Term continuationEnd;

        BigBlock correspondingBigBlockOrig;
        if (proofGenInfo.GetMappingLoopHeadBigBlocktoOrigLoopBigBlock().Keys.Contains(b))
        {
          correspondingBigBlockOrig = proofGenInfo.GetMappingLoopHeadBigBlocktoOrigLoopBigBlock()[b];
        }
        else
        {
          correspondingBigBlockOrig = proofGenInfo.GetMappingCopyBigblockToOrigBigblock()[b];
        }
        
        BigBlock successorBigBlockOrig = correspondingBigBlockOrig.successorBigBlock;
        
        //if the big block has no successors of any kind, make a 'KStop' continuation.
        if (successorBigBlockOrig == null)
        {
          continuationTerm = IsaCommonTerms.TermIdentFromName("KStop");
          return continuationTerm;
        }
        
        //if the big block is the last one in the body of a loop,
        //update the successor index needed for the continuation and make a 'KSeq' continuation. 
        if (successorBigBlockOrig.ec is WhileCmd)
        {
          WhileCmd wcmd = (WhileCmd) successorBigBlockOrig.ec;
          if (InLoop(correspondingBigBlockOrig, wcmd.Body.BigBlocks))
          {
            successorIndex++;
            
            continuationStart =
              IsaCommonTerms.TermIdentFromName("KSeq bigblock_" + successorIndex);
            continuationTerm = new TermApp(continuationStart, IsaCommonTerms.TermIdentFromName("cont_" + successorIndex));
            return continuationTerm;
          }
        }

        //if the big block is the special, artificially made, 'unwrapped' loop head big block, make a 'KEndBlock' continuation.
        if (b.ec is WhileCmd && proofGenInfo.GetMappingLoopHeadBigBlocktoOrigLoopBigBlock().Keys.Contains(b))
        {
          continuationStart = IsaCommonTerms.TermIdentFromName("KEndBlock (KSeq bigblock_" + successorIndex);
          continuationEnd = IsaCommonTerms.TermIdentFromName(")");
          continuationTerm = new TermApp(continuationStart, IsaCommonTerms.TermIdentFromName("cont_" + successorIndex), continuationEnd);
          return continuationTerm;
        }

        //in any other case, make a standard 'KSeq' continuation.
        continuationStart = IsaCommonTerms.TermIdentFromName("KSeq bigblock_" + successorIndex);
        continuationTerm = new TermApp(continuationStart, IsaCommonTerms.TermIdentFromName("cont_" + successorIndex));

        return continuationTerm;
      }

      private bool InLoop(BigBlock b, IList<BigBlock> bbs)
      {
        foreach (var curr in bbs)
        {
          if (curr == b)
          {
            return true;
          }

          if (curr.ec is IfCmd ifcmd)
          {
            if (InLoop(b, ifcmd.thn.BigBlocks) || (ifcmd.elseBlock != null) && InLoop(b, ifcmd.elseBlock.BigBlocks))
            {
              return true;
            }
          }
        }

        return false;
      }
      
      
    }
}