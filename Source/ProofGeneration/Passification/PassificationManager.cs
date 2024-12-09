using System;
using System.Collections.Generic;
using System.Linq;
using Isabelle.Ast;
using Isabelle.Util;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.CFGRepresentation;
using ProofGeneration.Util;

namespace ProofGeneration.Passification
{
    public class PassificationManager
    {
        private static readonly string oldRelListName = "R_old_list";
        private static readonly TermIdent oldRelList = IsaCommonTerms.TermIdentFromName("R_old_list");
        private static readonly string oldRelName = "R_old";
        private static readonly TermIdent oldRel = IsaCommonTerms.TermIdentFromName("R_old");
        private static readonly string allOldLookupLemmasName = "R_old_lemmas";

        public static TypeIsa StateRelListReprType =
            IsaCommonTypes.GetListType(new TupleType(
                IsaBoogieType.VnameType(),
                new SumType(IsaBoogieType.VnameType(), IsaBoogieType.LitType())));


        public static Theory PassificationProof(
            string theoryName,
            string boogieToVcTheoryName,
            bool generateEndToEndLemma,
            LemmaDecl boogieToVcLemma,
            Term vcAssm,
            CFGRepr beforePassificationCfg,
            IDictionary<Block, Block> nonPassiveToPassiveBlock,
            PassiveRelationGen relationGen,
            IProgramAccessor beforePassiveProgAccess,
            IProgramAccessor passiveProgAccess,
            IVariableTranslationFactory beforePassiveFactory,
            IVariableTranslationFactory passiveFactory)
        {
            
            var varContextName = "\\<Lambda>1";
            var passiveVarContextName = "\\<Lambda>2";
            var varContextNonPassivePassive = Tuple.Create(varContextName, passiveVarContextName);

            var oldGlobalVars = GetOldGlobalVariables(beforePassificationCfg);
            var oldRelationData =
                OldRelation(
                    oldGlobalVars,
                    beforePassiveFactory.CreateTranslation().VarTranslation,
                    out var oldRelListDecl);

            var passificationProofDecls = new List<OuterDecl>();
            passificationProofDecls.AddRange(oldRelListDecl);
            passificationProofDecls.AddRange(oldRelationData.VarToLookupLemma.Values);
            if (oldRelationData.VarToLookupLemma.Any())
                passificationProofDecls.Add(new LemmasDecl(allOldLookupLemmasName,
                    oldRelationData.VarToLookupLemma.Values.Select(lemma => lemma.Name).ToList()));

            var beforePassiveLemmaManager = new PassificationLemmaManager(
                beforePassificationCfg,
                nonPassiveToPassiveBlock,
                beforePassiveProgAccess,
                passiveProgAccess,
                varContextNonPassivePassive,
                oldRelationData,
                relationGen,
                beforePassiveFactory,
                passiveFactory
            );

            var lemmaNamer = new IsaUniqueNamer();

            var varContextAbbrev = new AbbreviationDecl(
                varContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), beforePassiveProgAccess.VarContext())
            );

            var passiveVarContextAbbrev = new AbbreviationDecl(
                passiveVarContextName,
                new Tuple<IList<Term>, Term>(new List<Term>(), passiveProgAccess.VarContext())
            );

            passificationProofDecls.Add(varContextAbbrev);
            passificationProofDecls.Add(passiveVarContextAbbrev);

            passificationProofDecls.AddRange(beforePassiveLemmaManager.Prelude());

            var cfgLemmas = new List<OuterDecl>();

            foreach (var block in beforePassificationCfg.GetBlocksBackwards())
            {
                var localAndCfgLemma =
                    beforePassiveLemmaManager.GenerateBlockLemma(
                        block,
                        GetLemmaName(block, lemmaNamer),
                        b => GetCfgLemmaName(b, lemmaNamer));
                passificationProofDecls.Add(localAndCfgLemma.Item1);
                cfgLemmas.Add(localAndCfgLemma.Item2);
            }

            //add cfg lemmas at the end
            passificationProofDecls.AddRange(cfgLemmas);

            if (generateEndToEndLemma)
            {
                var endToEnd = new PassificationEndToEnd();

                /* We need to add the accessed old global variables to the live variable subset at entry. This is because
                   we have a proof obligation requiring that the old global relation must be contained in the initial 
                   relation used to construct the initial passive state set in the end-to-end proof. */
                var oldGlobals = GetOldGlobalVariables(beforePassificationCfg);
                var liveVarsBefore = relationGen.LiveVarsBeforeBlock(beforePassificationCfg.entry).Union(oldGlobals);
                
                passificationProofDecls.AddRange(endToEnd.EndToEndProof(
                    GetCfgLemmaName(beforePassificationCfg.entry, lemmaNamer),
                    boogieToVcTheoryName + "." + boogieToVcLemma.Name,
                    vcAssm,
                    beforePassiveProgAccess,
                    passiveProgAccess,
                    varContextNonPassivePassive,
                    oldRelationData,
                    beforePassificationCfg,
                    liveVarsBefore,
                    passiveFactory.CreateTranslation().VarTranslation
                ));
            }

            var imports = new List<string>
            {
                "Boogie_Lang.Semantics", "Boogie_Lang.Util", beforePassiveProgAccess.TheoryName(),
                passiveProgAccess.TheoryName(), "Boogie_Lang.PassificationML",
                boogieToVcTheoryName
            };
            if (generateEndToEndLemma)
                imports.Add("Boogie_Lang.PassificationEndToEnd");

            return new Theory(theoryName, imports, passificationProofDecls);
        }

        /// <summary>
        ///     Return lookup lemmas for each element in the old relation as well as the definition of the old relation, which
        ///     is defined via an association list
        /// </summary>
        private static StateRelationData OldRelation(
            ISet<Variable> oldGlobalVars,
            IVariableTranslation<Variable> variableTranslation,
            out IList<OuterDecl> oldRelDecls)
        {
            //assume that passive version representing old variable of "g" is "g" itself
            var oldRelTuples = new List<Term>();
            var varList = new List<Variable>();
            var varToLookupLemma = new Dictionary<Variable, LemmaDecl>();
            var uniqueNamer = new IsaUniqueNamer();
            foreach (var v in oldGlobalVars)
                if (variableTranslation.TryTranslateVariableId(v, out var varTermId, out _))
                {
                    oldRelTuples.Add(new TermTuple(varTermId, IsaCommonTerms.Inl(varTermId)));
                    var lemma = new LemmaDecl(
                        "lookup_old_rel" + uniqueNamer.GetName(v, v.Name),
                        TermBinary.Eq(new TermApp(oldRel, varTermId),
                            IsaCommonTerms.SomeOption(IsaCommonTerms.Inl(varTermId))),
                        new Proof(new List<string>
                        {
                            "unfolding " + oldRelListName + "_def " + oldRelName + "_def",
                            "by simp"
                        })
                    );
                    varToLookupLemma.Add(v, lemma);
                    varList.Add(v);
                }
                else
                {
                    throw new ProofGenUnexpectedStateException("Could not translate variable");
                }

            //TODO: ensure no name clashes
            oldRelDecls = new List<OuterDecl>
            {
                DefDecl.CreateWithoutArg(oldRelListName, StateRelListReprType, new TermList(oldRelTuples)),
                DefDecl.CreateWithoutArg(oldRelName,
                    new TermApp(IsaCommonTerms.TermIdentFromName("map_of"), oldRelList))
            };

            return new StateRelationData(
                varToLookupLemma,
                varList,
                oldRel,
                oldRelList,
                allOldLookupLemmasName
            );
        }

        /// <summary>
        ///     return all global and constant variables that occur within an old expression in
        ///     <paramref name="beforePassiveCfg" />
        /// </summary>
        private static ISet<Variable> GetOldGlobalVariables(CFGRepr beforePassiveCfg)
        {
            var oldVarFinder = new OldVarFinder();
            var oldVars = new HashSet<Variable>();
            Predicate<Variable> pred = v => v is Constant || v is GlobalVariable;
            foreach (var b in beforePassiveCfg.GetBlocksForwards())
            {
                var result = oldVarFinder.FindOldVariables(b, pred);
                oldVars.UnionWith(result);
            }

            return oldVars;
        }

        private static string GetLemmaName(Block b, IsaUniqueNamer namer)
        {
            return namer.GetName(b, "block_" + b.Label);
        }

        private static string GetCfgLemmaName(Block b, IsaUniqueNamer namer)
        {
            return "cfg_" + namer.GetName(b, b.Label);
        }
    }
}