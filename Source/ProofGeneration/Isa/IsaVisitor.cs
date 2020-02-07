﻿using System.Collections.Generic;

namespace ProofGeneration
{

    public abstract class OuterDeclVisitor<R>
    {
        public R Visit(OuterDecl d)
        {
            return d.Dispatch(this);
        }

        public abstract R VisitFunDecl(FunDecl d);
          
        public abstract R VisitDefDecl(DefDecl d);
    }

    public abstract class TermVisitor<R>
    {
        public R Visit(Term t)
        {
            return t.Dispatch(this);
        }

        public IList<R> VisitList(IList<Term> list)
        {
            var result = new List<R>();
            foreach (var t in list)
            {
                result.Add(Visit(t));
            }
            return result;
        }

        public abstract R VisitTermApp(TermApp t);

        public abstract R VisitTermList(TermList t);

        public abstract R VisitTermSet(TermSet t);

        public abstract R VisitTermRecord(TermRecord t);

        public abstract R VisitTermTuple(TermTuple t);

        public abstract R VisitTermIdent(TermIdent t);

        public abstract R VisitTermNAry(TermNAry t);

        public abstract R VisitBoolConst(BoolConst t);

        public abstract R VisitNatConst(NatConst t);

        public abstract R VisitIntConst(IntConst t);

        public abstract R VisitStringConst(StringConst t);
    }

    public abstract class TypeIsaVisitor<R>
    {
        public R Visit(TypeIsa t)
        {
            return t.Dispatch(this);
        }

        public IList<R> VisitList(IList<TypeIsa> list)
        {
            var result = new List<R>();
            foreach(var t in list) {
                result.Add(Visit(t));
            }
            return result;
        }

        public abstract R VisitTupleType(TupleType t);

        public abstract R VisitArrowType(ArrowType t);

        public abstract R VisitDataType(DataType t);

        public abstract R VisitPrimitiveType(PrimitiveType t);
    }
        
 }