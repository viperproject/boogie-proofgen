//:: ProofGen(IgnoreFile)
// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function  Lit<T>(x: T) : T;
axiom Lit(true);
function  LitA<T>(x: T) : T; //renamed Lit to LitA to avoid Isabelle Lit clash
axiom LitA(true);

procedure test()
{
    assert LitA(true);
}
