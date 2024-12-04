//:: ProofGen(IgnoreFile)
// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/** MANUEL REWRITE renamed Lit to LitA to avoid Isabelle Lit clash **/
function LitA<T>(x: T) : T; 
axiom LitA(true);

procedure test()
{
    assert LitA(true);
}
