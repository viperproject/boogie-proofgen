function abs(x: int): int { if 0 <= x then x else -x }
function divt(int, int): int;
function modt(int, int): int;
axiom (forall a,b: int :: divt(a,b)*b + modt(a,b) == a);
axiom (forall a,b: int ::
  (0 <= a ==> 0 <= modt(a,b) && modt(a,b) < abs(b)) &&
  (a < 0 ==> -abs(b) < modt(a,b) && modt(a,b) <= 0));
function dive(int, int): int;
function mode(int, int): int;
axiom (forall a,b: int :: dive(a,b)*b + mode(a,b) == a);
axiom (forall a,b: int :: 0 <= mode(a,b) && mode(a,b) < abs(b));
procedure T_from_E(a,b: int) returns (q,r: int)
  requires b != 0;
  ensures q*b + r == a;
  ensures 0 <= a ==> 0 <= r && r < abs(b);
  ensures a < 0 ==> -abs(b) < r && r <= 0;
{
  var qq,rr: int;
  qq := dive(a,b);
  rr := mode(a,b);
  q := if 0 <= a || rr == 0 then qq else if 0 <= b then qq+1 else qq-1;
  r := if 0 <= a || rr == 0 then rr else if 0 <= b then rr-b else rr+b;
  assume true;
}
procedure E_from_T(a,b: int) returns (q,r: int)
  requires b != 0;
  ensures q*b + r == a;
  ensures 0 <= r;
  ensures r < abs(b);
{
  var qq,rr: int;
  qq := divt(a,b);
  rr := modt(a,b);
  q := if 0 <= rr then qq else if 0 < b then qq-1 else qq+1;
  r := if 0 <= rr then rr else if 0 < b then rr+b else rr-b;
}
