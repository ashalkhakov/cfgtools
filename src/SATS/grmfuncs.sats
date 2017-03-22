staload "./grm.sats"

(* ****** ****** *)
//
fun
ERASABLE {n:nat} (
  Grammar
, &arrayptr (Nonterminal, n)
, map (Nonterminal, size_t)
, size_t n
) : arrayptr (bool, n)
//
(* ****** ****** *)
//
fun{a:t@ype}
gsolve {n:nat} (
  g: $DG.digraph(n)
, I: &(@[set(INV(a))][n])(*initial set*)
, F: &(@[set(INV(a))?][n]) >> @[set(a)][n](*final set*)
): void
//
(* ****** ****** *)
//
fun
FIRSTSETS {n:nat} (
  Grammar
, &arrayptr (bool, n) >> _
, &arrayptr (Nonterminal, n) >> _
, map (Nonterminal, size_t)
, size_t n
) : arrayptr (set(Terminal), n)
//
fun
FIRST {n:nat;m:pos} (
  list(Symbol, m)
, &arrayptr (bool, n) >> _
, &arrayptr (Nonterminal, n) >> _
, map (Nonterminal, size_t)
, size_t n
, &arrayptr (set(Terminal), n) >> _
) : set(Terminal)
//
fun
FOLLOWSETS {n:nat} (
  Grammar
, &arrayptr (bool, n) >> _
, &arrayptr (Nonterminal, n) >> _ (*numbered nonterminals*)
, map (Nonterminal, size_t) (*nontermmap*)
, &arrayptr (set(Terminal), n) >> _ (*first sets*)
, size_t n
): arrayptr (set(Terminal), n)(*follow sets*)
//
