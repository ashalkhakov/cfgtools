#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

staload "./fundigraph.sats"
staload _(*anon*) = "./fundigraph.dats"

staload "libats/SATS/funset_avltree.sats"
staload _(*anon*) = "libats/DATS/funset_avltree.dats"

staload "libats/SATS/funmap_avltree.sats"

staload
_(*anon*) = "libats/DATS/qlist.dats"
staload
_(*anon*) = "libats/DATS/funmap_avltree.dats"

// ------------------
extern
fun{a:t0p}
funset_filter$pred (x: a): bool
extern
fun{a:t0p}{env:vt0p}
funset_filter$fwork (x: a, &(env) >> _): void
extern
fun{a:t0p}{env:vt0p}
funset_filter_env (set: set(INV(a)), &(env) >> _): void

implement{a}
funset_filter$pred (x) = true
implement{a}{env}
funset_filter$fwork (x, env) = ()
implement{a}{env}
funset_filter_env (set, env) = let
  implement
  funset_foreach$fwork<a><env> (x, env) =
    if funset_filter$pred<a> (x) then let
      val () = funset_filter$fwork<a><env> (x, env)
    in
    end
in
  funset_foreach_env<a><env> (set, env)
end
// ------------------
extern
fun{
a:vt0p}{b:vt0p}{env:vt0p
} array_mapto_env{n:int}
(
  A: &array(INV(a), n)
, B: &array(b?, n) >> array (b, n)
, env: &(env) >> _
, n: size_t (n)
) : void // end of [array_mapto_env]
extern
fun{
a:vt0p}{b:vt0p}{env:vt0p
} array_mapto_env$fwork (x: &a, y: &b? >> b, env: &(env) >> _) : void
//
implement
{a}{b}{env}
array_mapto_env
  {n}(A, B, env, n) = let
//
val pa = addr@ (A)
val pa2 = ptr_add<a> (pa, n)
val pb = addr@ (B)
//
fun loop{la,lb:addr}
(
  pa: ptr la, pa2: ptr, pb: ptr lb, env: &(env) >> _
) : void =
(
if pa < pa2 then let
  val (pfa, fpfa | pa) = $UN.ptr_vtake{a}(pa)
  val (pfb, fpfb | pb) = $UN.ptr_vtake{b?}(pb)
  val () = array_mapto_env$fwork<a><b> (!pa, !pb, env)
  prval () = fpfa (pfa)
  prval () = fpfb ($UN.castview0{(b?)@lb}(pfb))
in
  loop (ptr_succ<a> (pa), pa2, ptr_succ<b> (pb), env)
end (* end of [if] *)
)
//
val () = loop (pa, pa2, pb, env)
prval [lb:addr] EQADDR () = ptr_get_index (pb)
prval () = view@(B) := $UN.castview0{array_v (b, lb, n)}(view@(B))
//
in
  // nothing
end (* end of [array_mapto_env] *)
//
// ------------------
extern
fun{key:t0p;itm:t0p}
funmap_filter$pred
  (k: key, x: itm): bool
extern
fun{key:t0p;itm:t0p}{env:vt0p}
funmap_filter$fwork
  (k: key, x: itm, env: &(env) >> _): void
extern
fun{key:t0p;itm:t0p}{env:vt0p}
funmap_filter_env (map: map (key, INV(itm)), &(env) >> _): void
//
implement{key,itm}
funmap_filter$pred (k, x) = true
implement{key,itm}{env}
funmap_filter$fwork (k, x, env) = ()
implement{key,itm}{env}
funmap_filter_env (map, env) = let
  implement
  funmap_foreach$fwork<key,itm><env> (k, x, env) =
    if funmap_filter$pred<key,itm> (k, x) then
      funmap_filter$fwork<key,itm> (k, x, env)
  // end of [funmap_foreach$fwork]
in
  funmap_foreach_env<key,itm><env> (map, env)
end
// ------------------

datatype Symbol (b:bool) = Nterm (false) of string | Term(true) of string
typedef Terminal = Symbol(true)
typedef Nonterminal = Symbol(false)
typedef Symbol = [b:bool] Symbol (b)

val sym_EOF = Term("EOF")
val sym_EPS = Term("EPS")

extern
fun
fprint_Symbol (FILEref, Symbol): void
overload fprint with fprint_Symbol
extern
fun
fprint_Nonterminal (FILEref, Nonterminal): void
overload fprint with fprint_Nonterminal of 10
extern
fun
fprint_Terminal (FILEref, Terminal): void
overload fprint with fprint_Terminal of 10

implement
fprint_Symbol (out, sym) =
case+ sym of
| Nterm x => fprint!(out, "ntm(", x, ")")
| Term x => fprint!(out, "trm(", x, ")")

implement
fprint_Nonterminal (out, sym) = fprint_Symbol (out, sym)
implement
fprint_Terminal (out, sym) = fprint_Symbol (out, sym)

implement
fprint_val<Symbol> (out, sym) = fprint_Symbol (out, sym)
implement
fprint_val<Terminal> (out, sym) = fprint_Symbol (out, sym)
implement
fprint_val<Nonterminal> (out, sym) = fprint_Symbol (out, sym)

extern
fun
compare_Symbol_Symbol (x: Symbol, y: Symbol):<> int
overload compare with compare_Symbol_Symbol
extern
fun
eq_Symbol_Symbol (x: Symbol, y: Symbol):<> bool
overload = with eq_Symbol_Symbol
extern
fun
neq_Symbol_Symbol (x: Symbol, y: Symbol):<> bool
overload <> with neq_Symbol_Symbol

implement
compare_Symbol_Symbol (x, y) =
  case+ (x, y) of
  | (Nterm (x), Nterm (y)) => compare (x, y)
  | (Term (x), Term (y)) => compare (x, y)
  | (Nterm (x), Term (y)) => ~1
  | (Term (x), Nterm (y)) => 1

implement
eq_Symbol_Symbol (x, y) = compare (x, y) = 0
implement
neq_Symbol_Symbol (x, y) = compare (x, y) <> 0

implement
compare_elt_elt<Symbol> (x, y) = $effmask_all (compare_Symbol_Symbol (x, y))
implement
compare_elt_elt<Terminal> (x, y) = $effmask_all (compare_Symbol_Symbol (x, y))
implement
compare_elt_elt<Nonterminal> (x, y) = $effmask_all (compare_Symbol_Symbol (x, y))

implement
compare_key_key<Nonterminal> (x, y) = $effmask_all (compare_Symbol_Symbol (x, y))

extern
fun
Symbol_is_terminal {b:bool} (Symbol b): bool b
extern
fun
Symbol_is_nonterminal {b:bool} (Symbol b): bool (~b)

implement
Symbol_is_terminal {b} (x) =
  case+ x of Nterm _ => false | Term _ => true
implement
Symbol_is_nonterminal {b} (x) =
  case+ x of Nterm _ => true | Term _ => false

datatype Production = Prod of (Nonterminal, List(Symbol))
// NOTE: store terminals, nonterminals separately in arrays
// - only give indices into these arrays!
datatype Grammar = Grammar of (
  // arrayref (Nonterminal, n1)
  // arrayref (Terminal, n2)
  // map (int, Production1) where Production1 = Prod (NonterminalNr, List(SymbolNr))
  //    where SymbolNr = NT of NonterminalNr | T of TerminalNr
  //    or just: SymbolList = List(@(bool,size_t)) // true,1 -> ntm...
  set (Symbol)
, map (int, Production)
, int(*start prod*)
)

extern
fun
fprint_Production (FILEref, Production): void
overload fprint with fprint_Production

implement
fprint_Production (out, prod) = let
  val Prod (ntm, rhs) = prod
  val () = fprint_Symbol (out, ntm)
  val () = fprint! (out, " ::= ")
  val () = fprint! (out, rhs)
in
end
implement
fprint_val<Production> (out, prod) = fprint_Production (out, prod)

extern
fun
Production_derives (Production): Nonterminal
implement
Production_derives (prod) = let
  val Prod (ntm, rhs) = prod
in
  ntm
end

extern
fun
fprint_Grammar (FILEref, Grammar): void
overload fprint with fprint_Grammar
implement
fprint_Grammar (out, gr) = {
val Grammar (alphabet, prods, start) = gr
val () = fprintln!(out, "alphabet:")
val () = fprint_funset<Symbol> (stdout_ref, alphabet)
val () = fprint_newline (out)
val () = fprintln!(out, "productions:")
val () = fprint_funmap<int,Production> (stdout_ref, prods)
val () = fprint_newline (out)
val () = fprintln!(out, "start production:", start)
}
implement
fprint_val<Grammar> (out, gr) = fprint_Grammar (out, gr)
//
extern
fun
Grammar_nonterminals (
  Grammar
, &ptr? >> arrayptr (Nonterminal, n)
, &ptr? >> map (Nonterminal, size_t)
): #[n:int] size_t(n)
//
implement
Grammar_nonterminals (gr, nonterms, nontermmap) = let
  val Grammar (alphabet, prods, _) = gr
  fun
  aux0 {n:nat} (
    nxs: int n
  , xs: &list_vt(Nonterminal, n) >> list_vt (Nonterminal, m)
  , syms: &set(Symbol) >> _
  , symmap: &map (Nonterminal, size_t) >> _
  ) : #[m:nat] int m = let
    var sym : Symbol // uninitialized
    val res = funset_takeoutmin<Symbol> (syms, sym)
  in
    if :(sym: Symbol?) => res then let
      val sym0 = opt_unsome_get<Symbol> (sym)
    in
      if Symbol_is_nonterminal (sym0) then let
        val () = xs := list_vt_cons {Nonterminal} (sym0, xs)
        val idx = (i2sz)nxs
        val idx = (g0ofg1)idx
        val nxs = nxs+1
        var oidx : size_t
        val-false = funmap_insert<Nonterminal,size_t> (symmap, sym0, idx, oidx)
        prval () = opt_unnone {size_t} (oidx)
      in
        aux0 (nxs, xs, syms, symmap)
      end else let
      in
        aux0 (nxs, xs, syms, symmap)
      end // end of [if]
    end else let
      prval () = opt_unnone {Symbol} (sym)
    in
      nxs
    end
  end // end of [aux0]
  var nonterminals = alphabet // copy
  val () = nontermmap := funmap_nil {Nonterminal,size_t} ()
  var nodelst = list_vt_nil{Nonterminal} ()
  val nodecount = aux0 (0, nodelst, nonterminals, nontermmap)
  val nodecount = (i2sz)nodecount
  val (pf_arr, pf_free | p_arr) = array_ptr_alloc<Nonterminal> (nodecount)
  val () = array_copy_from_list_vt (!p_arr, nodelst)
(*
  val () = fprintln!(stdout_ref, "nodes array: ")
  val () = fprint_array (stdout_ref, !p_arr, nodecount)
  val () = fprint_newline (stdout_ref)
*)
  val () = nonterms := arrayptr_encode (pf_arr, pf_free | p_arr)
in
  nodecount
end
//
(* ****** ****** *)
//
extern
fun{a:t@ype}
gsolve {n:nat} (
  g: digraph(n)
, I: &(@[set(INV(a))][n])(*initial set*)
, F: &(@[set(INV(a))?][n]) >> @[set(a)][n](*final set*)
): void
//
implement{a}
gsolve {n} (g, I, F) = {
//
(*
compute sequence of approximations F_k(i), 1 <= i <= N, where
- F_0(i) = {}, 1 <= i <= N
   this is easy: just start with the empty sets for all of F
- F_(k+1)(i) = union(I(i), concat({F_k(j) | iGj, i <> j})), 1 <= i <= N
   this is a bit harder
F(i) = concat({I(j) | iG*j})
- this is what we can do, say use a depth-first search really
- start the search at i, and visit every node you can,
  adding its associated I set to the result
  - basically, we already have query here: reachable(i,j) -> do the deed!
*)
//
  vtypedef I(n:int) = @[set(a)][n]
//
  val rtc = fundigraph_rtc_init (g)
  val n = fundigraph_size (g)
//
  fun aux1 {i,j,n:nat | i < n; j <= n} .<n-j>. (
    init: &I(n)
  , p: &set(a) >> _
  , rtc: !digraph_rtc (n)
  , i: size_t i, j: size_t j, n: size_t n
  ): void =
    if j < n then begin
      if :(p: set(a)) => fundigraph_rtc_reachable_from (rtc, i, j) then {
      (*
        val () = fprintln! (stdout_ref, "node ", j, " reachable from ", i)
      *)
        val p1 = p
        val () = p := funset_union<a> (p1, init.[j])
      }; (* end of [val] *)
      aux1 (init, p, rtc, i, succ(j), n)
    end // end of [aux1]
//
  fun
  aux0 {i,n,n1:nat | i <= n; n1 == n-i} {l:addr} .<n1>. (
    pf: !array_v (set(a)?, l, n1) >> array_v (set(a), l, n1)
  | init: &I(n)
  , p: ptr l, rtc: !digraph_rtc(n)
  , i: size_t i, n: size_t n
  ) : void =
    if i < n then let
      prval (pf1, pf2) = array_v_uncons (pf)
      val () = !p := init.[i]
      (*
      val () = fprintln! (stdout_ref, "calling aux1 with: ", i)
      *)
      val () = aux1 (init, !p, rtc, i, (i2sz)0, n)
      val () = aux0 (pf2 | init, ptr1_succ<set(a)> (p), rtc, succ(i), n)
      prval () = pf := array_v_cons (pf1, pf2)
    in
      (*empty*)
    end else let
      prval () = pf := array_v_unnil_nil (pf)
    in
      (*empty*)
    end // end of [aux0]
(*
  val () = fprintln! (stdout_ref, "calling aux0:")
*)
  val () = aux0 (view@(F) | I, addr@(F), rtc, (i2sz)0, n)
  val () = fundigraph_rtc_free (rtc)
//
} (* end of [gsolve] *)
//
(* ****** ****** *)
//
implement
fprint_val<set(Terminal)> (out, x) =
  fprint_funset<Terminal> (out, x)
//
(* ****** ****** *)
//
// FIRST (A) = union(INITFIRST(A), concat({FIRST(B) | A -> B alpha in P, A <> B}))
(*
let F(i), 1 <= i <= N be sets to be computed
let I(i), 1 <= i <= N, I(i) subsetof F(i), be given initial subsets of F(i) (initial sets)

let G be a digraph, with nodes {1, ..., N}, with edges representing relationships
between F(i), 1 <= i <= N
- if there is edge between i, j (1 <= i <= N, 1 <= j <= N, i <> j), it is denoted iGj
- the existence of a path between i, j is denoted iG+j
- the existence of a path between i, j, including the null path, is denoted iG*j

if G represents a relation, then G* is reflexive and transition closure of G

we want to solve a system of equations:

F(i) = union(I(i), {F(j) | iGj, i <> j}), 1 <= i <= N

to solve:

compute sequence of approximations F_k(i), 1 <= i <= N, where
- F_0(i) = {}, 1 <= i <= N
- F_(k+1)(i) = union(I(i), concat({F_k(j) | iGj, i <> j})), 1 <= i <= N

*)
//
extern
fun
FIRSTSETS {n:nat} (
  Grammar
, &arrayptr (Nonterminal, n)
, map (Nonterminal, size_t)
, size_t n
) : arrayptr (set(Terminal), n)
//
local
//
extern
fun
INITFIRST (Grammar, Nonterminal): set(Terminal)
//
implement
INITFIRST (gr, X) = let
//
vtypedef Env = set(Terminal)
//
val Grammar (alphabet, prods, _) = gr
//
implement
funmap_foreach$fwork<int,Production><Env> (k, x, env) =
  if Production_derives(x) = X then let
    val Prod (_, rhs) = x
    (*
    val () = fprint!(stdout_ref, "working on: ")
    val () = fprint_Production (stdout_ref, x)
    val () = fprint_newline (stdout_ref)
    *)
  in
    case+ rhs of
    | list_cons (a, rhs) when Symbol_is_terminal (a) => {
    (*
      val () = fprintln!(stdout_ref, "inserting!")
    *)
      val _ = funset_insert<Terminal> (env, a)
    } (* end of [if] *)
    | _ => () // empty??? shouldn't happen (we don't handle EPS, yet)
  end // end of [funmap_foreach$fwork]
var env = funset_nil{Terminal} ()
val () = funmap_foreach_env<int,Production><Env> (prods, env)
//
in
  env
end // end of [INITFIRST]
//
extern
fun
GFIRST {n:nat} (
  Grammar
, &arrayptr (Nonterminal, n)
, map (Nonterminal, size_t)
, size_t (n)
): digraph(n)
implement
GFIRST (gr, nonterms, nontermmap, nodecount) = let
  typedef nodes = set(Nonterminal)
  val Grammar (alphabet, prods, _) = gr

  implement
  funmap_foreach$fwork<Nonterminal,size_t><digraph> (ntm, idx, env) = let
    implement
    funmap_foreach$fwork<int,Production><digraph> (k, x, env) =
      if Production_derives(x) = ntm then let
(*
        val () = fprintln!(stdout_ref, "considering production: ", x)
*)
        // production is of the form ntm -> rhs
        val Prod (_, rhs) = x
      in
        case+ rhs of
        | list_cons (y, _) when Symbol_is_nonterminal (y) =>
          // production is of the form ntm -> y rhs, where y is some nonterminal
          if y <> ntm then {
(*
            val () = fprint!(stdout_ref, "found edge from: ")
            val () = fprint_Symbol (stdout_ref, ntm)
            val () = fprint!(stdout_ref, " to: ")
            val () = fprint_Symbol (stdout_ref, y)
            val () = fprint_newline (stdout_ref)
*)
            var idx_y : size_t
            val-true = funmap_search<Nonterminal,size_t> (nontermmap, y, idx_y)
            prval () = opt_unsome {size_t} (idx_y)
            val n = fundigraph_size (env)
            prval [n:int] EQINT () = eqint_make_guint (n)
            val idx = $UN.cast{sizeLt(n)} (idx)
            val idx_y = $UN.cast{sizeLt(n)} (idx_y)
            val _ = fundigraph_insert_edge (env, idx_y, idx)
          } (* end of [if] *)
        | list_cons (y, _) => ()
        | list_nil () => ()
      end // end of [funmap_foreach$fwork]
  in
    funmap_foreach_env<int,Production><digraph> (prods, env)
  end
  var graph = fundigraph_make (nodecount)
  val () = funmap_foreach_env<Nonterminal,size_t><digraph> (nontermmap, graph)
//
  val nsz = fundigraph_size (graph)
  val () = assert_errmsg (nsz = nodecount, "digraph vertex count changed!")
//
in
  graph
end // end of [GFIRST]
//
in // in of [local]
//
implement
FIRSTSETS (
  gr
, nterms
, nontermmap
, nodecount
) = let
  // compute the GFIRST graph
  val gfirst = GFIRST (gr, nterms, nontermmap, nodecount)

  // allocate init and final arrays
  val (pf_init, pf_init_free | p_init) = array_ptr_alloc<set(Terminal)> (nodecount)
  val (pf_fin, pf_fin_free | p_fin) = array_ptr_alloc<set(Terminal)> (nodecount)
  // for each nonterminal, obtain its INITFIRST set
  implement
  array_mapto$fwork<Nonterminal><set(Terminal)> (ntm, init) = {
    val () = init := INITFIRST (gr, ntm)
    (*
    val () = fprintln! (stdout_ref, "for nonterminal: ")
    val () = fprint_Symbol (stdout_ref, ntm)
    val () = fprint_newline (stdout_ref)
    val () = fprintln! (stdout_ref, "the termset is:")
    val () = fprint_funset<Terminal> (stdout_ref, init)
    val () = fprint_newline (stdout_ref)
    *)
  } (* end of [array_mapto$fwork] *)
  val p_arrnode = arrayptr2ptr (nterms)
  prval pf_arrnode = arrayptr_takeout (nterms)
  val () = array_mapto<Nonterminal><set(Terminal)> (!p_arrnode, !p_init, nodecount)
  prval () = arrayptr_addback (pf_arrnode | nterms)
  //
(*
  val () = fprintln! (stdout_ref, "calling gsolve: ")
*)
  val () = gsolve<Terminal> (gfirst, !p_init, !p_fin)
  //
  val () = array_ptr_free (pf_init, pf_init_free | p_init)
  //
in
  arrayptr_encode (pf_fin, pf_fin_free | p_fin)
end // end of [FIRSTSETS]
//
end // end of [local]
//
(* ****** ****** *)
//
extern
fun
FOLLOWSETS {n:nat} (
  Grammar
, &arrayptr (Nonterminal, n) (*numbered nonterminals*)
, map (Nonterminal, size_t) (*nontermmap*)
, &arrayptr (set(Terminal), n)(*first sets*)
, size_t n
): arrayptr (set(Terminal), n)(*follow sets*)
//
local
//
extern
fun
INITFOLLOW {n:nat} (
  Grammar
, Nonterminal(*nonterminal*)
, &arrayptr (Nonterminal, n)(*numbered nonterminals*)
, map (Nonterminal, size_t)
, &arrayptr (set(Terminal), n)(*first sets*)
, size_t n
): set(Terminal)
//
typedef STATENODE (n:int) = @{
  nterms= ptr
, ntermmap= ptr
, fsets= ptr
, nodecount= size_t n
, result= ptr
} (* end of [STATENODE] *)
//
typedef STATENODE0 = STATENODE (0)?
absvt@ype STATE (n:int) = STATENODE (n)
vtypedef STATE = [n:nat] STATE (n)
//
extern
fun
STATE_init {n:int} (
  nterms: arrayptr (Nonterminal, n)(*numbered nonterminals*)
, ntermmap: map (Nonterminal, size_t)
, fsets: arrayptr (set(Terminal), n)(*first sets*)
, nodecount: size_t n
, &STATENODE0 >> STATE (n)
): void
//
extern
fun
STATE_getres_free {n:nat} (
  &ptr? >> arrayptr (Nonterminal, n)(*numbered nonterminals*)
, &ptr? >> arrayptr (set(Terminal), n)(*first sets*)
, &STATE (n) >> STATENODE0
) : set(Terminal)
//
extern
fun
STATE_get_nodecount {n:nat} (&STATE (n)): size_t(n)
//
extern
fun
STATE_scan {n,nxs:nat} (
  env: &STATE (n) >> STATE (n)
, X: Nonterminal
, xs: list (Symbol, nxs)
): void
//
local
//
typedef tset = set(Terminal)
typedef N = Nonterminal
typedef T = Terminal
typedef S = Symbol
//
assume STATE (n:int) = @{
  nterms= arrayptr (Nonterminal, n)(*numbered nonterminals*)
, ntermmap= map (Nonterminal, size_t)
, fsets= arrayptr (set(Terminal), n)(*first sets*)
, nodecount= size_t n
, result= set(Terminal)
} (* end of [STATE] *)
//
in // in of [local]
//
implement
STATE_init {n} (nterms, ntermmap, fsets, nodecount, env) = let
//
  prval () = let
    extern praxi
      __assert (!STATENODE0 >> STATE (0)): void
  in
    __assert (env)
  end
//
  prval () = let
    extern
    prfun
    arrayptr_zero_free {a:t0p}{l:addr} (arrayptr (INV(a), l, 0)):<> void
  in
    arrayptr_zero_free (env.nterms);
    arrayptr_zero_free (env.fsets)
  end
//
  val () = env.nterms := nterms
  val () = env.ntermmap := ntermmap
  val () = env.fsets := fsets
  val () = env.nodecount := nodecount
  val () = env.result := funset_nil {T} ()
//
in
  (*empty*)
end // end of [STATE_init]
//
implement
STATE_getres_free {n} (nterms, fsets, env) = let
  val res = env.result
  val () = nterms := env.nterms
  val () = fsets := env.fsets
  prval () = __assert (env) where {
    extern
    prfun
    __assert {a:vt0p} (&a >> STATENODE0): void
  } (* end of [val] *)
in
  res
end // end of [STATE_getres_free]
//
implement
STATE_get_nodecount {n} (env) = env.nodecount
//
implement
STATE_scan {n,nxs} (env, X, xs) = let
  fnx
  notfound {nxs:nat} (X: N, xs: list (S, nxs), env: &STATE (n) >> STATE (n)): void =
    case+ xs of
    | list_cons (a, xs) => (
      if Symbol_is_terminal (a) then notfound (X, xs, env)
      else begin (*a is nonterminal*)
        if a = X then found (X, xs, env)
        else notfound (X, xs, env)
      end // end of [if]
    ) (* end of [list_cons] *)
    | list_nil () => ((*stop*))
  // end of [notfound]
  and
  found {nxs:nat} (X:N, xs: list (S, nxs), env: &STATE(n) >> STATE(n)): void =
    case+ xs of
    | list_cons (a, xs) => (
      if :(env: STATE(n)) => Symbol_is_terminal (a) then let
        val _ = funset_insert<T> (env.result, a)
      in
        notfound (X, xs, env)
      end else let (* a is nonterminal *)
        var a_id : size_t
        val-true = funmap_search<Nonterminal,size_t> (env.ntermmap, a, a_id)
        prval () = opt_unsome {size_t} (a_id)
        val a_id = $UN.cast{sizeLt(n)} (a_id)
        val fst = arrayptr_get_at_guint<tset> (env.fsets, a_id)
        val res1 = env.result
        val () = env.result := funset_union<T> (res1, fst)
      in
        notfound (X, xs, env)
      end // end of [if]
    ) (* end of [list_cons] *)
    | list_nil () => ((*stop*))
  // end of [found]
in
  notfound (X, xs, env)
end // end of [STATE_scan]
//
end // end of [local]
//
implement
INITFOLLOW {n} (gr, A, nterms, ntermmap, fsets, nodecount) = let
  //
  val Grammar (alphabet, prods, _) = gr
  //
  val p_nterms = arrayptr2ptr (nterms)
  val p_fsets = arrayptr2ptr (fsets)
  //
  implement
  funmap_foreach$fwork<int,Production><STATE> (k, x, env) = let
    val Prod (lhs, rhs) = x
    prval () = lemma_list_param (rhs)
    val () = STATE_scan (env, A, rhs)
  in
  end // end of [funmap_foreach$fwork]
  //
  var env: STATENODE0
  val () = STATE_init (nterms, ntermmap, fsets, nodecount, env)
  val () = funmap_foreach_env<int,Production><STATE> (prods, env)
  val nodecount1 = STATE_get_nodecount (env)
  val () = assert_errmsg (nodecount = nodecount1, "node count changed!")
  val res = STATE_getres_free (nterms, fsets, env)
  //
  val p_nterms1 = arrayptr2ptr (nterms)
  val p_fsets1 = arrayptr2ptr (fsets)
  val () = assert_errmsg (p_nterms = p_nterms1, "nterms changed!")
  val () = assert_errmsg (p_fsets = p_fsets1, "fsets changed!")
  //
in
  res
end // end of [INITFOLLOW]
//
extern
fun
GFOLLOW {n:nat} (
  Grammar
, &arrayptr (Nonterminal, n)
, map (Nonterminal, size_t)
, size_t (n)
): digraph (n)
//
implement
GFOLLOW {n} (gr, nonterms, nontermmap, nodecount) = let
  typedef nodes = set(Nonterminal)
  val Grammar (alphabet, prods, _) = gr

  implement
  funmap_foreach$fwork<Nonterminal,size_t><digraph> (ntm, idx, env) = let
    implement
    funmap_foreach$fwork<int,Production><digraph> (k, x, env) =
      if Production_derives(x) <> ntm then let
(*
        val () = fprintln!(stdout_ref, "considering production: ", x)
*)
        // production is of the form ntm -> rhs
        val Prod (_, rhs) = x
        prval () = lemma_list_param (rhs)
      in
        if list_is_nil (rhs) then ((*empty*))
        else let
          val y = list_last (rhs)
        in
          if Symbol_is_nonterminal (y) then {
            // production is of the form ntm -> alpha y,
            // where y is some nonterminal (y <> ntm)
            //
            // add the edge!
(*
            val () = fprint!(stdout_ref, "found edge from: ")
            val () = fprint_Symbol (stdout_ref, ntm)
            val () = fprint!(stdout_ref, " to: ")
            val () = fprint_Symbol (stdout_ref, y)
            val () = fprint_newline (stdout_ref)
*)
            var idx_y : size_t
            val-true = funmap_search<Nonterminal,size_t> (nontermmap, y, idx_y)
            prval () = opt_unsome {size_t} (idx_y)
            val n = fundigraph_size (env)
            prval [n:int] EQINT () = eqint_make_guint (n)
            val idx = $UN.cast{sizeLt(n)} (idx)
            val idx_y = $UN.cast{sizeLt(n)} (idx_y)
            val _ = fundigraph_insert_edge (env, idx, idx_y)
          } (* end of [if] *)
        end // end of [let]
      end // end of [funmap_foreach$fwork]
  in
    funmap_foreach_env<int,Production><digraph> (prods, env)
  end
  var graph = fundigraph_make (nodecount)
  val () = funmap_foreach_env<Nonterminal,size_t><digraph> (nontermmap, graph)
//
  val nsz = fundigraph_size (graph)
  val () = assert_errmsg (nsz = nodecount, "digraph vertex count changed!")
//
in
  graph
end // end of [GFOLLOW]
//
in // in of [local]

implement
FOLLOWSETS {n} (gr, nterms, nontermmap, fsets, nodecount) = let
  // compute the GFOLLOW graph
  val gfollow = GFOLLOW (gr, nterms, nontermmap, nodecount)
  // allocate init and final arrays
  val (pf_init, pf_init_free | p_init) = array_ptr_alloc<set(Terminal)> (nodecount)
  val (pf_fin, pf_fin_free | p_fin) = array_ptr_alloc<set(Terminal)> (nodecount)
  // initialize
  typedef T = set(Terminal)
  //
  fun
  initflw_initize{n:int} (
    A: &(@[T?][n]) >> @[T][n]
  , asz: size_t n
  , nterms: &arrayptr (Nonterminal, n) (*numbered nonterminals*)
  , ntermmap: map (Nonterminal, size_t) (*nontermmap*)
  , fsets: &arrayptr (set(Terminal), n)(*first sets*)
  ): void = let
  //
  stadef V = array_v
  //
  fun loop
  {l:addr}{n,m,i:nat | i <= m; n+i==m} .<n>.
  (
    pf: !V (T?, l, n) >> V (T, l, n)
  | p: ptr l, n: size_t n, i: size_t i
  , nterms: &arrayptr (Nonterminal, m) (*numbered nonterminals*)
  , nontermmap: map (Nonterminal, size_t) (*nontermmap*)
  , fsets: &arrayptr (set(Terminal), m)(*first sets*)
  , nodecount: size_t (m)
  ) : void = (
    if n > 0 then let
      prval (pf1, pf2) = array_v_uncons (pf)
      val ntm = arrayptr_get_at_guint (nterms, i)
      val () = !p := INITFOLLOW (gr, ntm, nterms, nontermmap, fsets, nodecount)
      val () = loop (
        pf2 | ptr1_succ<T> (p), pred(n), succ(i), nterms, nontermmap, fsets, nodecount
      ) (* end of [val] *)
      prval () = pf := array_v_cons{T}(pf1, pf2)
    in
      // nothing
    end else let
      prval () = pf := array_v_unnil_nil (pf)
    in
      // nothing
    end // end of [if]
  ) (* end of [loop] *)
  //
  prval () = lemma_g1uint_param (asz)
  //
  in
    loop (
      view@ (A)
    | addr@ (A), asz, i2sz(0), nterms, nontermmap, fsets, asz
    )
  end // end of [initflw_initize]
  //
  // for each nonterminal, obtain its INITFOLLOW set
  val () = initflw_initize (!p_init, nodecount, nterms, nontermmap, fsets)
  //
  (*
  val () = fprintln!(stdout_ref, "INITFOLLOW array:")
  implement
  fprint_val<T> (out, x) = let
    val () = fprintln!(out, "{")
    val () = fprint_funset<Terminal> (out, x)
    val () = fprint!(out, "}")
  in
  end // end of [fprint_val]
  val () = fprint_array<T> (stdout_ref, !p_init, nodecount)
  val () = fprint_newline (stdout_ref)
  *)
  //
  val () = gsolve<Terminal> (gfollow, !p_init, !p_fin)
  //
  val () = array_ptr_free (pf_init, pf_init_free | p_init)
  //
in
  arrayptr_encode (pf_fin, pf_fin_free | p_fin)
end // end of [FOLLOWSETS]
//
end /// end of [local]
//
(* ****** ****** *)

dynload "./fundigraph.dats"

(* ****** ****** *)

implement
main0 () = let

// setup a simple grammar
val _sS = Nterm("S")
val _sE = Nterm("E")
val _sT = Nterm("T")
val _sF = Nterm("F")
val _sa = Term("a")
val _sLPAREN = Term("(")
val _sRPAREN = Term(")")
val _sPLUS = Term("+")
val _sMINUS = Term("-")
val _sSTAR = Term("*")

val xs =
$list_vt{Symbol}(_sS, _sE, _sT, _sF, _sa, _sLPAREN, _sRPAREN, _sPLUS, _sMINUS, _sSTAR, sym_EOF, sym_EPS)
var alphabet = funset_make_list ($UN.list_vt2t(xs))
val () = list_vt_free (xs)

var prods = funmap_make_nil{int,Production} ()
var res: Production
val-false = funmap_insert (prods, 0, Prod (_sS, $list{Symbol}(_sE, sym_EOF)), res)
prval () = opt_clear (res)
val-false = funmap_insert (prods, 1, Prod (_sE, $list{Symbol}(_sE, _sPLUS, _sT)), res)
prval () = opt_clear (res)
val-false = funmap_insert (prods, 2, Prod (_sE, $list{Symbol}(_sT)), res)
prval () = opt_clear (res)
val-false = funmap_insert (prods, 3, Prod (_sT, $list{Symbol}(_sT, _sSTAR, _sF)), res)
prval () = opt_clear (res)
val-false = funmap_insert (prods, 4, Prod (_sT, $list{Symbol}(_sF)), res)
prval () = opt_clear (res)
val-false = funmap_insert (prods, 5, Prod (_sF, $list{Symbol}(_sLPAREN, _sE, _sRPAREN)), res)
prval () = opt_clear (res)
val-false = funmap_insert (prods, 6, Prod (_sF, $list{Symbol}(_sMINUS, _sT)), res)
prval () = opt_clear (res)
val-false = funmap_insert (prods, 7, Prod (_sF, $list{Symbol}(_sa)), res)
prval () = opt_clear (res)

var gr = Grammar (alphabet, prods, 0(*start rule*))

val () = fprintln!(stdout_ref, "grammar: ", gr)
//
implement
funset_filter$pred<Symbol> (x) = case+ x of Nterm _ => false | _ => true
implement(env)
funset_filter$fwork<Symbol><env> (x, env) = fprint_Symbol (stdout_ref, x)
//
var env: void
val () = fprint!(stdout_ref, "terminals:")
val () = funset_filter_env<Symbol> (alphabet, env)
//
implement
funset_filter$pred<Symbol> (x) = case+ x of Nterm _ => true | _ => false
implement(env)
funset_filter$fwork<Symbol><env> (x, env) =
  (fprint_Symbol (stdout_ref, x); fprint_newline (stdout_ref))
val () = fprint!(stdout_ref, "nonterminals:")
val nonterminals = funset_filter_env<Symbol> (alphabet, env)
//
val () = fprint!(stdout_ref, "productions starting with: ")
val () = fprint_Symbol (stdout_ref, _sE)
val () = fprint_newline (stdout_ref)
implement
funmap_filter$pred<int,Production> (k, x) = Production_derives (x) = _sE
implement(env)
funmap_filter$fwork<int,Production><env> (k, x, env) = fprintln!(stdout_ref, x)
val () = funmap_filter_env<int,Production> (prods, env)
//
(*
val () = fprintln!(stdout_ref, "INITFIRST(E) = ", INITFIRST (gr, _sE))
val () = fprintln!(stdout_ref, "INITFIRST(S) = ", INITFIRST (gr, _sS))
val () = fprintln!(stdout_ref, "INITFIRST(F) = ", INITFIRST (gr, _sF))
*)
//
(*
var nnode_gfirst: size_t
var arrnode: ptr
val gfirst = GFIRST (gr, nnode_gfirst, arrnode)
val () = fprintln!(stdout_ref, "GFIRST(gr) = ")
val () = fprint_fundigraph (stdout_ref, gfirst)
val () = fprint_newline (stdout_ref)
val () = arrayptr_free (arrnode)
*)
//
var nonterms: ptr
var nontermmap: ptr
val nodecount = Grammar_nonterminals (gr, nonterms, nontermmap)

val () = fprintln!(stdout_ref, "calling FIRSTSETS")
prval () = lemma_g1uint_param (nodecount)
var fstsets = FIRSTSETS (gr, nonterms, nontermmap, nodecount)
//
val () = fprintln!(stdout_ref, "FIRSTSETS(gr) = ")
val () = fprintln!(stdout_ref, "nonterminals array:")
val () = fprint_arrayptr<Nonterminal> (stdout_ref, nonterms, nodecount)
val () = fprint_newline (stdout_ref)
//
val () = fprintln!(stdout_ref, "first set termsets array:")
implement
fprint_val<set(Terminal)> (out, x) = let
  val () = fprintln!(out, "{")
  val () = fprint_funset<Terminal> (out, x)
  val () = fprint!(out, "}")
in
end // end of [fprint_val]
val () = fprint_arrayptr<set(Terminal)> (stdout_ref, fstsets, nodecount)
val () = fprint_newline (stdout_ref)
//
var flwsets = FOLLOWSETS (gr, nonterms, nontermmap, fstsets, nodecount)
//
val () = fprintln!(stdout_ref, "followset termsets array:")
implement
fprint_val<set(Terminal)> (out, x) = let
  val () = fprintln!(out, "{")
  val () = fprint_funset<Terminal> (out, x)
  val () = fprint!(out, "}")
in
end // end of [fprint_val]
val () = fprint_arrayptr<set(Terminal)> (stdout_ref, flwsets, nodecount)
val () = fprint_newline (stdout_ref)
//
val () = arrayptr_free (nonterms)
val () = arrayptr_free (fstsets)
val () = arrayptr_free (flwsets)
//
in
end