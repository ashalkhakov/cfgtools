#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

staload "./../utils/SATS/fundigraph.sats"
staload _(*anon*) = "./../utils/DATS/fundigraph.dats"

staload "libats/SATS/funset_avltree.sats"
staload _(*anon*) = "libats/DATS/funset_avltree.dats"

staload "libats/SATS/funmap_avltree.sats"
staload
_(*anon*) = "libats/DATS/funmap_avltree.dats"
staload
_(*anon*) = "libats/DATS/qlist.dats"

staload "./../SATS/grm.sats"
staload _ = "./../DATS/grm.dats"
staload "./../SATS/grmfuncs.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)
//
implement
ERASABLE {n} (gr, nterms, ntermmap, nodecount) = let
  val (pf_arr, pf_arr_free | p_arr) = array_ptr_alloc<bool> (nodecount)
  val () = array_initize_elt<bool> (!p_arr, nodecount, false)
  var erasable = arrayptr_encode {bool} (pf_arr, pf_arr_free | p_arr)
  //
  // NOTE: the type is curious; the index [n] is hidden to ensure
  // that templates are instantiated properly
  vtypedef Env = @([n1:nat | n1 == n] arrayptr (bool, n1), bool(*change*))
  //
  val alphabet = Grammar_get_syms (gr)
  val prods = Grammar_get_prods (gr)
  //
  implement
  funmap_foreach$fwork<Production,size_t><Env> (x, k, env) = let
    val Prod (ntm, rhs) = x
  in
    case+ rhs of
    | list_cons (sym, list_nil ()) when sym = sym_EPS => let
(*
        val () = fprint! (stdout_ref, "nonterminal ")
        val () = fprint_Symbol (stdout_ref, ntm)
        val () = fprintln! (stdout_ref, " is trivially erasable due to ", x)
*)
        var idx : size_t
        val-true = funmap_search<Nonterminal,size_t> (ntermmap, ntm, idx)
        prval () = opt_unsome {size_t} (idx)
        val i = $UN.cast{sizeLt(n)} (idx)
      in
        arrayptr_set_at_guint (env.0, i, true)
      end // end of [let]
    | _ => ()
  end // end of [funmap_foreach$fwork]
  var env = @(erasable, false) : Env
  val () = funmap_foreach_env<Production,size_t><Env> (prods, env)
//
  fun
  aux (env: &Env >> _): void = let
    implement
    funmap_foreach$fwork<Production,size_t><Env> (x, k, env) = let
      val Prod (ntm, rhs) = x
      val len = list_length(rhs)
      implement
      list_iforeach$fwork<Symbol><Env> (i, x, env) = ()
      implement
      list_iforeach$cont<Symbol><Env> (_, x, env) =
        if Symbol_is_terminal (x) then false
        else let
          var idx : size_t
          val-true = funmap_search<Nonterminal,size_t> (ntermmap, x, idx)
          prval () = opt_unsome {size_t} (idx)
          val i = $UN.cast{sizeLt(n)} (idx)
          val res = arrayptr_get_at_guint (env.0, i)
(*
          val () = fprint! (stdout_ref, "erasable(")
          val () = fprint_Symbol (stdout_ref,  x)
          val () = fprintln! (stdout_ref, ") = ", res)
*)
        in
          res
        end // end of [list_foreach$cont]
      val len1 = list_iforeach_env<Symbol><Env> (rhs, env)
      //
      val () = fprintln!(stdout_ref, "len = ", len, ", len1 = ", len1)
      //
      var idx : size_t
      val-true = funmap_search<Nonterminal,size_t> (ntermmap, ntm, idx)
      prval () = opt_unsome {size_t} (idx)
      val i = $UN.cast{sizeLt(n)} (idx)
    in
      if  (len = len1) && (arrayptr_get_at_guint<bool> (env.0, i) = false) then let
        val () = arrayptr_set_at_guint<bool> (env.0, i, true)
      in
        env.1 := true
      end
    end // end of [funmap_foreach$fwork]
    val () = env.1 := false
    val () = funmap_foreach_env<Production,size_t><Env> (prods, env)
    // how to determine if something changed?
  in
    if env.1 then aux (env)
  end // end of [aux]
  val () = aux (env)
in
  env.0
end // end of [ERASABLE]
//
(* ****** ****** *)
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
local
//
extern
fun
INITFIRST {n:nat} (Grammar, Nonterminal, &arrayptr(bool,n) >> _, map (Nonterminal,size_t), nodecount: size_t(n)): set(Terminal)
//
implement
INITFIRST {n} (gr, X, erasable, ntermmap, nodecount) = let
//
vtypedef Env = @([n1:nat | n1 == n] arrayptr (bool, n1), set(Terminal))
//
val alphabet = Grammar_get_syms (gr)
val prods = Grammar_get_prods (gr)
//
implement
funmap_foreach$fwork<Production,size_t><Env> (x, k, env) = let
//
fun
aux0 (xs: List (Symbol), erasable: &arrayptr (bool, n), res: &set(Terminal) >> _): void =
  if list_is_cons (xs) then let
    val+ list_cons (x, xs) = xs
    prval () = lemma_list_param (xs)
  in
    if Symbol_is_terminal (x) then let
    in
      if x = sym_EPS then let
        val () = aux0 (xs, erasable, res)
      in
      end else let
      (*
        val () = fprintln!(stdout_ref, "inserting!")
      *)
        val _ = funset_insert<Terminal> (res, x)
      in
        (*empty*)
      end
    end else let
      var idx : size_t
      val-true = funmap_search<Nonterminal,size_t> (ntermmap, x, idx)
      prval () = opt_unsome {size_t} (idx)
      val i = $UN.cast{sizeLt(n)} (idx)
      val e = arrayptr_get_at_guint (erasable, i)
    in
      if e then aux0 (xs, erasable, res)
    end
  end // end of [aux0]
//
in
  if :(env: Env) => Production_derives(x) = X then let
    val Prod (_, rhs) = x
    (*
    val () = fprint!(stdout_ref, "working on: ")
    val () = fprint_Production (stdout_ref, x)
    val () = fprint_newline (stdout_ref)
    *)
    prval () = lemma_arrayptr_param (env.0)
    var env0 = env.0
    var env1 = env.1
    val () = aux0 (rhs, env0, env1)
    val () = env.0 := env0
    val () = env.1 := env1
  in
  end
end // end of [funmap_foreach$fwork]
var env = @(erasable, funset_nil{Terminal} ()) : Env
val () = funmap_foreach_env<Production,size_t><Env> (prods, env)
val () = erasable := env.0
val res = env.1
prval () = topize (env.1)
//
in
  res
end // end of [INITFIRST]
//
extern
fun
GFIRST {n:nat} (
  Grammar
, &arrayptr (bool, n) >> _
, &arrayptr (Nonterminal, n)
, map (Nonterminal, size_t)
, size_t (n)
): digraph(n)
implement
GFIRST {n} (gr, erasable, nonterms, nontermmap, nodecount) = let
  typedef nodes = set(Nonterminal)
//
  val alphabet = Grammar_get_syms (gr)
  val prods = Grammar_get_prods (gr)
//
vtypedef Env = @([n1:nat | n1 == n] arrayptr (bool, n1), [n1:nat | n1 == n] digraph (n1))
//
fun
aux0 (x: Nonterminal, j: sizeLt(n), ys: List (Symbol), env: &Env >> _): void =
  if list_is_cons (ys) then let
    val+ list_cons (y, ys) = ys
  in
    if Symbol_is_nonterminal (y) then let
      var idx_y : size_t
      val-true = funmap_search<Nonterminal,size_t> (nontermmap, y, idx_y)
      prval () = opt_unsome {size_t} (idx_y)
      val i = $UN.cast{sizeLt(n)} (idx_y)

      val () = fprint!(stdout_ref, "firstset: considering edge ")
      val () = fprint_Symbol (stdout_ref, x)
      val () = fprint!(stdout_ref, " to ")
      val () = fprint_Symbol (stdout_ref, y)
      val () = fprint_newline (stdout_ref)

    in
      if i <> j then let
        val nil = arrayptr_get_at_guint<bool> (env.0, i)
      in
        if nil = false then let

          val () = fprint!(stdout_ref, "found an edge from: ")
          val () = fprint_Symbol (stdout_ref, x)
          val () = fprint!(stdout_ref, " to: ")
          val () = fprint_Symbol (stdout_ref, y)
          val () = fprint_newline (stdout_ref)

          val _ = fundigraph_insert_edge (env.1, j, i)
        in
          (*empty*)
        end else let
          val () = fprintln!(stdout_ref, "skipping, because nilable")
        in
          aux0 (x, j, ys, env) // nilable
          (*empty*)
        end
      end
    end
  end // end of [aux0]
//
  implement
  funmap_foreach$fwork<Nonterminal,size_t><Env> (ntm, idx, env) = let
    implement
    funmap_foreach$fwork<Production,size_t><Env> (x, k, env) =
      if Production_derives(x) = ntm then let

        val () = fprintln!(stdout_ref, "considering production: ", x)

        // production is of the form ntm -> rhs
        val Prod (_, rhs) = x
        var idx : size_t
        val-true = funmap_search<Nonterminal,size_t> (nontermmap, ntm, idx)
        prval () = opt_unsome {size_t} (idx)
        val i = $UN.cast{sizeLt(n)} (idx)

        val () = fprint_Symbol (stdout_ref, ntm)
        val () = fprintln!(stdout_ref, " maps to ", i)

      in
        aux0 (ntm, i, rhs, env)
      end // end of [funmap_foreach$fwork]
  in
    funmap_foreach_env<Production,size_t><Env> (prods, env)
  end
  var env = @(erasable, fundigraph_make (nodecount)) : Env
  val () = funmap_foreach_env<Nonterminal,size_t><Env> (nontermmap, env)
//
  val () = erasable := env.0
  val res = env.1
  prval () = topize (env.1)
//
  val () = fprintln!(stdout_ref, "GFIRST(gr) = ")
  val () = fprint_fundigraph (stdout_ref, res)
  val () = fprint_newline (stdout_ref)
//
in
  res
end // end of [GFIRST]
//
in // in of [local]
//
implement
FIRSTSETS {n} (
  gr
, erasable
, nterms
, nontermmap
, nodecount
) = let
  // compute the GFIRST graph
  val gfirst = GFIRST (gr, erasable, nterms, nontermmap, nodecount)

  // allocate init and final arrays
  val (pf_init, pf_init_free | p_init) = array_ptr_alloc<set(Terminal)> (nodecount)
  val (pf_fin, pf_fin_free | p_fin) = array_ptr_alloc<set(Terminal)> (nodecount)
  //
  typedef T = set(Terminal)
  // for each nonterminal, obtain its INITFIRST set
  var i: int = 0
  prval [lres:addr] EQADDR () = eqaddr_make_ptr (p_init)
  var p = p_init
  prvar pf0 = array_v_nil {T} ()
  prvar pf1 = pf_init
  //
  val () =
  while* {i:nat | i <= n} .<n-i>. (
    i: int (i)
  , p: ptr (lres + i*sizeof(T))
  , pf0: array_v (T, lres, i)
  , pf1: array_v (T?, lres+i*sizeof(T), n-i)
  ) : (
    pf0: array_v (T, lres, n)
  , pf1: array_v (T?, lres+i*sizeof(T), 0)
  ) => (
    (i2sz)i < nodecount
  ) {
  //
    prval (pf_at, pf1_res) = array_v_uncons {T?} (pf1)
    prval () = pf1 := pf1_res
    val ntm = nterms[i]
    val e = INITFIRST (gr, ntm, erasable, nontermmap, nodecount)
(*
    val () = fprintln! (stdout_ref, "for nonterminal: ")
    val () = fprint_Symbol (stdout_ref, ntm)
    val () = fprint_newline (stdout_ref)
    val () = fprintln! (stdout_ref, "the termset is:")
    val () = fprint_funset<Terminal> (stdout_ref, e)
    val () = fprint_newline (stdout_ref)
*)
    val () = ptr_set<T> (pf_at | p, e)
    val () = p := ptr1_succ<T> (p)
    prval () = pf0 := array_v_extend {T} (pf0, pf_at)
    val () = i := i + 1
  //
  } // end of [val]
  //
  prval () = pf_init := pf0
  prval () = array_v_unnil {T?} (pf1)
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
implement
FIRST {n,m} (xs, erasable, nterms, ntermmap, nodecount, fsets) = let
  //
  fun
  is_erasable (x: Symbol, erasable: &arrayptr (bool, n)): bool =
    if Symbol_is_terminal (x) then (x = sym_EPS)
    else let
      var idx : size_t
      val-true = funmap_search<Nonterminal,size_t> (ntermmap, x, idx)
      prval () = opt_unsome {size_t} (idx)
      val i = $UN.cast{sizeLt(n)} (idx)
    in
      arrayptr_get_at_guint<bool> (erasable, i)
    end
  // end of [is_erasable]
  fun
  aux (sym: Symbol, fsets: &arrayptr (set(Terminal), n), res: &set(Terminal) >> _):void =
    if Symbol_is_terminal (sym) then {
      val _ = funset_insert<Terminal> (res, sym)
    } else {
      var idx : size_t
      val-true = funmap_search<Nonterminal,size_t> (ntermmap, sym, idx)
      prval () = opt_unsome {size_t} (idx)
      val i = $UN.cast{sizeLt(n)} (idx)
      val fs = fsets[i]
      val () = res := funset_union<Terminal> (fs, res)
    } (* end of [aux] *)
  // end of [aux]
  fun
  loop {m:nat} (
    syms: list (Symbol, m)
  , erasable: &arrayptr (bool, n)
  , fsets: &arrayptr (set(Terminal), n)
  , res: &set(Terminal) >> _
  ): void =
    case+ syms of
    | list_nil () => ()
    | list_cons (x, xs) => let
        val () = aux (x, fsets, res)
      in
        if is_erasable (x, erasable) then loop (xs, erasable, fsets, res)
      end // end of [loop]
  var res = funset_nil {Terminal} ()
  val () = loop (xs, erasable, fsets, res)
in
  res
end // end of [FIRST]
//
end // end of [local]
//
(* ****** ****** *)
//
local
//
extern
fun
INITFOLLOW {n:nat} (
  Grammar
, Nonterminal(*nonterminal*)
, &arrayptr (bool, n)
, &arrayptr (Nonterminal, n)(*numbered nonterminals*)
, map (Nonterminal, size_t)
, &arrayptr (set(Terminal), n)(*first sets*)
, size_t n
): set(Terminal)
//
typedef STATENODE (n:int) = @{
  erasable= ptr
, nterms= ptr
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
  erasable: arrayptr (bool, n)
, nterms: arrayptr (Nonterminal, n)(*numbered nonterminals*)
, ntermmap: map (Nonterminal, size_t)
, fsets: arrayptr (set(Terminal), n)(*first sets*)
, nodecount: size_t n
, &STATENODE0 >> STATE (n)
): void
//
extern
fun
STATE_getres_free {n:nat} (
  &ptr? >> arrayptr (bool, n)
, &ptr? >> arrayptr (Nonterminal, n)(*numbered nonterminals*)
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
STATE_scan {n:nat;nxs:pos} (
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
  erasable= arrayptr (bool, n)
, nterms= arrayptr (Nonterminal, n)(*numbered nonterminals*)
, ntermmap= map (Nonterminal, size_t)
, fsets= arrayptr (set(Terminal), n)(*first sets*)
, nodecount= size_t n
, result= set(Terminal)
} (* end of [STATE] *)
//
in // in of [local]
//
implement
STATE_init {n} (erasable, nterms, ntermmap, fsets, nodecount, env) = let
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
    arrayptr_zero_free (env.erasable);
    arrayptr_zero_free (env.nterms);
    arrayptr_zero_free (env.fsets)
  end
//
  val () = env.erasable := erasable
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
STATE_getres_free {n} (erasable, nterms, fsets, env) = let
  val res = env.result
  val () = erasable := env.erasable
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
    if list_is_cons (xs) then let
      val fst = FIRST (xs, env.erasable, env.nterms, env.ntermmap, env.nodecount, env.fsets)
      val () = env.result := funset_union<Terminal> (env.result, fst)
    in
    end // end of [found]
in
  notfound (X, xs, env)
end // end of [STATE_scan]
//
end // end of [local]
//
implement
INITFOLLOW {n} (gr, A, erasable, nterms, ntermmap, fsets, nodecount) = let
  //
  val alphabet = Grammar_get_syms (gr)
  val prods = Grammar_get_prods (gr)
  //
  val p_erasable = arrayptr2ptr (erasable)
  val p_nterms = arrayptr2ptr (nterms)
  val p_fsets = arrayptr2ptr (fsets)
  //
  implement
  funmap_foreach$fwork<Production,size_t><STATE> (x, k, env) = let
    val Prod (lhs, rhs) = x
    prval () = lemma_list_param (rhs)
    val () = STATE_scan (env, A, rhs)
  in
  end // end of [funmap_foreach$fwork]
  //
  var env: STATENODE0
  val () = STATE_init (erasable, nterms, ntermmap, fsets, nodecount, env)
  val () = funmap_foreach_env<Production,size_t><STATE> (prods, env)
  val nodecount1 = STATE_get_nodecount (env)
  val () = assert_errmsg (nodecount = nodecount1, "node count changed!")
  val res = STATE_getres_free (erasable, nterms, fsets, env)
  //
  val p_erasable1 = arrayptr2ptr (erasable)
  val p_nterms1 = arrayptr2ptr (nterms)
  val p_fsets1 = arrayptr2ptr (fsets)
  val () = assert_errmsg (p_erasable = p_erasable1, "erasable changed!")
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
, &arrayptr (bool, n) >> _
, &arrayptr (Nonterminal, n) >> _
, map (Nonterminal, size_t)
, size_t (n)
): digraph (n)
//
implement
GFOLLOW {n} (gr, erasable, nonterms, nontermmap, nodecount) = let
  typedef nodes = set(Nonterminal)
//
  val alphabet = Grammar_get_syms (gr)
  val prods = Grammar_get_prods (gr)
//
  val () = fprintln!(stdout_ref, "computing GFOLLOW")
//
  vtypedef Env = @([n1:nat | n1 == n] arrayptr (bool, n1), [n1:nat | n1 == n] digraph (n1))

  // there is an edge from nonterminal A to nonterminal B if:
  // - there is a production B->alpha A, or
  // - there is a production B->alpha A A1...Ak, s.t. E(A1) = ... = E(Ak) = true
//
  implement
  funmap_foreach$fwork<Nonterminal,size_t><Env> (A, idx, env) = let
    val idx = $UN.cast{sizeLt(n)} (idx)

    val () = fprint!(stdout_ref, "considering nonterminal: ")
    val () = fprint_Symbol (stdout_ref, A)
    val () = fprint_newline (stdout_ref)

    implement
    funmap_foreach$fwork<Production,size_t><Env> (x, k, env) = let
      val B = Production_derives (x)
    in
      if B <> A then let

        val () = fprintln!(stdout_ref, "considering production: ", x)

        // production is of the form B -> rhs, where A <> B
        val Prod (_, rhs) = x
        prval () = lemma_list_param (rhs)
//
        fun
        loop {m:nat} (rhs: list_vt (Symbol, m), B: Nonterminal, A: Nonterminal, j: sizeLt(n), env: &Env >> _): void =
          case+ rhs of
          | ~list_vt_nil () => ()
          | ~list_vt_cons (y, rhs) =>
            if Symbol_is_nonterminal (y) then let
              var idx_y : size_t
              val-true = funmap_search<Nonterminal,size_t> (nontermmap, y, idx_y)
              prval () = opt_unsome {size_t} (idx_y)
              val i = $UN.cast{sizeLt(n)} (idx_y)
              val nil = arrayptr_get_at_guint<bool> (env.0, i)
            in
              if nil then loop (rhs, B, A, j, env)
              else if y = A then let
                // production is of the form B -> alpha A beta
                val () = list_vt_free<Symbol> (rhs)
                var idx_B : size_t
                val-true = funmap_search<Nonterminal,size_t> (nontermmap, B, idx_B)
                prval () = opt_unsome {size_t} (idx_B)
                val i = $UN.cast{sizeLt(n)} (idx_B)

                val () = fprint!(stdout_ref, "found edge from: ")
                val () = fprint_Symbol (stdout_ref, A)
                val () = fprint!(stdout_ref, "(", j, ")")
                val () = fprint!(stdout_ref, " to: ")
                val () = fprint_Symbol (stdout_ref, B)
                val () = fprint!(stdout_ref, "(", i, ")")
                val () = fprint_newline (stdout_ref)

                // only add if it isn't already there?
                val _ = fundigraph_insert_edge (env.1, j, i)
              in
                (*empty*)
              end else let
                val () = list_vt_free<Symbol> (rhs)
              in
                (*empty*)
              end // end of [if]
            end else let
              val () = list_vt_free<Symbol> (rhs)
            in
              (*empty*)
            end // end of [loop]
        val rhs = list_reverse (rhs)
      in
        loop (rhs, B, A, idx, env)
      end
    end // end of [funmap_foreach$fwork]
  in
    funmap_foreach_env<Production,size_t><Env> (prods, env)
  end
//
  var env = @(erasable, fundigraph_make (nodecount)) : Env
  val () = funmap_foreach_env<Nonterminal,size_t><Env> (nontermmap, env)
  val () = erasable := env.0
  val res = env.1
  prval () = topize (env.1)
//
  val () = fprintln!(stdout_ref, "GFOLLOW(gr) = ")
  val () = fprint_fundigraph (stdout_ref, res)
  val () = fprint_newline (stdout_ref)
//
in
  res
end // end of [GFOLLOW]
//
in // in of [local]
//
implement
FOLLOWSETS {n} (gr, erasable, nterms, nontermmap, fsets, nodecount) = let
  // compute the GFOLLOW graph
  val gfollow = GFOLLOW (gr, erasable, nterms, nontermmap, nodecount)
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
  , erasable: &arrayptr (bool, n)
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
  , erasable: &arrayptr (bool, m)
  , nterms: &arrayptr (Nonterminal, m) (*numbered nonterminals*)
  , nontermmap: map (Nonterminal, size_t) (*nontermmap*)
  , fsets: &arrayptr (set(Terminal), m)(*first sets*)
  , nodecount: size_t (m)
  ) : void = (
    if n > 0 then let
      prval (pf1, pf2) = array_v_uncons (pf)
      val ntm = arrayptr_get_at_guint (nterms, i)
      val () = !p := INITFOLLOW (gr, ntm, erasable, nterms, nontermmap, fsets, nodecount)
      val () = loop (
        pf2 | ptr1_succ<T> (p), pred(n), succ(i), erasable, nterms, nontermmap, fsets, nodecount
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
    | addr@ (A), asz, i2sz(0), erasable, nterms, nontermmap, fsets, asz
    )
  end // end of [initflw_initize]
  //
  // for each nonterminal, obtain its INITFOLLOW set
  val () = initflw_initize (!p_init, nodecount, erasable, nterms, nontermmap, fsets)
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
