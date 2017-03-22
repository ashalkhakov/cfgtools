#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

staload "./../utils/SATS/fundigraph.sats"
staload _(*anon*) = "./../utils/DATS/fundigraph.dats"

staload "libats/SATS/funset_avltree.sats"
staload _(*anon*) = "libats/DATS/funset_avltree.dats"

staload "./../SATS/grm.sats"

staload "libats/SATS/funmap_avltree.sats"

staload
_(*anon*) = "libats/DATS/qlist.dats"
staload
_(*anon*) = "libats/DATS/funmap_avltree.dats"

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

//local

datatype SYMBOL (b:bool) = Nterm (false) of string | Term(true) of string
assume Symbol (b:bool) = SYMBOL (b)

//in // in of [local]

implement
sym_EOF = Term("EOF")
implement
sym_EPS = Term("EPS")

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

implement
Symbol_is_terminal {b} (x) =
  case+ x of Nterm _ => false | Term _ => true
implement
Symbol_is_nonterminal {b} (x) =
  case+ x of Nterm _ => true | Term _ => false

implement
Symbol_terminal (lab) = Term(lab)
implement
Symbol_nonterminal (lab) = Nterm(lab)

//end // end of [local]

(* ****** ****** *)

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

implement
compare_Production_Production (p1, p2) = let
  val+Prod (lhs1, rhs1) = p1
  val+Prod (lhs2, rhs2) = p2
  val res = compare (lhs1, lhs2)
  fun
  aux {m1,m2:nat} .<max(m1,m2)>. (rhs1: list (Symbol, m1), rhs2: list (Symbol, m2)):<> int =
    case+ (rhs1, rhs2) of
    | (list_nil (), _) => ~1
    | (_, list_nil ()) => 1
    | (list_cons (x1, rhs1), list_cons (x2, rhs2)) => let
        val res = compare (x1, x2)
      in
        if res = 0 then aux (rhs1, rhs2)
        else res
      end // end of [aux]
in
  if res = 0 then aux (rhs1, rhs2)
  else res
end // end of [compare_Production_Production]
implement
compare_key_key<Production> (p1, p2) = compare_Production_Production (p1, p2)

implement
Production_derives (prod) = let
  val Prod (ntm, rhs) = prod
in
  ntm
end
//
(* ****** ****** *)
//
//local
//
datatype GRAMMAR = Grammar of (
  set (Symbol) // symbols
, map (Production, size_t(*tag*))
  // API for productions?
  // - alloc: {r:rgn} (size_t(*size*)) -> Productions(r)
  // - new : {n:pos} (Productions(r), Nonterminal(r), list(Symbol(r), n)) -> Prod(r)
  // - lhs : (Productions(r), Prod(r)) -> Nonterminal(r)
  // - rhs : (Productions(r), Prod(r)) -> [n:pos] list(Symbol(r), n)
  // - foreach$fwork : {env:vt0p} {n:pos} (Prod(r), Nonterminal(r), list(Symbol (r), n), &(env) >> _) -> void
  // - foreach_env : {env:vt0p} (Productions(r), &(env) >> _) -> void
  //
  // API for grammar?
  // - alloc: () -> [r:rgn] Grammar(r)
  // - productions : Grammar(r) -> Productions(r)
  // - alphabet : Grammar(r) -> Symbols(r)
  // - start_set : (Grammar(r), Prod(r)) -> void
  // - start_get : Grammar(r) -> Prod(r)
  // - easier thing to do? below (if grammar becomes linear, it is easier for us to modify it)
  //   - otherwise, we'd have to invent some tricks for multiple takeouts and such, probably
  // - modify$fwork : {env:vt0p} {r:rgn} (&Symbols(r) >> _, &Productions(r) >> _, &Prod(r) >> _, &(env) >> _): void
  // - modify : {env:vt0p} {r:rgn} (Grammar(r), &(env) >> _): void
, size_t(*start prod*)
, int(*nprods*)
) (* end of [GRAMMAR] *)
assume Grammar = GRAMMAR
//
//in // in of [local]
//
implement
Grammar_get_syms (g) = let
  val Grammar (syms, prods, st, _) = g
in
  syms
end
implement
Grammar_get_prods (g) = let
  val Grammar (syms, prods, st, _) = g
in
  prods
end
implement
Grammar_set_start (g, x) = {
  val Grammar (syms, prods, st, nprods) = g
  val-true = x >= 0
  val-true = x < nprods
  val () = g := Grammar (syms, prods, x, nprods)
}
implement
Grammar_get_start (g) = let
  val Grammar (syms, prods, st, _) = g
in
  st
end
implement
Grammar_make_nil () = let
  val syms = funset_make_nil {Symbol} ()
  val prods = funmap_make_nil {Production,size_t} ()
  val res = Grammar (syms, prods, (i2sz)0, 0)
in
  res
end
implement
Grammar_add_terminal (gr, lab) = let
  val sym = Symbol_terminal(lab)
  val+Grammar (syms, prods, st, nprods) = gr
  var syms = syms
  val _ = funset_insert<Symbol> (syms, sym)
  val () = gr := Grammar (syms, prods, st, nprods)
in
  sym
end
implement
Grammar_add_nonterminal (gr, lab) = let
  val sym = Symbol_nonterminal(lab)
  val+Grammar (syms, prods, st, nprods) = gr
  var syms = syms
  val _ = funset_insert<Symbol> (syms, sym)
  val () = gr := Grammar (syms, prods, st, nprods)
in
  sym
end
implement
Grammar_add_empty_production (gr, lhs) = let
  val res = Grammar_add_production (gr, lhs, $list{Symbol} (sym_EPS))
in
  res
end // end of [Grammar_add_empty_production]
implement
Grammar_add_production (gr, lhs, rhs) = let
  val prod = Prod (lhs, rhs)
  val+Grammar (syms, prods, st, nprods) = gr
  val tag = nprods
  val nprods = nprods + 1
  var res: size_t
  var prods = prods
  val tag = g0int2uint_int_size (tag)
  val-false = funmap_insert<Production,size_t> (prods, prod, tag, res)
  prval () = opt_clear (res)
  val () = gr := Grammar (syms, prods, st, nprods)
in
  tag
end
//
implement
fprint_Grammar (out, gr) = {
val Grammar (alphabet, prods, start, _) = gr
val () = fprintln!(out, "alphabet:")
val () = fprint_funset<Symbol> (stdout_ref, alphabet)
val () = fprint_newline (out)
val () = fprintln!(out, "productions:")
val () = fprint_funmap<Production, size_t> (stdout_ref, prods)
val () = fprint_newline (out)
val () = fprintln!(out, "start production:", start)
}
implement
fprint_val<Grammar> (out, gr) = fprint_Grammar (out, gr)
//
//end // end of [local]
//
(* ****** ****** *)
//
implement
Grammar_nonterminals (gr, nonterms, nontermmap) = let
  val alphabet = Grammar_get_syms (gr)
  val prods = Grammar_get_prods (gr)
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
  val nodelst = list_vt_reverse (nodelst)
  val () = array_copy_from_list_vt (!p_arr, nodelst)

  val () = fprintln!(stdout_ref, "nodes array: ")
  val () = fprint_array (stdout_ref, !p_arr, nodecount)
  val () = fprint_newline (stdout_ref)

  val () = fprintln!(stdout_ref, "nontermmap: ", nontermmap)

  val () = nonterms := arrayptr_encode (pf_arr, pf_free | p_arr)
in
  nodecount
end
//
