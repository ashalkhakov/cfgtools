staload "./Grammar.sats"

#include "share/atspre_staload.hats"

(* ****** ****** *)
//
staload _ = "prelude/DATS/integer.dats"
staload _ = "prelude/DATS/string.dats"
staload _ = "prelude/DATS/strptr.dats"
staload _ = "prelude/DATS/reference.dats"
staload _ = "prelude/DATS/list.dats"
staload _ = "prelude/DATS/pointer.dats"
staload _ = "prelude/DATS/gorder.dats"
//
//
datatype SymbolType (bool) =
  | STterm (true) of string
  | STntm (false) of string
//
staload "libats/SATS/funset_avltree.sats"
//
staload
_(*anon*) = "libats/DATS/funset_avltree.dats"
//
staload
_(*anon*) = "prelude/DATS/unsafe.dats"
//
assume Symbol (b:bool) = SymbolType (b)
//
typedef itm = Symbol
//
val the_alphabet = ref (funset_make_nil{itm} ())
//
extern
fun
Nonterminal_make_fresh (): Nonterminal
implement
Nonterminal_make_fresh () = Symbol_make_ntm ("S'")
//
implement sym_EOF = STterm "$"
//
implement sym_EPS = STterm "^" // pick another character?
//
implement
compare_Symbol_Symbol (x, y) =
case+ (x, y) of
| (STntm (a), STntm (b)) => compare (a, b)
| (STterm (a), STterm (b)) => compare (a, b)
| (STterm (a), STntm (b)) => ~1
| (STntm (a), STterm (b)) => 1
//
implement
compare_elt_elt<Symbol> (x, y) = compare_Symbol_Symbol (x, y)
//
fun
Symbol_add (sym: Symbol): void = let
  val (vbox pf_at | p_at) = ref_get_viewptr {set(itm)} (the_alphabet)
  val _ = funset_insert<itm> (!p_at, sym)
in
  (*empty*)
end
//
implement
symbol_is_term (x) =
case+ x of
| STterm _ => true | STntm _ => false
//
implement
symbol_is_nt (x) =
case+ x of
| STntm _ => true | STterm _ => false
//
implement
Symbol_make_ntm (x) = let
  // rename all non-terminals such that we don't have
  // any name clashes...
  val sz = funset_size<Symbol> (the_alphabet[])
  val sz = g0uint2int_size_int (sz)
  val sz_str = g0int2string_int (sz)
  val sz_str = strptr2string (sz_str)
  val app = string0_append3 (x, "'", sz_str)
  val x1 = strptr2string (app)
  val x = STntm(x1)
  val () = Symbol_add (x)
in
  x
end
//
implement
Symbol_make_term (x) = let
  val x = STterm(x)
  val () = Symbol_add (x)
in
  x
end
//
implement
eq_Symbol_Symbol (x, y) =
case+ (x, y) of
| (STntm (a), STntm (b)) => a = b
| (STterm (a), STterm (b)) => a = b
| (STterm (a), STntm (b)) => false
| (STntm (a), STterm (b)) => false
//
implement
fprint_val<Terminal> (out, sym) = let
  val STterm(a) = sym
in
  fprint!(out, "term(\"", a, "\")")
end
//
implement
fprint_val<Nonterminal> (out, sym) = let
  val STntm(a) = sym
in
  fprint!(out, "term(\"", a, "\")")
end
//
implement
fprint_val<Symbol> (out, sym) =
case+ sym of
| STntm (a) => fprint!(out, "ntm(\"", a, "\")")
| STterm (a) => fprint!(out, "term(\"", a, "\")")
//
implement
Symbol_fprint (out, sym) = fprint_val<Symbol>(out, sym)
implement
Symbol_print (sym) = Symbol_fprint (stdout_ref, sym)
//
extern
fun
the_alphabet_get (): set(itm)
implement
the_alphabet_get () = the_alphabet[]
//
implement{env}
Symbol_foreach$fwork (s, env) = ()
//
implement{env}
Symbol_foreach_env (env) = let
  val set = the_alphabet_get ()
  implement
  funset_foreach$fwork<itm><env> (x, env) =
    Symbol_foreach$fwork<env> (x, env)
  // end of [funmap_foreach$fwork]
in
  funset_foreach_env<itm><env> (set, env)
end // end of [Symbol_foreach_env]
//
(* ****** ****** *)
//
//
staload "libats/SATS/funmap_rbtree.sats"
//
staload
_(*anon*) = "libats/DATS/qlist.dats"
staload
_(*anon*) = "libats/DATS/funmap_rbtree.dats"
staload
_(*anon*) = "prelude/DATS/unsafe.dats"
//
assume ProductionNr = int
//
datatype Production = Production of (Nonterminal, List(Symbol))
//
typedef key = ProductionNr
typedef itm = Production
typedef map = map (key, itm)
//
val the_prods = ref (funmap_make_nil{key,itm} ())
val the_next_key = ref (0)
//
//
implement
compare_ProductionNr_ProductionNr (x, y) = compare (x, y)
implement
compare_key_key<ProductionNr> (x, y) = compare (x, y)
implement
compare_elt_elt<ProductionNr> (x, y) = compare (x, y)
//
extern
fun
lookup (int): Production
//
implement
lookup (p) = let
  val map = ref_get_elt<map> (the_prods)
  var prod : itm // uninitialized
(*
  val () = print!("lookup(")
  val () = print_int (p)
  val () = print!(")")
  val () = print_newline ()
*)
  val-true = $effmask_ref (funmap_search<key,itm> (map, p, prod))
  prval () = opt_unsome {itm} (prod)
in
  prod
end
//
implement
Production_make (hd, rhs) = let
  val prod = Production (hd, rhs)
  val id = ref_get_elt<int> (the_next_key)
  val () = ref_set_elt<int> (the_next_key, id+1)
  var res: itm?
  val (vbox pf_at | p_at) = ref_get_viewptr {map} (the_prods)
  val-false = $effmask_ref (funmap_insert<key,itm> (!p_at, id, prod, res))
  prval () = opt_clear (res)
in
  id
end // end of [Production_make]
//
implement
Production_make_eps (hd) = let
  val prod = Production (hd, list_cons{Symbol}(sym_EPS, list_nil{Symbol}()))
  val id = ref_get_elt<int> (the_next_key)
  val () = ref_set_elt<int> (the_next_key, id+1)
  var res: itm?
  val (vbox pf_at | p_at) = ref_get_viewptr {map} (the_prods)
  val-false = $effmask_ref (funmap_insert<key,itm> (!p_at, id, prod, res))
  prval () = opt_clear (res)
in
  id
end // end of [Production_make_eps]
//
implement
Production_is_eps (p) = let
  val Production (hd, rhs) = lookup (p)
  val hd = list_head_exn (rhs)
in
  if hd = sym_EPS then true
  else false
end // end of [Production_is_eps]
//
val the_augmented_sym = ref (None ()) : ref (Option(Nonterminal))
//
implement
Production_augment (head) = let
  val-None() = the_augmented_sym[]
  val newsym = Nonterminal_make_fresh ()
  val rhs = list_cons {Symbol} (head, list_cons {Symbol} (sym_EOF, list_nil {Symbol} ()))
  val newprod = Production_make (newsym, rhs)
  val () = the_augmented_sym[] := Some (newsym)
in
  newprod
end
//
implement
Production_yields (p) = let
  val+ Production (hd, rhs) = lookup (p)
in
  hd
end // end of [Production_yields]
//
implement
Production_item_count (p) = let
  val+ Production (hd, rhs) = lookup (p)
in
  list_length (rhs)
end // end of [Production_item_count]
//
implement
Production_item (p, itemNr) = let
  val+ Production (hd, rhs) = lookup (p)
  val len = list_length (rhs)
  val i = (g1ofg0)itemNr
  val () = assert_errmsg (i >= 0, "Production_item: invalid item nr")
  val () = assert_errmsg (i < len, "Production_item: invalid item nr")
  val res = list_get_at<Symbol> (rhs, i)
in
  res
end
//
extern
fun
get_prods_map (): map
implement
get_prods_map () = ref_get_elt<map> (the_prods)
//
implement{env}
Production_head_foreach$fwork (p, env) = ()
//
implement{env}
Production_head_foreach_env (nt, env) = let
  val map = get_prods_map ()
  implement
  funmap_foreach$fwork<key,itm><env> (k, x, env) = let
    val Production (hd, itms) = x
  in
    if hd = nt then
      Production_head_foreach$fwork<env> (k, env)
  end // end of [funmap_foreach$fwork]
//  val () = println!("Production_head_foreach: called with ", nt)
in
  funmap_foreach_env<key,itm><env> (map, env)
end
//
implement
fprint_val<ProductionNr> (out, p) = {
  val Production (hd, rhs) = lookup (p)
  val () = fprint_val<Symbol> (out, hd)
  val () = fprint_string (out, " ::= ")
  val () = fprint_list<Symbol> (out, rhs)
}
//
implement
Production_fprint (out, p) = fprint_val<ProductionNr>(out, p)
implement
Production_print (p) = Production_fprint (stdout_ref, p)

implement
grammar_print () = let
  //
  var env = (g0ofg1)1
  vtypedef env = int
  //
  val () = println!("alphabet:")
  val set = the_alphabet_get ()
  implement
  funset_foreach$fwork<Symbol><env> (x, env) = {
    val () = Symbol_print (x)
    val () = print_newline ()
  }
  // end of [funmap_foreach$fwork]
  val () = funset_foreach_env<Symbol><env> (set, env)
  //
  val () = println!("productions:")
  val map = get_prods_map ()
  implement
  funmap_foreach$fwork<key,itm><env> (k, _, env) = {
    val () = Production_print(k)
    val () = print_newline ()
  }
  val () = funmap_foreach_env<key,itm><env> (map, env)
  //
in
end
//
assume termset = set (Terminal)
//
implement
compare_elt_elt<Terminal> (x, y) = compare_Symbol_Symbol (x, y)
//
implement
fprint_val<termset> (out, ts) = let
  val () = fprint_funset<Terminal> (out, ts)
in
end // end of [fprint_val]
//
implement
termset_fprint (out, ts) = fprint_val<termset>(out, ts)
implement
termset_print (ts) = termset_fprint (stdout_ref, ts)
//
implement{env}
termset_foreach$fwork (t, env) = ()
//
implement{env}
termset_foreach_env (ts, env) = let
  implement
  funset_foreach$fwork<Terminal><env> (t, env) =
    termset_foreach$fwork<env> (t, env)
  // end of [funset_foreach$fwork]
  val () = funset_foreach_env<Terminal><env> (ts, env)
in
  (*empty*)
end // end of [termset_foreach_env]
//
// NOTE: from http://www.cs.virginia.edu/~cs415/reading/FirstFollowLL.pdf

(*
the previous attempt doesn't work, never stops.
http://marvin.cs.uidaho.edu/Teaching/CS445/firstfollow.txt
http://lara.epfl.ch/w/cc09:algorithm_for_first_and_follow_sets
http://ezekiel.vancouver.wsu.edu/~cs452/lectures/first-follow/firstfollow.pdf
- this is even better! shows the nullable, first, follow set construction
  but in mathematical terms
- construct the nullable, first, follow sets
- then SLR(1) will be easy to do
- ... and LR(1) will be a bit harder but nevertheless okay
and: http://compilers.iecc.com/comparch/article/01-04-079
and here: http://www.cis.upenn.edu/~jean/gbooks/graphm.pdf
- okay, I've implemented the digraph abstract type,
  now I can probably follow what's given in graphm.pdf

var nullable: set(Nonterminal)
var first: map(Symbol,termset)
var follow: map(Nonterminal,Termset)

nullable = {}
foreach nonterminal X:
  first(X)={}
  follow(X)={}
for each terminal Y:
  first(Y)={Y}
  follow(Y)={}

repeat
 foreach grammar rule X ::= Y(1) ... Y(k)
  if k=0 or {Y(1),...,Y(k)} subset of nullable then
    nullable = nullable union {X}
    NOTE: in my case, for eps-rules, k=1 and Y(1) = eps
  for i = 1 to k
    if i=1 or {Y(1),...,Y(i-1)} subset of nullable then
      first(X) = first(X) union first(Y(i))
    for j = i+1 to k
      if i=k or {Y(i+1),...Y(k)} subset of nullable then
        follow(Y(i)) = follow(Y(i)) union follow(X)
      if i+1=j or {Y(i+1),...,Y(j-1)} subset of nullable then
        follow(Y(i)) = follow(Y(i)) union first(Y(j))
until none of nullable,first,follow changed in last iteration
*)
//
implement
first (syms) = let
  vtypedef env = termset
  fun
  aux0 (sym: Symbol, env: &(env) >> _): void = (
    if symbol_is_term (sym) then let // NOTE: terminal or EPS!
      val _ = funset_insert<Terminal> (env, sym)
    in
      (*empty*)
    end else let
      implement
      Production_head_foreach$fwork<env> (p, env) = let
        val Production (lhs, rhs) = lookup (p)
        val rhs_len = list_length (rhs)
        val cnt = aux1 (rhs, env, 0)
      in
        if cnt = rhs_len then {
          // all nullable!
          val _ = funset_insert<Terminal> (env, sym_EPS)
        }
      end // end of [Production_head_foreach$fwork]
    in
      Production_head_foreach_env<env> (sym, env)
    end
  ) (* end of [aux0] *)
  and
  aux1 (syms: List(Symbol), env: &(env) >> _, acc: int): int =
    case+ syms of
    | list_nil () => ((*println!("aux1: done");*) acc)
    | list_cons (sym, syms) => let
        var env0 = funset_nil {Terminal} ()
(*
        val () = println!("aux1 at ", sym)
*)
        val () = aux0 (sym, env0)
(*
        val () = println!("aux0 gives: ", env0)
*)
        val containedEPS = funset_remove<Terminal> (env0, sym_EPS)
        val () = env := funset_union (env, env0)
(*
        val () = println!("new env: ", env)
*)
      in
        if containedEPS then aux1 (syms, env, acc+1)
        else acc
      end
  // end of [aux1]
  var env = funset_nil{Terminal} ()
  val len = list_length (syms)
  val cnt = aux1 (syms, env, 0)
  val () =
    if :(env: termset) => cnt = len then {
      // all nullable!
(*
      val () = println!("all nullable!")
*)
      val _ = funset_insert<Terminal> (env, sym_EPS)
    } (* end of [if] *)
  // end of [val]
in
  env
end // end of [first]
//
local
//
vtypedef env = termset
//
fun
aux0 (
  A: Nonterminal, k: Nonterminal, xs: List(Symbol), env: &(env) >> _
): void =
  case+ xs of
  | list_nil () => ()(*println!("aux finished")*)
  | list_cons (X, xs) =>
    if X = A then let
    (*
      val () = println!("found occurrence of ", A, " in rhs of ", k)
    *)
    in
      if list_is_cons (xs) then let
        var fb0 = first(xs)
(*
        val () = println!("first:", fb0)
*)
        val containedEPS = funset_remove<Terminal> (fb0, sym_EPS)
(*
        val () = println!("contained EPS: ", containedEPS)
*)
        val () = env := funset_union<Terminal> (env, fb0)
(*
        val () = println!("resulting set: ", env)
*)
      in
        if containedEPS
        then let
          // FIXME: runaway recursion,
          // say k = A... or k leads indirectly to A
          // - is production P visited? if yes, just don't visit it twice
          val () = aux1 (k, env)
        in
          aux0 (A, k, xs, env) // look for other occurrences
        end else let
          // nothing
        in
        (*
          println!("aux finished")
        *)
          (*empty*)
        end
      end else let
        val () = aux1 (k, env)
      in
      end
    end else aux0 (A, k, xs, env)
// end of [aux0]

and aux1 (A: Nonterminal, env: &(env) >> _): void = let
  // if A is the start nonterminal, put EOF into follow(A)
  val augmented_sym_opt = the_augmented_sym[]
  val augmented_sym = option_unsome_exn<Symbol> (the_augmented_sym[])
  val () =
    if :(env: termset) => eq_Symbol_Symbol (augmented_sym, A) then let

    val () = println!("follow(", A, "): start nonterminal")

    val _ = funset_insert<Terminal> (env, sym_EOF)
    in
      (*empty*)
    end // end of [val]
//
//  val () = println!("follow(", A, ") = ?, see below")
//
  // go over all productions
  val map = get_prods_map ()
  //
  implement
  funmap_foreach$fwork<key,itm><termset> (p, bod, env) = let
    val Production (lhs, rhs) = bod
(*
    val () = print!("production ")
    val () = print_int (p)
    val () = println!(": ", lhs, " ::= ...")
*)
  in
    if lhs = A then () // right? skip the rules for the nonterminal itself
    else
      aux0 (A, lhs, rhs, env);
//  println!("aux finished 1")
  end // end of [funmap_foreach$fwork]
  // looks like this one doesn't work?
  val () = funmap_foreach_env<key,itm><termset> (map, env)
in
  (*empty*)
end

in // in of [local]

implement
follow (A) = let
  var env = funset_nil{Terminal} ()
  val () = aux1 (A, env)

  val () = println!("follow(", A, ") = ", env)

in
  env
end // end of [follow]

end // end of [local]
