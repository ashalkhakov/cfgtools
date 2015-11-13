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
(*
fun{env:vt0p}
Symbol_foreach$fwork (Symbol, env: &(env) >> _): void
*)
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
(*
fun{env:vt0p}
Production_head_foreach$fwork (ProductionNr, env: &(env) >> _): void
*)
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
        val cnt = aux1 (rhs, env, 0)
        val rhs_len = list_length (rhs)
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
    | list_nil () => acc
    | list_cons (sym, syms) => let
        var env0 = funset_nil {Terminal} ()
        val fs = aux0 (sym, env0)
        val containedEPS = funset_remove<Terminal> (env0, sym_EPS)
        val () = env := funset_union (env, env0)
      in
        if containedEPS then aux1 (syms, env, acc+1)
        else acc
      end
  // end of [aux1]
  var env = funset_nil{Terminal} ()
  val cnt = aux1 (syms, env, 0)
  val len = list_length (syms)
  val () =
    if :(env: termset) => cnt = len then {
      // all nullable!
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
extern
fun
aux (
  A: Nonterminal, k: Nonterminal, xs: List(Symbol), env: &(env) >> _
): void
//
implement
aux (A, k, xs, env) =
  case+ xs of
  | list_nil () => ()
  | list_cons (X, xs) =>
    if X = A then let
    in
      if list_is_cons (xs) then let
        var fb0 = first(xs)
        val containedEPS = funset_remove<Terminal> (fb0, sym_EPS)
        val () = env := funset_union<Terminal> (env, fb0)
      in
        if containedEPS
        then let
          val fk = follow(k)
          val () = env := funset_union<Terminal> (env, fk)
        in
          aux (A, k, xs, env) // look for other occurrences
        end
      end else let
        val () = env := funset_union<Terminal> (env, follow (k))
      in
      end
    end else aux (A, k, xs, env)
// end of [aux]

in // in of [local]

implement
follow (A) = let
//
  var env = funset_nil{Terminal} ()
//
  // if A is the start nonterminal, put EOF into follow(A)
  val () = let
    val augmented_sym_opt = the_augmented_sym[]
    val augmented_sym = option_unsome_exn<Symbol> (the_augmented_sym[])
  in
    if :(env: termset) => eq_Symbol_Symbol (augmented_sym, A) then {
      val _ = funset_insert<Terminal> (env, sym_EOF)
    }
  end // end of [val]
//
  // go over all productions
  val map = get_prods_map ()
  implement
  funmap_foreach$fwork<key,itm><termset> (p, bod, env) = let
    val Production (lhs, rhs) = bod
  in
    aux (A, lhs, rhs, env)
  end // end of [funmap_foreach$fwork]
  val () = funmap_foreach_env<key,itm><termset> (map, env)
in
  env
end // end of [follow]

end // end of [local]

// TODO: LALR(1)
// - http://web.cs.dal.ca/~sjackson/lalr1.html
//   "Syntax Analysis Goal: Action and Goto Table"
// - test first/follow sets
//
// build LR(0) item sets and transitions
// build the translation table
// - To construct the Translation Table all we need to do is determine what item set to go to next based on a given input.
// - Item Set nr, Symbol -> Item Set nr (isn't this just the transitions between states??)
// build extended grammar
// - extended with a lookahead symbol
// - For example, if we wanted to start in I0 and follow the rule V → * E
//   We would start by giving I0 a *.
//   According to the picture above, this would lead to I2.
//   We express this as 0*2 (itemset 0, when given a *, leads to itemset 2)
//
// 1. determine the first set of every nonterminal in the grammar
// 2. determine the follow set of every nonterminal in the grammar
