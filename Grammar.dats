staload "./Grammar.sats"

#include "share/atspre_staload.hats"

(* ****** ****** *)
//
staload _ = "prelude/DATS/integer.dats"
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
assume Symbol (b:bool) = SymbolType (b)
//
implement
Symbol_make_ntm (x) = STntm(x)
//
implement
Symbol_make_term (x) = let
  val x = STterm(x)
in
  x
end
//

//
implement
gcompare_val_val<Symbol> (x, y) =
case+ (x, y) of
| (STntm (a), STntm (b)) => compare (a, b)
| (STterm (a), STterm (b)) => compare (a, b)
| (STterm (a), STntm (b)) => ~1
| (STntm (a), STterm (b)) => 1
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
compare_key_key<ProductionNr> (x, y) = compare (x, y)
//
fun lookup (p: int): Production = let
  val map = the_prods[]
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
  // this halts!
  val-false = $effmask_ref (funmap_insert<key,itm> (!p_at, id, prod, res))
  prval () = opt_clear (res)
in
  id
end // end of [Production_make]
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
//
