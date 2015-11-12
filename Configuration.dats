#include
"share/atspre_staload.hats"

staload "./Grammar.sats"
staload "./Configuration.sats"

staload _ = "./Grammar.dats"

//
staload "libats/SATS/funmap_rbtree.sats"
staload "libats/SATS/funset_avltree.sats"
//
staload
_(*anon*) = "libats/DATS/qlist.dats"
staload
_(*anon*) = "libats/DATS/funmap_rbtree.dats"
staload
_(*anon*) = "libats/DATS/funset_avltree.dats"
staload
_(*anon*) = "prelude/DATS/unsafe.dats"
//
assume ConfigurationNr = int
//
datatype Configuration = Configuration of (ProductionNr, int(*dot*))
//
typedef key = ConfigurationNr
typedef itm = Configuration
typedef map0 = map (itm, key)
typedef map = map (key, itm)
//
val the_config_set = ref (funmap_make_nil{itm,key} ())
val the_configs = ref (funmap_make_nil{key,itm} ())
val the_next_key = ref (0)
//
//
implement
compare_key_key<ProductionNr> (x, y) = compare_ProductionNr_ProductionNr (x, y)
implement
compare_ConfigurationNr_ConfigurationNr (x, y) = compare (x, y)
implement
compare_key_key<ConfigurationNr> (x, y) = compare (x, y)
implement
compare_key_key<itm> (x, y) = let
  val Configuration (prod0, dot0) = x
  val Configuration (prod1, dot1) = y
  val res = compare_key_key<ProductionNr> (prod0, prod1)
in
  if res = 0 then compare (dot0, dot1)
  else res
end // end of [compare_elt_elt]
//
extern
fun
the_config_insert (key, itm): void
implement
the_config_insert (id, item) = let
  var bod: itm?
  val (vbox pf_at | p_at) = ref_get_viewptr {map} (the_configs)
  val-false = $effmask_ref (funmap_insert<key,itm> (!p_at, id, item, bod))
  prval () = opt_clear (bod)
in
end // end of [the_config_insert]
//
extern
fun
the_config_set_insert (key, itm): void
implement
the_config_set_insert (id, item) = let
  var bod: key?
  val (vbox pf_at | p_at) = ref_get_viewptr {map0} (the_config_set)
  val-false = $effmask_ref (funmap_insert<itm,key> (!p_at, item, id, bod))
  prval () = opt_clear (bod)
in
end // end of [the_config_set_insert]
//
fun
Configuration_make_internal (item: Configuration): ConfigurationNr = let
var k0: key
in
  if :(k0: key?) => funmap_search (the_config_set[], item, k0) then let
    val id = opt_unsome_get<key> (k0)
  in
    id
  end else let
    prval () = opt_unnone {key} (k0)
    val id = ref_get_elt<int> (the_next_key)
    val () = ref_set_elt<int> (the_next_key, id+1)
    val () = the_config_insert (id, item)
    val () = the_config_set_insert (id, item)
  in
    id
  end
end

implement
Configuration_make (prod) = let
  val item = Configuration (prod, 0)
  (*
  val () = println!("new config for production: ", prod)
  *)
  val res = Configuration_make_internal (item)
  (*
  val () = print!("resulted in: ")
  val () = print_int (res)
  val () = print_newline ()
  *)
in
  res
end
//
extern
fun lookup (c: int): Configuration
//
implement
lookup (c) = let
  val map = the_configs[]
  var conf : itm // uninitialized
  val-true = $effmask_ref (funmap_search<key,itm> (map, c, conf))
  prval () = opt_unsome {itm} (conf)
in
  conf
end


implement
Configuration_production (c) = let
  val Configuration (prod, dot) = lookup (c)
in
  prod
end
implement
Configuration_dot (c) = let
  val Configuration (prod, dot) = lookup (c)
in
  dot
end
implement
Configuration_is_final (c) = let
  val Configuration (prod, dot) = lookup (c)
  val itemCount = Production_item_count (prod)
in
  dot = itemCount
end

implement
Configuration_is_accepting (c) = let
  val Configuration (prod, dot) = lookup (c)
  val itemCount = Production_item_count (prod)
in
  if dot < itemCount then let
    val itm = Production_item (prod, dot)
  in
    itm = sym_EOF
  end else false
end

implement
Configuration_advance (c) = let
  val-false = Configuration_is_final (c)
  val dot = Configuration_dot (c)
  val prod = Configuration_production (c)
  val dot1 = dot+1
  val con = Configuration (prod, dot1)
in
  Configuration_make_internal (con)
end
//
implement
fprint_val<ConfigurationNr> (out, c) = let
  val Configuration (prod, dot) = lookup (c)
  val hd = Production_yields (prod)
  val () = fprint!(out, hd, " ::= ")
  fun
  aux (prod: ProductionNr, dot: int, itm: int) =begin
    if itm = dot then fprint!(out, ".");
    if itm < Production_item_count (prod) then begin
      fprint!(out, Production_item (prod, itm));
      fprint!(out, " ");
      aux (prod, dot, itm+1)
    end
  end // end of [aux]
  val () = aux (prod, dot, 0)
in
end
//
implement
Configuration_fprint (out, c) = fprint_val<ConfigurationNr> (out, c)
//
implement
Configuration_print (c) = Configuration_fprint (stdout_ref, c)
