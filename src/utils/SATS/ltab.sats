(* ****** ****** *)
//
fun{key:t@ype}
equal_key_key (key, key):<> bool
//
fun{key:t@ype}
hash_key (x: key):<> ulint
//
typedef HASHTBLNODE = @{
  buckets= ptr
, ntot= size_t
, n= int
, nextfree= int
} (* end of [HASHTBLNODE] *)
//
absvt@ype hashtbl_vt0ype (key:t@ype, itm:t@ype, int) = HASHTBLNODE
//
vtypedef hashtbl (k:t@ype, i:t@ype, n:int) = hashtbl_vt0ype (k, i, n)
//
praxi
lemma_hashtbl_param
  {key:t@ype;itm:t@ype}{n:int}
  (!hashtbl (key, itm, n)): [n >= 0] void
//
fun{key,itm:t@ype}
hashtbl_make_nil {ntot:nat} (&HASHTBLNODE? >> hashtbl (key, itm, ntot), size_t ntot): void
//
fun{key,itm:t@ype}
hashtbl_free {ntot:int} (&hashtbl (key, itm, ntot) >> HASHTBLNODE?): void
//
fun{key,itm:t@ype}
hashtbl_insert {ntot:nat} (
  ht: &hashtbl (key, itm, ntot) >> hashtbl (key, itm, ntot)
, k0: key
, itm: itm
, res: &itm? >> opt (itm, b)
) : #[b:bool] bool b
//
fun{key,itm:t@ype}
hashtbl_search {ntot:nat} (
  ht: &hashtbl (key, itm, ntot)
, k0: key
, res: &itm? >> opt (itm, b)
) : #[b:bool] bool b(*found*)
//
fun{key,itm:t@ype}
hashtbl_search_ref {ntot:nat} (
  ht: &hashtbl (key, itm, ntot)
, k0: key
) : intBtw(~1, ntot)
//
fun{key,itm:t@ype}
hashtbl_get_ref {ntot:nat} (ht: &hashtbl (key, itm, ntot), k0: natLt(ntot)): itm
//
(* ****** ****** *)
