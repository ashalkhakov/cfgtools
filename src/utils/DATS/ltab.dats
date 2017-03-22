#include "share/atspre_staload.hats"

(* ****** ****** *)
//
staload "./../SATS/ltab.sats"
//
#define ATS_DYNLOADFLAG 0
//
staload "libats/SATS/hashfun.sats"
staload _ = "libats/DATS/hashfun.dats"
//
staload _ = "prelude/DATS/integer.dats"
staload _ = "prelude/DATS/array.dats"
staload _ = "prelude/DATS/gnumber.dats"
//
implement{a}
equal_key_key (x, y) = gequal_val_val<a> (x, y)
//
implement
hash_key<string> (str) =
  string_hash_multiplier (31UL, 618033989UL, str)
//
local
//
typedef entry0 (key:t@ype, itm:t@ype) = @{
  key= key
, itm= itm
, inuse= bool
, hashnext= int
}
//
vtypedef entry (key:t@ype, itm: t@ype, b:bool, ntot: int) = @{
  key= opt (key, b)
, itm= opt (itm, b)
, inuse= bool b
, hashnext= intBtw(~1, ntot)
}
vtypedef entry (key:t@ype, itm:t@ype, ntot:int) = [b:bool] entry (key, itm, b, ntot)
vtypedef entry0 (key:t@ype, itm:t@ype) = @{key= key, itm= itm, inuse=bool, hashnext=int}
//
vtypedef HASHTBLSTRUCT (key:t@ype, itm:t@ype, ntot:int) = @{
  buckets= arrayptr (entry(key, itm, ntot), ntot)
, ntot= size_t ntot
, n= int // total elements which are used
, nextfree= intBtw (~1, ntot) // 0 <= ncellar <= nf <= n
} (* end of [HASHTBLSTRUCT] *)
//
assume hashtbl_vt0ype (
  key:t@ype, itm:t@ype, ntot:int
) = HASHTBLSTRUCT (key, itm, ntot)
//
in // in of [local]
//
implement{key,itm}
hashtbl_make_nil {ntot} (ht, ntot) = {
//
  vtypedef T0 = entry0(key,itm)
  vtypedef T = entry(key,itm,ntot)
  val (pf_buckets, pf_buckets_free | p_buckets) = array_ptr_alloc<T0> (ntot)
//
  fun
  aux0 {l:addr} .< >. (pf : !T0? @ l >> T @ l | p: ptr l): void = {
    val () = !p.inuse := false
    prval () = opt_none (!p.key)
    prval () = opt_none (!p.itm)
    val () = !p.hashnext := ~1
  } (* end of [aux0] *)
//
  fun
  aux {lres:addr} {n:nat} (
    pf_hashtbl_make_nil: !(@[T0?][n] @ lres) >> @[T][n] @ lres
  | p_hashtbl_make_nil: ptr lres, nodecount: size_t n
  ): void = {
    var i: int = 0
    var p = p_hashtbl_make_nil
    prvar pf0 = array_v_nil {T} ()
    prvar pf1 = pf_hashtbl_make_nil
    //
    val () =
    while* {i:nat | i <= n} .<n-i>. (
      i: int (i)
    , p: ptr (lres + i*sizeof(T0))
    , pf0: array_v (T, lres, i)
    , pf1: array_v (T0?, lres+i*sizeof(T0), n-i)
    ) : (
      pf0: array_v (T, lres, n)
    , pf1: array_v (T0?, lres+i*sizeof(T0), 0)
    ) => (
      (i2sz)i < nodecount
    ) {
    //
      prval (pf_at, pf1_res) = array_v_uncons {T0?} (pf1)
      prval () = pf1 := pf1_res
      val () = aux0 (pf_at | p)
      val () = p := add_ptr1_bsz (p, sizeof<T>)
      prval () = pf0 := array_v_extend {T} (pf0, pf_at)
      val () = i := i + 1
    //
    } // end of [val]
    //
    prval () = pf_hashtbl_make_nil := pf0
    prval () = array_v_unnil {T0?} (pf1)
    //
  } (* end of [aux] *)
  val () = aux (pf_buckets | p_buckets, ntot)
//
  val () = ht.buckets := arrayptr_encode (pf_buckets, pf_buckets_free | p_buckets)
  val () = ht.ntot := ntot
  val () = ht.n := (g0ofg1)0
  val () = ht.nextfree := pred((sz2i)ntot)
//
} (* end of [hashtbl_make_nil] *)
//
implement{key,itm}
hashtbl_free {ntot} (ht) = {
//
  vtypedef T = entry (key,itm,ntot)
  vtypedef T0 = entry0 (key,itm)
//
  fn
  aux0 {l:addr} .< >. (pf : !T @ l >> T0? @ l | p: ptr l): void = let
  in
    if :(pf: T0? @ l) => !p.inuse then let
      prval () = opt_unsome {key} (!p.key)
      prval () = topize {key} (!p.key)
      prval () = opt_unsome {itm} (!p.itm)
      prval () = topize {itm} (!p.itm)
      val () = !p.inuse := false
    in
      (*empty*)
    end else let
      prval () = opt_unnone {key} (!p.key)
      prval () = opt_unnone {itm} (!p.itm)
    in
      (*empty*)
    end
  end // end of [aux0]
//
  fun
  aux {lres:addr} {n:nat} (
    pf_hashtbl_make_nil: !(@[T][n] @ lres) >> @[T0?][n] @ lres
  | p_hashtbl_make_nil: ptr lres, nodecount: size_t n
  ): void = {
    var i: int = 0
    var p = p_hashtbl_make_nil
    prvar pf0 = array_v_nil {T0?} ()
    prvar pf1 = pf_hashtbl_make_nil
    //
    val () =
    while* {i:nat | i <= n} .<n-i>. (
      i: int (i)
    , p: ptr (lres + i*sizeof(T0))
    , pf0: array_v (T0?, lres, i)
    , pf1: array_v (T, lres+i*sizeof(T), n-i)
    ) : (
      pf0: array_v (T0?, lres, n)
    , pf1: array_v (T, lres+i*sizeof(T), 0)
    ) => (
      (i2sz)i < nodecount
    ) {
    //
      prval (pf_at, pf1_res) = array_v_uncons {T} (pf1)
      prval () = pf1 := pf1_res
      val () = aux0 (pf_at | p)
      val () = p := add_ptr1_bsz (p, sizeof<T>)
      prval () = pf0 := array_v_extend {T0?} (pf0, pf_at)
      val () = i := i + 1
    //
    } // end of [val]
    //
    prval () = pf_hashtbl_make_nil := pf0
    prval () = array_v_unnil {T} (pf1)
    //
  } (* end of [aux] *)
//
  extern
  castfn
  arrayptr_decode :
    {a:vt0p}{l:addr}{n:int}
    (arrayptr (a, l, n)) -<0> (array_v (INV(a), l, n), mfree_gc_v l | ptr l)
//
  val (pf_buckets, pf_buckets_free | p_buckets) = arrayptr_decode (ht.buckets)
  prval () = lemma_g1uint_param (ht.ntot)
  val () = aux (pf_buckets | p_buckets, ht.ntot)
  val () = array_ptr_free (pf_buckets, pf_buckets_free | p_buckets)
//
} (* end of [hashtbl_free] *)
//
extern
fun{key,itm:t@ype}
empty {n:nat} (&hashtbl(key, itm, n), natLt(n)): bool
//
implement{key,itm}
empty {n} (ht, idx) = let
  val idx = (i2sz)idx
  vtypedef T = entry(key,itm, n)
  val (pf_buckets | p_buckets) = arrayptr_takeout_viewptr (ht.buckets)
  val (pf_at, fpf | p_at) = array_ptr_takeout<T> (pf_buckets | p_buckets, idx)
  fun
  fwork {l:addr} (pf_at: !T @ l | p_at: ptr l): bool = let
    val res = !p_at.inuse in
    ~res
  end // end of [fwork]
  val res = fwork (pf_at | p_at)
  prval () = pf_buckets := fpf (pf_at)
  prval () = arrayptr_addback (pf_buckets | ht.buckets)
in
  res
end // end of [empty]
//
extern
fun{key,itm:t@ype}
hash {n:int} (ht: &hashtbl (key, itm, n), k0: key): natLt(n)
//
implement{key,itm}
hash {n} (ht, k0) = let
  val m = ht.ntot
  val-true = m > 0
  val h = hash_key<key> (k0)
  val h = g0uint2uint_ulint_size(h)
  val h = (g1ofg0)h
  val (pf | i) = g1uint_mod2 (h, m)
  val i = g1uint2int (i)
in
  i
end // end of [hash]
//
extern
fun{key,itm:t@ype}
get_hashnext {n:nat} (ht: &hashtbl (key, itm, n), idx: natLt(n)): intBtw(~1, n)
//
implement{key,itm}
get_hashnext {n} (ht, idx) = let
  val idx = (i2sz)idx
  vtypedef T = entry(key, itm, n)
  val (pf_buckets | p_buckets) = arrayptr_takeout_viewptr (ht.buckets)
  val (pf_at, fpf | p_at) = array_ptr_takeout<T> (pf_buckets | p_buckets, idx)
  fun
  fwork {l:addr} (pf_at: !T @ l | p_at: ptr l): intBtw(~1, n) = let
    val nxt = !p_at.hashnext in
    nxt
  end // end of [fwork]
  val nxt = fwork (pf_at | p_at)
  prval () = pf_buckets := fpf (pf_at)
  prval () = arrayptr_addback (pf_buckets | ht.buckets)
in
  nxt
end // end of [get_hashnext]
//
extern
fun{key,itm:t@ype}
set_hashnext {n:nat} (ht: &hashtbl (key, itm, n), idx: natLt(n), nxt: intBtw(~1, n)): void
//
implement{key,itm}
set_hashnext {n} (ht, idx, nxt) = {
  val idx = (i2sz)idx
  vtypedef T = entry(key, itm, n)
  val (pf_buckets | p_buckets) = arrayptr_takeout_viewptr (ht.buckets)
  val (pf_at, fpf | p_at) = array_ptr_takeout (pf_buckets | p_buckets, idx)
  //
  fun
  fwork {l:addr} (pf_at: !T @ l >> T @ l | p_at: ptr l, nxt: intBtw(~1, n)): void = {
    val () = !p_at.hashnext := nxt
  } (* end of [fwork] *)
  val () = fwork (pf_at | p_at, nxt)
  //
  prval () = pf_buckets := fpf (pf_at)
  prval () = arrayptr_addback (pf_buckets | ht.buckets)
} (* end of [get_hashnext] *)
//
extern
fun{key,itm:t@ype}
get_key {n:nat} (ht: &hashtbl (key, itm, n), idx: natLt(n)): key
//
implement{key,itm}
get_key {n} (ht, idx) = let
  val idx = (i2sz)idx
  vtypedef T = entry(key, itm, n)
  val (pf_buckets | p_buckets) = arrayptr_takeout_viewptr (ht.buckets)
  val (pf_at, fpf | p_at) = array_ptr_takeout (pf_buckets | p_buckets, idx)
  //
  fun
  fwork {l:addr} (pf_at: !T @ l >> T @ l | p_at: ptr l): key = let
    val-true = !p_at.inuse
    prval () = opt_unsome{key} (!p_at.key)
    val res = !p_at.key
    prval () = opt_some{key} (!p_at.key)
  in
    res
  end (* end of [fwork] *)
  val res = fwork (pf_at | p_at)
  //
  prval () = pf_buckets := fpf (pf_at)
  prval () = arrayptr_addback (pf_buckets | ht.buckets)
in
  res
end // end of [get_key]
//
extern
fun{key,itm:t@ype}
get_itm {n:nat} (ht: &hashtbl (key, itm, n), idx: natLt(n)): itm
//
implement{key,itm}
get_itm {n} (ht, idx) = let
  val idx = (i2sz)idx
  vtypedef T = entry(key, itm, n)
  val (pf_buckets | p_buckets) = arrayptr_takeout_viewptr (ht.buckets)
  val (pf_at, fpf | p_at) = array_ptr_takeout (pf_buckets | p_buckets, idx)
  //
  fun
  fwork {l:addr} (pf_at: !T @ l >> T @ l | p_at: ptr l): itm = let
    val-true = !p_at.inuse
    prval () = opt_unsome{itm} (!p_at.itm)
    val res = !p_at.itm
    prval () = opt_some{itm} (!p_at.itm)
  in
    res
  end (* end of [fwork] *)
  val res = fwork (pf_at | p_at)
  //
  prval () = pf_buckets := fpf (pf_at)
  prval () = arrayptr_addback (pf_buckets | ht.buckets)
in
  res
end // end of [get_itm]
//
extern
fun{key,itm:t@ype}
set_itm {n:nat} (ht: &hashtbl (key, itm, n), idx: natLt(n), itm: itm): void
//
implement{key,itm}
set_itm {n} (ht, idx, itm) = {
  val idx = (i2sz)idx
  vtypedef T = entry(key, itm, n)
  val (pf_buckets | p_buckets) = arrayptr_takeout_viewptr (ht.buckets)
  val (pf_at, fpf | p_at) = array_ptr_takeout (pf_buckets | p_buckets, idx)
  //
  fun
  fwork {l:addr} (pf_at: !T @ l >> T @ l | p_at: ptr l): void = {
    val-true = !p_at.inuse
    prval () = opt_clear{itm} (!p_at.itm)
    val () = !p_at.itm := itm
    prval () = opt_some{itm} (!p_at.itm)
  } (* end of [fwork] *)
  val () = fwork (pf_at | p_at)
  //
  prval () = pf_buckets := fpf (pf_at)
  prval () = arrayptr_addback (pf_buckets | ht.buckets)
} (* end of [set_itm] *)
//
extern
fun{key,itm:t@ype}
set_key_itm {n:nat} (ht: &hashtbl (key, itm, n), idx: natLt(n), key: key, itm: itm): void
//
implement{key,itm}
set_key_itm {n} (ht, idx, key, itm) = {
  val idx = (i2sz)idx
  vtypedef T = entry(key, itm, n)
  val (pf_buckets | p_buckets) = arrayptr_takeout_viewptr (ht.buckets)
  val (pf_at, fpf | p_at) = array_ptr_takeout (pf_buckets | p_buckets, idx)
  //
  fun
  fwork {l:addr} (pf_at: !T @ l >> T @ l | p_at: ptr l): void = {
    prval () = opt_clear{key} (!p_at.key)
    val () = !p_at.key := key
    prval () = opt_clear{itm} (!p_at.itm)
    val () = !p_at.itm := itm
    val () = !p_at.inuse := true
    prval () = opt_some{key} (!p_at.key)
    prval () = opt_some{itm} (!p_at.itm)
  } (* end of [fwork] *)
  val () = fwork (pf_at | p_at)
  //
  prval () = pf_buckets := fpf (pf_at)
  prval () = arrayptr_addback (pf_buckets | ht.buckets)
} (* end of [set_key_itm] *)
//
// from https://users.dcc.uchile.cl/~rbaeza/handbook/algs/3/3312.ins.c.html
implement{key,itm}
hashtbl_insert {ntot} (ht, k0, elt, res) = let
  val idx = hash<key,itm> (ht, k0)
(*
  val () = fprintln!(stdout_ref, "hash: ", idx)
*)
in
  // used slot?
  if empty<key,itm> (ht, idx) then let
    // not used, claim it
(*
    val () = fprintln!(stdout_ref, "empty slot!")
*)
    val () = set_key_itm<key,itm> (ht, idx, k0, elt)
    val () = set_hashnext<key,itm> (ht, idx, ~1)
    val () = ht.n := succ(ht.n)
    prval () = opt_none {itm} (res)
  in
    false
  end else let
    // already used, find end of chain
    fun
    aux (ht: &hashtbl (key, itm, ntot), idx: natLt(ntot)): natLt(ntot) = let
      val nxt = get_hashnext<key,itm> (ht, idx)
    in
      if nxt = ~1 then idx
      else let
        val k1 = get_key<key,itm> (ht, idx)
      in
        if equal_key_key<key> (k1, k0) then idx
        else aux (ht, nxt)
      end
    end // end of [aux]
    val idx = aux (ht, idx)
    val e1 = get_key<key,itm> (ht, idx)
  in
    if equal_key_key<key> (e1, k0) then let
      // duplicate element found
      val () = res := get_itm<key,itm> (ht, idx)
      val () = set_itm<key,itm> (ht, idx, elt)
      prval () = opt_some {itm} (res)
    in
      true
    end else let
      // find next free slot
      fun
      aux (
        ht: &hashtbl (key, itm, ntot), nxt: intBtw(~1, ntot)
      ): intBtw(~1, ntot) = (
        if nxt < 0 then nxt
        else let
          val e = empty<key,itm> (ht, nxt)
        in
          if e then nxt
          else let
            val nxt = pred(nxt)
          in
            aux (ht, nxt)
          end
        end
      ) (* end of [aux] *)
      val nextfree = aux (ht, ht.nextfree)
    in
      if nextfree = ~1 then let
        // table is full, unable to insert (have to resize)
        val-true = false
        prval () = opt_none {itm} (res)
      in
        false
      end else let
        // link the new slot to chain
        val () = set_hashnext<key,itm> (ht, idx, nextfree)
        val () = set_hashnext<key,itm> (ht, nextfree, ~1)
        val () = set_key_itm<key,itm> (ht, nextfree, k0, elt)
        val () = ht.nextfree := nextfree
        val () = ht.n := succ(ht.n)
        prval () = opt_none {itm} (res)
      in
        false
      end
    end
  end
end // end of [hashtbl_insert]
//
implement{key,itm}
hashtbl_search_ref {ntot} (ht, k0) = let
//
  val i = hash<key,itm> (ht, k0)
//
  fun
  aux (
   ht: &hashtbl (key, itm, ntot), i: intBtw(~1,ntot)
  ): intBtw(~1, ntot) =
    if i = ~1 then ~1
    else begin
      if empty<key,itm> (ht, i) then ~1
      else let
        val k1 = get_key<key,itm> (ht, i)
      in
        if equal_key_key<key> (k1, k0) then i
        else let
          val nxt = get_hashnext<key,itm> (ht, i)
        in
          aux (ht, nxt)
        end
      end
    end // end of [aux]
  val i = aux (ht, i)
in
  if i = ~1 then ~1
  else begin
    if empty (ht, i) then ~1
    else i
  end
end // end of [hashtbl_search_ref]
//
implement{key,itm}
hashtbl_search {ntot} (ht, k0, res) = let
//
  val i = hashtbl_search_ref<key,itm> (ht, k0)
//
in
  if i = ~1 then let
    prval () = opt_none {itm} (res)
  in
    false
  end else let
    val () = res := get_itm<key,itm> (ht, i)
    prval () = opt_some {itm} (res)
  in
    true
  end
end // end of [hashtbl_search]
//
implement{key,itm}
hashtbl_get_ref {ntot} (ht, k0) = let
  val res = get_itm (ht, k0)
in
  res
end // end of [hashtbl_get_ref]
//
end // end of [local]
//
(* ****** ****** *)
