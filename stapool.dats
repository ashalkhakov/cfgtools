#include
"share/atspre_staload.hats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)
//
typedef STAPOOL (n:int, m:int, l:addr) = @(size_t n, size_t m, ptr l)
absvt@ype stapool_vt (a:t@ype, n:int, m:int) = [l:addr] STAPOOL (n, m, l)
typedef stapool_vt0 = STAPOOL (0, 0, null)
vtypedef stapool_vt1 (a:t@ype, n:int) = [i:int | i <= n] stapool_vt (a, i, n)
//
extern
prfun
lemma_stapool_param {a:t@ype} {n,m:int} (
  !stapool_vt (a, n, m)
): [n >= 0; m >= 0; n <= m] void
//
extern
fun{a:t@ype}
stapool_init {n:int} (
  &stapool_vt0? >> stapool_vt (a, 0, n)
, size_t n
): void
//
extern
fun{}
stapool_free {a:t@ype} {n,m:int} (
  // NB. the type given to buf after returning
  // is the same as what it was prior to [stapool_init]
  !stapool_vt (a, n, m) >> stapool_vt0?
): void
//
extern
fun{a:t@ype}
stapool_used {n,m:int} (&stapool_vt (a, n, m)): size_t n
//
extern
fun{a:t@ype}
stapool_isnot_full {n,m:int} (
  &stapool_vt (a, n, m)
): bool (n < m)
//
typedef pptr (n:int) = natLt(n)
//
extern
fun{a:t@ype}
stapool_alloc {n,m:int | n < m} (
  &stapool_vt (a, n, m) >> stapool_vt (a, n+1, m)
, a
): pptr (n+1)
//
(*
extern
fun{a:t@ype}
stapool_read {n,m:int} (
  &stapool_vt (a, n, m)
, natLt(n)
): a
//
extern
fun{a:t@ype}
stapool_write {n,m:int} (
  &stapool_vt (a, n, m) >> stapool_vt (a, n, m)
, natLt(n)
, a
): void*)
//
extern
fun{a:t@ype}{env:vt@ype}
stapool_foreach$fwork (size_t(*idx*), a, &(env) >> _): void
//
extern
fun{a:t@ype}{env:vt@ype}
stapool_foreach_env {n,m:int} (
  &stapool_vt (a, n, m), &(env) >> _
): void
//
extern
fun{a:t@ype}
pptr_read
  {n0,n,m:int | n0 <= n}
  (&stapool_vt (a, n, m), pptr (n0)): a
//
extern
fun{a:t@ype}
pptr_write
  {n0,n,m:int | n0 <= n}
  (&stapool_vt (a, n, m), pptr (n0), a): void
//
(* ****** end of [stapool.sats] ****** *)

//
local
//
staload UN = "prelude/SATS/unsafe.sats"
//
vtypedef varr_vt (a:t@ype, n:int, m:int, l:addr) = (
  array_v (a, l, n)
, array_v (a?, l + n*sizeof(a), m-n)
, mfree_gc_v (l)
| ptr l
) (* end of [varr_vt] *)
// NB. the structure of the type closely follows
// the structure given in the interface; we are only
// allowed to refine the tuple elements, but not
// add some new elements, even if we only add proofs
// NB. we don't add a top-level constraint to the top (e.g. [n>=0])
assume stapool_vt (a:t@ype, n:int, m:int) = @(
  size_t n
, size_t m
, [l:addr] varr_vt (a, n, m, l)
) (* end of [buf_vt] *)
//
extern
fun{a:vt@ype}
ptr1_diff {l:addr} {i:nat} (p0: ptr l, p1: ptr (l+i*sizeof(a))): size_t i
implement{a}
ptr1_diff {l} {i} (p0, p1) = let
  prval () = lemma_sizeof {a} ()
  prval pf1_mul = mul_make {i,sizeof(a)} ()
  prval () = mul_nat_nat_nat {i,sizeof(a)} (pf1_mul)
  prval () = prop_verify_and_add {l <= l+i*sizeof(a)} ()
  val diff = sub_ptr1_ptr1 (p1, p0)
  prval [i0:int] EQINT () = eqint_make_gint (diff)
  prval () = prop_verify_and_add {i0 >= 0} ()
  val diff = g1int2uint_ssize_size {i0} (diff)
  prval () = prop_verify_and_add {i*sizeof(a) == i0} ()
//
  prval () = __assert () where {
    extern
    praxi __assert (): [sizeof(a) > 0] void
  } (* end of [prval] *)
//
  val [q,r:int] (
    pf_divmod:DIVMOD(i*sizeof(a),sizeof(a),q,r) | res
  ) = g1uint_div2 {i*sizeof(a),sizeof(a)} (diff, sizeof<a>)
//
  prval () = __lemma {i,sizeof(a)} {i*sizeof(a),q,r} (pf1_mul, pf_divmod) where {
    // if [y] is one of divisors of [x], then we can
    // divide [x] by [y] with no remainder
    extern
    prfun __lemma {x,y:int | x >= 0; y > 0} {p,q,r:int} (
      pf_mul: MUL (x,y,p), pf_divmod: DIVMOD (p,y,q,r)
    ): [r==0;q==x] void
  } (* end of [prval] *)
//
in
  res
end // end of [ptr1_diff]
//
in (* of [local] *)
//
implement{a}
stapool_init {n} (buf, n) = {
  val (pf_bytes, pf_free | p_arr) = array_ptr_alloc<a> (n)
  prval () = lemma_array_v_param {a?} (pf_bytes)
  val () = buf.0 := (i2sz)0
  val () = buf.1 := n

  val () = __cast (buf.2) where {
    extern
    castfn
    __cast (!ptr (null)? >> varr_vt (a, 0, 0, null)): void
  } (* end of [prval] *)

  prval () = __discard (buf.2.0, buf.2.1, buf.2.2) where {
    extern
    prfun
    __discard (
      array_v (a, null, 0)
    , array_v (a?, null + 0*sizeof(a), 0)
    , mfree_gc_v (null)
    ): void
  } (* end of [prval] *)
  prval () = $effmask_wrt (buf.2.0 := array_v_nil {a} ())
  prval () = $effmask_wrt (buf.2.1 := pf_bytes)
  prval () = $effmask_wrt (buf.2.2 := pf_free)
  val () = buf.2.3 := p_arr
} (* end of [stapool_init] *)
//
implement{}
stapool_free {a} {m,n} (buf) = let
//
val (pf1_arr, pf2_arr, pf_free | p) = buf.2
//
prval pf1_arr = __trustme {a} (pf1_arr) where {
  // can be proven by induction over [n] using [topize]
  extern
  prval __trustme : {a:t@ype} {l:addr} {n:int} array_v (INV(a), l, n) -<> array_v (a?, l, n)
} // end of [prval]
//
prval pf_arr = array_v_unsplit {a?} (pf1_arr, pf2_arr)
//
val () = array_ptr_free {a} (pf_arr, pf_free | p)
//
in
end // end of [stapool_free]
//
implement{a}
stapool_isnot_full {n,m} (buf) = buf.0 < buf.1
//
implement{a}
stapool_used {n,m} (buf) = buf.0
//
implement{a}
stapool_alloc {n,m} (buf, x) = let
  val (pf1_arr, pf2_arr, pf_free | p_buf) = buf.2
  prval [l:addr] EQADDR () = eqaddr_make_ptr (p_buf)
  prval () = lemma_array_v_param (pf1_arr)
  prval () = lemma_array_v_param (pf2_arr)
  prval (pf1_at, pf2_arr) = array_v_uncons {a?} {l+n*sizeof(a)} (pf2_arr)
  prval () = lemma_array_v_param (pf1_arr)
  val p = ptr1_add_guint<a> (p_buf, buf.0)
  prval [l1:addr] EQADDR () = eqaddr_make_ptr (p)
  val () = ptr_set<a> (pf1_at | p, x)
  val i = buf.0
  val () = buf.0 := succ (buf.0)
  prval pf1_arr = array_v_extend (pf1_arr, pf1_at)
  val () = buf.2 := (pf1_arr, pf2_arr, pf_free | p_buf)
in
  (sz2i)i
end // end of [stapool_alloc]
//
(*
implement{a}
stapool_read {n,m} (buf, i) = let
  prval pf_arr = buf.0.0
  val p_arr = buf.2
  val res = array_get_at_gint<a> (!p_arr, i)
  prval () = $effmask_wrt (buf.0.0 := pf_arr)
in
  res
end // end of [stapool_read]
//
implement{a}
stapool_write {n,m} (buf, i, x) = {
//
  prval pf_arr = buf.0.0
  val p_arr = buf.2
  val () = array_set_at_gint<a> (!p_arr, i, x)
  prval () = $effmask_wrt (buf.0.0 := pf_arr)
//
} (* end of [stapool_write] *)
*)
//
implement{a}{env}
stapool_foreach$fwork (idx, x, env) = ()
//
implement{a}{env}
stapool_foreach_env {n,m} (buf, env) = {
  implement
  array_iforeach$cont<a><env> (i, x, env) = true
  implement
  array_iforeach$fwork<a><env> (i, x, env) =
    stapool_foreach$fwork (i, x, env)
  val n = stapool_used<a> (buf)
  val (pf1_arr, pf2_arr, pf_free | p_buf) = buf.2
  val _ = array_iforeach_env<a><env> (!p_buf, n, env)
  val () = buf.2 := (pf1_arr, pf2_arr, pf_free | p_buf)
} (* end of [stapool_foreach_env] *)
//
implement{a}
pptr_read {n0,n1,m1} (buf, i) = let
  val (pf1_arr, pf2_arr, pf_free | p_buf) = buf.2
  val res = array_get_at_gint<a> (!p_buf, i)
  prval () = $effmask_wrt (buf.2 := (pf1_arr, pf2_arr, pf_free | p_buf))
in
  res
end // end of [pptr_read]
//
implement{a}
pptr_write {n0,n1,m1} (buf, r, x) = let
//
  val (pf1_arr, pf2_arr, pf_free | p_buf) = buf.2
  val () = array_set_at_gint<a> (!p_buf, r, x)
  prval () = $effmask_wrt (buf.2 := (pf1_arr, pf2_arr, pf_free | p_buf))
//
in
end // end of [pptr_write]
//
end (* of [local] *)
//

(* ****** end of [stapool.dats] ****** *)
