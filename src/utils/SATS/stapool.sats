#include
"share/atspre_staload.hats"

(* ****** ****** *)
//
typedef STAPOOL (n:int, m:int, l:addr) = @(size_t n, size_t m, ptr l)
absvt@ype stapool_vt (a:t@ype, n:int, m:int) = [l:addr] STAPOOL (n, m, l)
typedef stapool_vt0 = STAPOOL (0, 0, null)
vtypedef stapool_vt1 (a:t@ype, n:int) = [i:int | i <= n] stapool_vt (a, i, n)
//
prfun
lemma_stapool_param {a:t@ype} {n,m:int} (
  !stapool_vt (a, n, m)
): [n >= 0; m >= 0; n <= m] void
//
fun{a:t@ype}
stapool_init {n:int} (
  &stapool_vt0? >> stapool_vt (a, 0, n)
, size_t n
): void
//
fun{}
stapool_free {a:t@ype} {n,m:int} (
  // NB. the type given to buf after returning
  // is the same as what it was prior to [stapool_init]
  !stapool_vt (a, n, m) >> stapool_vt0?
): void
//
fun{a:t@ype}
stapool_used {n,m:int} (&stapool_vt (a, n, m)): size_t n
//
fun{a:t@ype}
stapool_isnot_full {n,m:int} (
  &stapool_vt (a, n, m)
): bool (n < m)
//
typedef pptr (n:int) = natLt(n)
//
fun{a:t@ype}
stapool_alloc {n,m:int | n < m} (
  &stapool_vt (a, n, m) >> stapool_vt (a, n+1, m)
, a
): pptr (n+1)
//
(*
fun{a:t@ype}
stapool_read {n,m:int} (
  &stapool_vt (a, n, m)
, natLt(n)
): a
//
fun{a:t@ype}
stapool_write {n,m:int} (
  &stapool_vt (a, n, m) >> stapool_vt (a, n, m)
, natLt(n)
, a
): void*)
//
fun{a:t@ype}{env:vt@ype}
stapool_foreach$fwork (size_t(*idx*), a, &(env) >> _): void
//
fun{a:t@ype}{env:vt@ype}
stapool_foreach_env {n,m:int} (
  &stapool_vt (a, n, m), &(env) >> _
): void
//
fun{a:t@ype}
pptr_read
  {n0,n,m:int | n0 <= n}
  (&stapool_vt (a, n, m), pptr (n0)): a
//
fun{a:t@ype}
pptr_write
  {n0,n,m:int | n0 <= n}
  (&stapool_vt (a, n, m), pptr (n0), a): void
//
(* ****** end of [stapool.sats] ****** *)
