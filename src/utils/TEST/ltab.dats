#include
"share/atspre_staload.hats"

staload "libats/SATS/hashfun.sats"
staload _ = "libats/DATS/hashfun.dats"
//
staload _ = "prelude/DATS/integer.dats"
staload _ = "prelude/DATS/array.dats"
staload _ = "prelude/DATS/gnumber.dats"

staload "./../SATS/ltab.sats"
staload _ = "./../DATS/ltab.dats"

//
implement main0 () = {
//
  typedef T = string
  typedef V = int
  #define SZ 1024
  var ht : HASHTBLNODE // unhashtbl_make_nilialized
  val sz = (i2sz)SZ
  val () = hashtbl_make_nil<T,V> (ht, sz)
//
  fun
  test_insertlkup (ht: &hashtbl (T, V, SZ) >> hashtbl (T, V, SZ), k: T, v: V): void = {
    var itm: V
    val () = fprint!(stdout_ref, "insert [", k, "] <- [", v,"]; ")
    val-false = hashtbl_insert<T,V> (ht, k, v, itm)
    prval () = opt_clear {V} (itm)
    val-true = hashtbl_search<T,V> (ht, k, itm)
    prval () = opt_unsome {V} (itm)
    val () = fprint!(stdout_ref, "lookup [", k, "] = [", itm, "]: ")
    val () =
      if itm = v then fprintln!(stdout_ref, "OK")
      else fprintln!(stdout_ref, "FAILED")
    // end of [val]
  } (* end of [test_insertlkup] *)
//
  fun
  test_insertlkup_dup (ht: &hashtbl (T, V, SZ) >> hashtbl (T, V, SZ), k: T, v: V): void = {
    var itm: V
    val () = fprint!(stdout_ref, "insert (dup) [", k, "] <- [", v,"]; ")
    val-true = hashtbl_insert<T,V> (ht, k, v, itm)
    prval () = opt_clear {V} (itm)
    val-true = hashtbl_search<T,V> (ht, k, itm)
    prval () = opt_unsome {V} (itm)
    val () = fprint!(stdout_ref, "lookup [", k, "] = [", itm, "]: ")
    val () =
      if itm = v then fprintln!(stdout_ref, "OK")
      else fprintln!(stdout_ref, "FAILED")
    // end of [val]
  } (* end of [test_insertlkup_dup] *)
//
  val () = test_insertlkup (ht, "hello", 0)
  val () = test_insertlkup (ht, "hey", 1)
  val () = test_insertlkup (ht, "there", 2)
  val () = test_insertlkup (ht, "hey 2", 3)
//
  val () = test_insertlkup_dup (ht, "hello", 5)
  val () = test_insertlkup_dup (ht, "there", 35)
//
  val () = hashtbl_free<T,V> (ht)
} (* end of [main0] *)
