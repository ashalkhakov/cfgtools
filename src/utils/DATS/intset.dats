#include "share/atspre_staload.hats"

// a tagset is a set where every element is tagged
// - compare elements modulo the tags
// - before inserting element with a tag, check if such element has already been assigned a tag
// see: https://github.com/ashalkhakov/ATS-Lang/blob/master/utils/atslex/top.sats
// - states_t

abstype
tagset_type (t@ype(*itm*)) = ptr
typedef tagset (a:t@ype) = tagset_type (a)

extern
fun{a:t0p}
compare_elt_elt (x1: a, x2: a):<> int

extern
fun{}
funtagset_nil {a:t0p} ():<> tagset(a)
extern
fun{}
funtagset_make_nil {a:t0p} ():<> tagset(a)

extern
fun{a:t0p}
funtagset_sing (tag: int, x0: a):<> tagset(a)
extern
fun{a:t0p}
funtagset_make_sing (tag: int, x0: a):<> tagset(a)

extern
fun{a:t0p}
funtagset_make_list (xs: List(INV(@(int, a)))):<> tagset(a)

fun{}
funtagset_is_nil {a:t0p} (xs: set(INV(a))):<> bool
fun{}
funtagset_isnot_nil {a:t0p} (xs: set(INV(a))):<> bool

fun{a:t0p}
funtagset_find_tag (xs: set(INV(a)), x0: a):<> int(*~1 or tag*)

fun{a:t0p}
funtagset_insert
  (xs: &set(INV(a)) >> _, tag0: int, x0: a, res: &int? >> opt (int, b)):<!wrt> #[b:bool] bool b(*[x0] in [xs]*)
// end of [funtagset_insert]
