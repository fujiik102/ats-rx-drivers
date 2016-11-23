
(*
**
** A template for single-file ATS programs
**
*)

(* ****** ****** *)
//
#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"

staload "Pin.sats"
//
(* ****** ****** *)

//
// please write you program in this section
//

primplement bits8_test1 () = BEQNIL()
primplement bits8_test2 () = 
  BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQNIL))))))))
primplement bits8_test3 () = 
  BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQNIL))))))))

fn {b:bit}{bs:bits}{n,bn:int}
  changeBitBits (v:bits_int_t (n,bs),bn:int bn,b:bit_int_t b)
  : [bs':bits] (CHANGE_BIT_BITS (bs,bn,b,bs') | bits_int_t (n,bs')) =
  if b == I then lor (1 << bn, v) else land (~(1 << bn), v)
  

fun
{tk:tk}
g1int_ndiv2
  {i,j:int | i >= 0; j > 0}
(
  x: g1int(tk, i), y: g1int(tk, j)
) :<>
[
  q,r:int | 0 <= r; r < j
] (
  DIVMOD (i, j, q, r) | g1int (tk, q)
) (* end of [g1int_ndiv2] *) 
(* ****** ****** *)

implement main0 () = () // a dummy implementation for [main]

