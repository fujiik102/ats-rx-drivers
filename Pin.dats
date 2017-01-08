
(*
**
** A template for single-file ATS programs
**
*)

(* ****** ****** *)
//
#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"


staload UN = "prelude/SATS/unsafe.sats"
staload "Pin.sats"
//
(* ****** ****** *)

//
// please write you program in this section
//

(* ****** ****** *)

implement main0 () = () // a dummy implementation for [main]


primplement bits_test1 () = BEQNIL()
primplement bits8_test2 () = 
  BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQNIL))))))))
primplement bits8_test3 () = 
  BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQCONS1 (BEQNIL))))))))
primplement bits8_test4_1 () = BEQCONS1 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQNIL))))))))
primplement bits8_test4_2 () = BEQCONS0 (BEQCONS1 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQNIL))))))))
primplement bits8_test4_3 () = BEQCONS0 (BEQCONS0 (BEQCONS1 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQNIL))))))))
primplement bits8_test4_4 () = BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS1 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQNIL))))))))
primplement bits8_test4_5 () = BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS1 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQNIL))))))))
primplement bits8_test4_6 () = BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS1 (BEQCONS0 (BEQCONS0 (BEQNIL))))))))
primplement bits8_test4_7 () = BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS1 (BEQCONS0 (BEQNIL))))))))
primplement bits8_test4_8 () = BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS0 (BEQCONS1 (BEQNIL))))))))

primplement bitscons0_eq_double     {bs}{n,v} (bitseq) = BEQCONS0 (bitseq)
primplement bitscons0_eq__cons1_inc {bs}{n,v} (bitseq) = let prval BEQCONS0 (bitseq') = bitseq in BEQCONS1 (bitseq') end

extern praxi le_refl {n:int} ():[n <= n] void
extern praxi plus_0 {n:int} ():[n == n+0] void
extern praxi le_plus_1 {n,m:int | n <= m} ():[n <= m+1] void

prfun le_plus_nat {n,m:int | n <= m}{p:nat} .<p>. ():[n <= m+p] void =
  sif 0 < p then let
      prval () = le_plus_nat {n,m}{p-1} ()
    in le_plus_1 {n,m+(p-1)} () end
  else let
      prval () = plus_0 {m} ()
    in (* nothing *) end

dataprop BIT_OR (bit,bit,bit) =
 | {b:bit} BIT_OR_IL (I,b,I)
 | {b:bit} BIT_OR_IR (b,I,I)
 | BIT_OR_O (O,O,O)

dataprop BITS_OR (int,bits,bits,bits) =
 | BITS_OR_NIL (0,BitsNil,BitsNil,BitsNil) of ()
 | {n:int}{b,l,r:bit}{bs,lbs,rbs:bits}
   BITS_OR_CONS (n+1,BitsCons (l,lbs),BitsCons (r,rbs),BitsCons (b,bs))
    of (BIT_OR (l,r,b),BITS_OR (n,lbs,rbs,bs))

dataprop POW2 (int,int) =
 | POW2_0 (0,1) of ()
 | {n,v:int} POW2_N (n+1,v+v) of POW2 (n,v)

prfun pow2_total {n:nat} .<n>. ():[npow:int] POW2 (n,npow) =
  sif 0 < n then POW2_N (pow2_total {n-1} ())
            else POW2_0 ()

extern praxi pow2_domain_nat {n,npow:int} (POW2 (n,npow)):[0 <= n] void

prfun pow2_range_lte_1 {n:nat}{npow:int} .<n>. (pow:POW2 (n,npow)):[1 <= npow] void
 = case+ pow of
   | POW2_0 ()        => () // 1 <= 1
   | POW2_N (pow_ind) => let
       prval () = pow2_domain_nat (pow_ind)
       prval () = pow2_range_lte_1 (pow_ind)
     in  end // 1 <= npow_ind -> 1 <= npow_ind+npow_ind

prfn pow2_lte {n,npow:int} (pow2:POW2 (n,npow)):[0 <= n][1 <= npow] void
 = let
     prval () = pow2_domain_nat (pow2)
     prval () = pow2_range_lte_1 (pow2)
   in end

prfun pow2_injective {n,npow1,npow2:nat} .<n>. (pow1:POW2 (n,npow1), pow2:POW2 (n,npow2)):[npow1==npow2] void
 = sif 0 < n then let
       prval POW2_N (pow1') = pow1
       prval POW2_N (pow2') = pow2
     in pow2_injective (pow1',pow2') end
   else case+ (pow1,pow2) of
        | (POW2_0 (), POW2_0 ()) => () // 0 == 0
        | (POW2_N (pow_ind), _) =/=> let prval () = pow2_lte (pow_ind) in end // 0 == n && 0 <= n-1
        | (_, POW2_N (pow_ind)) =/=> let prval () = pow2_lte (pow_ind) in end // 0 == n && 0 <= n-1

(*
prfun {n,npow,v:int}{bs:bits}
  bits_eq_int_lt_pow2 (POW2 (n,npow),BITSEQINT (n,bs,v)):(v<npow)

//prfun {} doble_lt_inc ():[n+1 < m+m]

primplements {n,npow,v:int}{bs:bits}
  bits_eq_int_lt_pow2 (pow2:POW2 (n,npow),beq:BITSEQINT (n,bs,v)):[v<npow]() = let
    prfun ind {m,mpow:int}{cs:bits} (pow2:POW2 (m,mpow),ceq (m,cs,w)):[n<npow] =
      case+ ceq of
      | BEQNIL () => [0<1] ()
      | BEQCONS0 (ceqind) =>
        case+ pow2 of
        | POW2_N (pow2ind) => let
            () = ind (pow2ind, ceqind)
          in end
      | BEQCONS1 (ceqind) =>
        case+ pow2 of
        | POW2_N (pow2ind) => let
            () = ind (pow2ind, ceqind)
          in end
  in ind (pow2, beq)
  end
*)

prfn beqint_is_nat {n,v:int}{bs:bits}
  (beqint_fst:BITSEQINT (n,bs,v)):[0 <= v] void =
let
  prfun aux {n,v:int}{bs:bits} .<bs>. (beqint:BITSEQINT (n,bs,v)):[0 <= v] void =
    case+ beqint of
    | BEQNIL   ()       => le_refl ()   // 0 <= 0
    | BEQCONS0 (beqind) => aux (beqind) // (0 <= n) -> (0 <= n+0)
    | BEQCONS1 (beqind) => aux (beqind) // (0 <= n) -> (0 <= n+1)
in aux (beqint_fst) end

(*
dataprop NAT_MUL (int,int,int) =
 | {n:nat} NMULbas (n,0,0) of ()
 | {n,m,l:nat} NMULind (n,m+1,l+n) of NAT_MUL (n,m,l)

extern praxi inteq_refl {n:int} ():[n == n] void

prfun nhalf_is_half {n,h:nat} .<n>. (nhalf:NAT_MUL (2,h,n)):[n == h+h] void
 = case+ nhalf of
   | NMULbas ()                   => inteq_refl ()
   | NMULind {_,h',n'} (nhalfind) => nhalf_is_half {n',h'} (nhalfind)

prfun n_double_half_is_n {n:nat} .<n>. ():NAT_MUL (2,n,n+n)
 = sif 0 == n then NMULbas ()
   else NMULind (n_double_half_is_n {n-1} ())
*)

dataprop NAT_EVEN (int) =
 | NEVENbas (0) of ()
 | {n:nat} NEVENind (n+2) of NAT_EVEN (n)

dataprop NAT_ODD (int) =
 | NODDbas (1) of ()
 | {n:nat} NODDind (n+2) of NAT_ODD (n)

prfn {n:int} neven_nat (ev:NAT_EVEN (n)):[0 <= n] void
 = case+ ev of
   | NEVENbas ()       => le_refl ()
   | NEVENind {n'} (_) => le_plus_nat {0,n'}{2} ()

prfn {n:int} nodd_gte_1 (odd:NAT_ODD (n)):[1 <= n] void
 = sif 1 <= n then ()
       else case+ odd of
       | NODDbas ()       =/=> () // 1 < 1
       | NODDind {n'} (_) =/=> () // 0 <= n' && n'+2 < 1

prfun nodd_prev_is_even {n:nat} .<n>. (odd:NAT_ODD (n)):NAT_EVEN (n-1)
 = case+ odd of
   | NODDbas ()       => NEVENbas ()
   | NODDind (oddind) => let
       prval () = nodd_gte_1 (oddind)
     in NEVENind (nodd_prev_is_even (oddind)) end

datasort oddity = EVEN | ODD

dataprop NAT_ODDITY (int,oddity) =
 | {n:int} NATeven (n,EVEN) of NAT_EVEN (n)
 | {n:int} NATodd  (n,ODD)  of NAT_ODD  (n)

prfun natoddity_total {n:nat} .<n>. ():[o:oddity] NAT_ODDITY (n,o)
 = sif      n == 0 then NATeven (NEVENbas ())
   else sif n == 1 then NATodd  (NODDbas  ())
   else     case+ natoddity_total {n-2} () of
            | NATeven (ev)  => NATeven (NEVENind (ev))
            | NATodd  (odd) => let prval () = nodd_gte_1 (odd)
                               in NATodd  (NODDind  (odd)) end
(*
prfun nathalf_total_if_even {n:nat} .<n>. (ev:NAT_EVEN (n))
                           :[h:nat] NAT_MUL (2,h,n)
 = case+ ev of
   | NEVENbas ()   => NMULbas ()
   | NEVENind {n'} (ev) => let prval () = neven_nat<n'> (ev)
                      in NMULind (nathalf_total_if_even {n'} (ev)) end
*)
prfun nat_half {n:nat} .<n>. (ev:NAT_EVEN (n)):[h:nat | h+h == n] int h
 = case+ ev of
   | NEVENbas ()   => 0 // 0+0 == 0
   | NEVENind {n'} (ev) => let prval () = neven_nat<n'> (ev)
                           in nat_half {n'} (ev) + 1 (* h+h == n' -> h+1 + h+1 == n'+2 *) end
(*
prfn pow2_succ_double {n,npow,npow_succ:int} (pow2:POW2 (n,npow), pow2_succ:POW2 (n+1, npow_succ)):NAT_MUL (2,npow,npow_succ)
 = let
     prval () = pow2_lte (pow2)
     prval () = pow2_lte (pow2_succ)
     prval () = pow2_injective (POW2_N (pow2),pow2_succ)
   in n_double_half_is_n {npow} () end

extern praxi Sn_le_m__n_le_m {n,m:nat | n+1 <= m} ():[n <= m] void

prfun double_saves_lte_relation {n,m:nat | n <= m} .<m-n>. ():[n+n <= m+m] void
 = sif n == m then le_refl {n+n} ()
   else let
       prval () = double_saves_lte_relation {n+1,m} ()
       prval () = Sn_le_m__n_le_m {n+n+1,m+m} ()
     in Sn_le_m__n_le_m {n+n,m+m} () end
*)

prfn double_v_lt_2pow_succ__v_lt_2pow {v,n,npow_succ,npow:nat | v+v < npow_succ}
                                      (pow2:POW2(n,npow),pow2succ:POW2 (n+1,npow_succ)):[v < npow] void
 = let
     prval () = pow2_injective (POW2_N (pow2), pow2succ)// npow_succ == npow+npow
   in end // v+v < npow+npow -> v < npow

prfun nat_eq_bits {n,npow,v:nat | v < npow}{v <= INTMAX} .<n>.
  (pow2:POW2 (n,npow)):[bs:bits] BITSEQINT (n,bs,v) =
  sif 0 < n then let
      prval POW2_N {n',npow'} (pow2ind) = pow2
      prval () = pow2_lte (pow2ind)
    in case+ natoddity_total {v} () of
       | NATeven (ev) => let
           prval [h:int](_) = nat_half {v} (ev)
           prval () = double_v_lt_2pow_succ__v_lt_2pow {h,n',npow,npow'} (pow2ind,pow2) // h < npow'
         in BEQCONS0 (nat_eq_bits {n',npow',h} (pow2ind)) end
       | NATodd  (odd) => let
           prval (ev) = nodd_prev_is_even (odd)
           prval () = nodd_gte_1 (odd)
           prval [h:int](_) = nat_half {v-1} (ev)
           prval () = double_v_lt_2pow_succ__v_lt_2pow {h,n',npow,npow'} (pow2ind,pow2) // h < npow'
         in BEQCONS1 (nat_eq_bits {n',npow',h} (pow2ind)) end
    end
  else let
      prval () = pow2_injective (pow2, POW2_0 ())
    in BEQNIL () end

implement {bs:bits} setBitBits {n,bn} (v,bn)
 = let
     prval (biteq | intv) = v
     prval () = beqint_is_nat (biteq)
     val+ result = g1int2uint (intv) lor g0int2uint (1<<bn)

     extern prfun npow_intmax {n,npow:nat | n < INTBITS} (POW2 (n,npow)): [npow <= INTMAX] void
     prval [npow:int](pow2) = pow2_total{n} ()
     prval () = pow2_lte (pow2)
     prval () = npow_intmax (pow2)
     prval [w:int](w) = $UN.cast{natLt npow}{uint} (result)
     prval [wbits:bits](wbitseq) = nat_eq_bits{n,npow,w} (pow2)
     prval p = $UN.proof_assert{CHANGE_BIT_BITS (bs,bn,I,wbits)} ()
   in (p | (wbitseq | w)) end

implement {bs} clearBitBits {n,bn} (v,bn)
 = let
     prval (biteq | intv) = v
     prval () = beqint_is_nat (biteq)
     val+ result = g1int2uint (intv) land (lnot (g0int2uint (1<<bn)))

     extern prfun npow_intmax {n,npow:nat | n < INTBITS} (POW2 (n,npow)): [npow <= INTMAX] void
     prval [npow:int](pow2) = pow2_total{n} ()
     prval () = pow2_lte (pow2)
     prval () = npow_intmax (pow2)
     prval [w:int](w) = $UN.cast{natLt npow}{uint} (result)
     prval [wbits:bits](wbitseq) = nat_eq_bits{n,npow,w} (pow2)
     prval p = $UN.proof_assert{CHANGE_BIT_BITS (bs,bn,O,wbits)} ()
   in (p | (wbitseq | w)) end

(*
fn {b:bit}{bs:bits}
  changeBitBits {n,bn:nat | bn < n}{n < INTBITS} (bits_int_t (n,bs),int bn,bit_int_t b)
  : [bs':bits] (CHANGE_BIT_BITS (bs,bn,b,bs') | bits_int_t (n,bs'))
*)
implement {b}{bs} changeBitBits {n,bn} (v,bn,bint)
 = let
     extern prfun {b:bit}{v:int} chgbit_lemma (BITEQINT (b,v)):[0 <= v][v <= 1] void
     extern prfun {b:bit} chgbit_lemma2 (BITEQINT (b,0)):[O == b] void
     extern prfun {b:bit} chgbit_lemma3 (BITEQINT (b,1)):[I == b] void
     prval (biteq | bint') = bint
     prval () = chgbit_lemma<b> (biteq)
   in case+ bint' of
      | 0 => let prval () = chgbit_lemma2<b> (biteq)
                 val+ (chgbit | bitint) = clearBitBits (v,bn)
             in (chgbit_bit_eq (chgbit) | bitint) end
      | 1 => let prval () = chgbit_lemma3<b> (biteq)
                 val+ (chgbit | bitint) = setBitBits (v,bn)
             in (chgbit_bit_eq (chgbit) | bitint) end
   end

(*
fn {bs:bits}
  testBitBits {n,bn:nat | bn < n}{n < INTBITS} (bits_int_t (n,bs),int bn)
  : [b:bit] (TEST_BIT_BITS (bs,bn,b) | bool (b==I))
*)
implement {bs} testBitBits {n,bn} (v,bn)
 = let
     prval (biteq | intv) = v
     prval () = beqint_is_nat (biteq)
     val+ result = (g1int2uint 1 = ((g1int2uint (intv) >> bn) land g1int2uint 1))
     prval [bbit:bit](bbool) = $UN.cast{[b:bit](bool (b==I))}{bool} (result)
     prval p = $UN.proof_assert{TEST_BIT_BITS (bs,bn,bbit)} ()
   in (p | bbool) end

////
fn {bs,cs:bits}{p:IOPort}
  writePMR (PMR_V (p,bs) | ioport_t p, bits_int_t (8,cs))
   :(PMR_V (p,cs) | void)

fn {bs,cs:bits}{p:IOPort}{b:bit}
  changePMRBit {bn:int | bn < 8}
    (CHANGE_BIT_BITS (bs,bn,b,cs),
     !PMR_V (p,bs) >> PMR_V (p,cs)
    | pin_t (p,bn), bit_int_t b):void

fn {bs:bits}{p:IOPort}
  readPMR (!PMR_V (p,bs) | p:ioport_t p)
   :bits_int_t (8,bs)

fn {p:IOPort}{bs,cs:bits}{v: int}
  writePDR (PDR_PERMIT (p,cs),
            !PDR_V (p,bs) >> PDR_V (p,cs) |
            ioport_t p,bits_int_t (8,cs)):void

fn {p:IOPort}{bs:bits}
  readPDR (!PDR_V (p,bs) | ioport_t p)
   : bits_int_t (8,bs)

fn {p:IOPort}{bs,cs:bits}
  writePODR (PODR_PERMIT (p,cs),
             !PODR_V (p,bs) >> PODR_V (p,cs) |
             ioport_t p, bits_int_t (8,cs)):void

fn {p:IOPort}{bs:bits}
  readPODR (PODR_V (p,bs) | ioport_t p)
   :bits_int_t (8,bs)

fn getInitialPinViews (IOPortNotGetInitialView) :
    (GPIOView (Port0, 0) false false, GPIOView (Port0, 1),
     GPIOView (Port1, 0) false false, GPIOView (Port1, 1) | void)

fn configIOPin {pin:Pin}{rw,outv,bef_rw:bool} (pin:pin_t, rw:bool | GPIOView (id,bef_rw,outv)): (GPIOView (id,rw,outv) | void)
fn putIO {outv:bool}{bef_out:bit} (GPIOView (id,true,out) | id:Pin, bool outv): (GPIOView (id,true,outv) | void)
fn readIO {rw,outv,actualv:bool} (GPIOView (ud,rw,outv) | id:Pin): (GPIOView (id,rw,outv) | bool)

