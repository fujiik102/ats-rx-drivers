
(*
**
** A template for single-file ATS programs
**
*)

(* ****** ****** *)
//
#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"


staload "prelude/SATS/char.sats"
staload UN = "prelude/SATS/unsafe.sats"
staload "Bit.sats"
staload "Bit.dats"
staload "Pin.sats"
//
  (* ****** ****** *)

//
// please write you program in this section
//

(* ****** ****** *)

implement main0 () = () // a dummy implementation for [main]

// Pin control drivers

// Definitons for implementations

typedef ioport_impl_type = int
typedef bits8_uint_impl_type = uint

extern fun writePMR_impl (p: ioport_impl_type, v: bits8_uint_impl_type):<!wrt> void = "ext#"
extern fun readPMR_impl (p: ioport_impl_type):<!ref> bits8_uint_impl_type = "ext#"
extern fun writePDR_impl (p: ioport_impl_type, v: bits8_uint_impl_type):<!wrt> void = "ext#"
extern fun readPDR_impl (p: ioport_impl_type):<!ref> bits8_uint_impl_type = "ext#"
extern fun writePODR_impl (p: ioport_impl_type, v: bits8_uint_impl_type):<!wrt> void = "ext#"
extern fun readPODR_impl (p: ioport_impl_type):<!ref> bits8_uint_impl_type = "ext#"
extern fun readPIDR_impl (p: ioport_impl_type):<!ref> bits8_uint_impl_type = "ext#"


extern prfn bisect_spec_half_plus_half__full {r,s,t,u:bisectional | bisectional_half_b (r,s) && bisectional_half_b (r,t) && bisectional_add_b (s,t,u)} (): [r==u] void

extern prfn bisect_spec_mul2_half__one {r,s,t,u:bisectional | bisectional_add_b (r,r,s) && bisectional_half_b (s,t)} (): [r==t] void

prfn biset_half (): [bisectional_half_b (bisect1,bisectional (1,1))] void
 = let
   prval unitp = bisectional_half_axi<1,0> ()
 in end


// PMR
implement {p}{bs,cs}{b} changePMRBit {bn}
          (bs_chg_cs,pmr_v,perm | pin,bit)
 = let
     val+ @(ioport,bitnum) = pin
     val+ bsnum = readPMR (pmr_v | ioport)
     prval () = chgbit_bnum_nat (bs_chg_cs)
     val+ [bs':bits] (bs_chg_bs' | csnum) = changeBitBits (bsnum, bitnum, bit)
     prval () = chgbit_bits_injective (bs_chg_cs,bs_chg_bs')
     prval EQBITS () = eqbits_make {cs,bs'}()
     val+ () = writePMR (pmr_v,perm | ioport,csnum)
   in end

implement pmr2pmr_bits {p}{b7,b6,b5,b4,b3,b2,b1,b0}{v}(pmr_v | bs_v)
 = let
     prval PMR_V (pmrbit7,pmrbit6,pmrbit5,pmrbit4,pmrbit3,pmrbit2,pmrbit1,pmrbit0)
           = pmr_v
     val+ [b0_:bit](test_b0 | bool_b0) = testBitBits (bs_v,i2u 0)
     prval () = testbit_buttombit {..}{b0,b0_}(test_b0)
     prval EQBIT () = eqbit_make {b0,b0_}()
     val+ [b1_:bit](test_b1 | bool_b1) = testBitBits (bs_v,i2u 1) 
     prval TEST_BIT_BITS_ind (test_b1_base) = test_b1
     prval () = testbit_buttombit {..}{b1,b1_}(test_b1_base)
     prval EQBIT () = eqbit_make {b1,b1_}()
     val+ [b2_:bit](test_b2 | bool_b2) = testBitBits (bs_v,i2u 2) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b2_base)) = test_b2
     prval () = testbit_buttombit {..}{b2,b2_}(test_b2_base)
     prval EQBIT () = eqbit_make {b2,b2_}()
     val+ [b3_:bit](test_b3 | bool_b3) = testBitBits (bs_v,i2u 3) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b3_base))) = test_b3
     prval () = testbit_buttombit {..}{b3,b3_}(test_b3_base)
     prval EQBIT () = eqbit_make {b3,b3_}()
     val+ [b4_:bit](test_b4 | bool_b4) = testBitBits (bs_v,i2u 4) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b4_base)))) = test_b4
     prval () = testbit_buttombit {..}{b4,b4_}(test_b4_base)
     prval EQBIT () = eqbit_make {b4,b4_}()
     val+ [b5_:bit](test_b5 | bool_b5) = testBitBits (bs_v,i2u 5) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b5_base))))) = test_b5
     prval () = testbit_buttombit {..}{b5,b5_}(test_b5_base)
     prval EQBIT () = eqbit_make {b5,b5_}()
     val+ [b6_:bit](test_b6 | bool_b6) = testBitBits (bs_v,i2u 6) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b6_base)))))) = test_b6
     prval () = testbit_buttombit {..}{b6,b6_}(test_b6_base)
     prval EQBIT () = eqbit_make {b6,b6_}()
     val+ [b7_:bit](test_b7 | bool_b7) = testBitBits (bs_v,i2u 7) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b7_base))))))) = test_b7
     prval () = testbit_buttombit {..}{b7,b7_}(test_b7_base)
     prval EQBIT () = eqbit_make {b7,b7_}()
   in (pmrbit7,pmrbit6,pmrbit5,pmrbit4,pmrbit3,pmrbit2,pmrbit1,pmrbit0,
       test_b0,test_b1,test_b2,test_b3,test_b4,test_b5,test_b6,test_b7
      | (bool_b7,bool_b6,bool_b5,bool_b4,bool_b3,bool_b2,bool_b1,bool_b0)) end


// PDR
implement {p}{bs,cs}{b} changePDRBit {bn}
          (bs_chg_cs,pdr_v,perm | pin,bit)
 = let
     val+ @(ioport,bitnum) = pin
     val+ bsnum = readPDR (pdr_v | ioport)
     prval () = chgbit_bnum_nat (bs_chg_cs)
     val+ [bs':bits] (bs_chg_bs' | csnum) = changeBitBits (bsnum, bitnum, bit)
     prval () = chgbit_bits_injective (bs_chg_cs,bs_chg_bs')
     prval EQBITS () = eqbits_make {cs,bs'}()
     val+ () = writePDR (pdr_v,perm | ioport,csnum)
   in end

implement pdr2pdr_bits {p}{b7,b6,b5,b4,b3,b2,b1,b0}{v}(pdr_v | bs_v)
 = let
     prval PDR_V (pdrbit7,pdrbit6,pdrbit5,pdrbit4,pdrbit3,pdrbit2,pdrbit1,pdrbit0)
           = pdr_v
     val+ [b0_:bit](test_b0 | bool_b0) = testBitBits (bs_v,i2u 0)
     prval () = testbit_buttombit {..}{b0,b0_}(test_b0)
     prval EQBIT () = eqbit_make {b0,b0_}()
     val+ [b1_:bit](test_b1 | bool_b1) = testBitBits (bs_v,i2u 1) 
     prval TEST_BIT_BITS_ind (test_b1_base) = test_b1
     prval () = testbit_buttombit {..}{b1,b1_}(test_b1_base)
     prval EQBIT () = eqbit_make {b1,b1_}()
     val+ [b2_:bit](test_b2 | bool_b2) = testBitBits (bs_v,i2u 2) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b2_base)) = test_b2
     prval () = testbit_buttombit {..}{b2,b2_}(test_b2_base)
     prval EQBIT () = eqbit_make {b2,b2_}()
     val+ [b3_:bit](test_b3 | bool_b3) = testBitBits (bs_v,i2u 3) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b3_base))) = test_b3
     prval () = testbit_buttombit {..}{b3,b3_}(test_b3_base)
     prval EQBIT () = eqbit_make {b3,b3_}()
     val+ [b4_:bit](test_b4 | bool_b4) = testBitBits (bs_v,i2u 4) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b4_base)))) = test_b4
     prval () = testbit_buttombit {..}{b4,b4_}(test_b4_base)
     prval EQBIT () = eqbit_make {b4,b4_}()
     val+ [b5_:bit](test_b5 | bool_b5) = testBitBits (bs_v,i2u 5) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b5_base))))) = test_b5
     prval () = testbit_buttombit {..}{b5,b5_}(test_b5_base)
     prval EQBIT () = eqbit_make {b5,b5_}()
     val+ [b6_:bit](test_b6 | bool_b6) = testBitBits (bs_v,i2u 6) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b6_base)))))) = test_b6
     prval () = testbit_buttombit {..}{b6,b6_}(test_b6_base)
     prval EQBIT () = eqbit_make {b6,b6_}()
     val+ [b7_:bit](test_b7 | bool_b7) = testBitBits (bs_v,i2u 7) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b7_base))))))) = test_b7
     prval () = testbit_buttombit {..}{b7,b7_}(test_b7_base)
     prval EQBIT () = eqbit_make {b7,b7_}()
   in (pdrbit7,pdrbit6,pdrbit5,pdrbit4,pdrbit3,pdrbit2,pdrbit1,pdrbit0,
       test_b0,test_b1,test_b2,test_b3,test_b4,test_b5,test_b6,test_b7
      | (bool_b7,bool_b6,bool_b5,bool_b4,bool_b3,bool_b2,bool_b1,bool_b0)) end


// PODR
implement {p}{bs,cs}{b} changePODRBit {bn}
          (bs_chg_cs,podr_v,perm | pin,bit)
 = let
     val+ @(ioport,bitnum) = pin
     val+ bsnum = readPODR (podr_v | ioport)
     prval () = chgbit_bnum_nat (bs_chg_cs)
     val+ [bs':bits] (bs_chg_bs' | csnum) = changeBitBits (bsnum, bitnum, bit)
     prval () = chgbit_bits_injective (bs_chg_cs,bs_chg_bs')
     prval EQBITS () = eqbits_make {cs,bs'}()
     val+ () = writePODR (podr_v,perm | ioport,csnum)
   in end

implement podr2podr_bits {p}{b7,b6,b5,b4,b3,b2,b1,b0}{v}(podr_v | bs_v)
 = let
     prval PODR_V (podrbit7,podrbit6,podrbit5,podrbit4,podrbit3,podrbit2,podrbit1,podrbit0)
           = podr_v
     val+ [b0_:bit](test_b0 | bool_b0) = testBitBits (bs_v,i2u 0)
     prval () = testbit_buttombit {..}{b0,b0_}(test_b0)
     prval EQBIT () = eqbit_make {b0,b0_}()
     val+ [b1_:bit](test_b1 | bool_b1) = testBitBits (bs_v,i2u 1) 
     prval TEST_BIT_BITS_ind (test_b1_base) = test_b1
     prval () = testbit_buttombit {..}{b1,b1_}(test_b1_base)
     prval EQBIT () = eqbit_make {b1,b1_}()
     val+ [b2_:bit](test_b2 | bool_b2) = testBitBits (bs_v,i2u 2) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b2_base)) = test_b2
     prval () = testbit_buttombit {..}{b2,b2_}(test_b2_base)
     prval EQBIT () = eqbit_make {b2,b2_}()
     val+ [b3_:bit](test_b3 | bool_b3) = testBitBits (bs_v,i2u 3) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b3_base))) = test_b3
     prval () = testbit_buttombit {..}{b3,b3_}(test_b3_base)
     prval EQBIT () = eqbit_make {b3,b3_}()
     val+ [b4_:bit](test_b4 | bool_b4) = testBitBits (bs_v,i2u 4) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b4_base)))) = test_b4
     prval () = testbit_buttombit {..}{b4,b4_}(test_b4_base)
     prval EQBIT () = eqbit_make {b4,b4_}()
     val+ [b5_:bit](test_b5 | bool_b5) = testBitBits (bs_v,i2u 5) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b5_base))))) = test_b5
     prval () = testbit_buttombit {..}{b5,b5_}(test_b5_base)
     prval EQBIT () = eqbit_make {b5,b5_}()
     val+ [b6_:bit](test_b6 | bool_b6) = testBitBits (bs_v,i2u 6) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b6_base)))))) = test_b6
     prval () = testbit_buttombit {..}{b6,b6_}(test_b6_base)
     prval EQBIT () = eqbit_make {b6,b6_}()
     val+ [b7_:bit](test_b7 | bool_b7) = testBitBits (bs_v,i2u 7) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b7_base))))))) = test_b7
     prval () = testbit_buttombit {..}{b7,b7_}(test_b7_base)
     prval EQBIT () = eqbit_make {b7,b7_}()
   in (podrbit7,podrbit6,podrbit5,podrbit4,podrbit3,podrbit2,podrbit1,podrbit0,
       test_b0,test_b1,test_b2,test_b3,test_b4,test_b5,test_b6,test_b7
      | (bool_b7,bool_b6,bool_b5,bool_b4,bool_b3,bool_b2,bool_b1,bool_b0)) end

// PIDR
implement pidr2pidr_bits {p}{b7,b6,b5,b4,b3,b2,b1,b0}{v}(pidr_p | bs_v)
 = let
     prval PIDR_P (pidrbit7,pidrbit6,pidrbit5,pidrbit4,pidrbit3,pidrbit2,pidrbit1,pidrbit0)
           = pidr_p
     val+ [b0_:bit](test_b0 | bool_b0) = testBitBits (bs_v,i2u 0)
     prval () = testbit_buttombit {..}{b0,b0_}(test_b0)
     prval EQBIT () = eqbit_make {b0,b0_}()
     val+ [b1_:bit](test_b1 | bool_b1) = testBitBits (bs_v,i2u 1) 
     prval TEST_BIT_BITS_ind (test_b1_base) = test_b1
     prval () = testbit_buttombit {..}{b1,b1_}(test_b1_base)
     prval EQBIT () = eqbit_make {b1,b1_}()
     val+ [b2_:bit](test_b2 | bool_b2) = testBitBits (bs_v,i2u 2) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b2_base)) = test_b2
     prval () = testbit_buttombit {..}{b2,b2_}(test_b2_base)
     prval EQBIT () = eqbit_make {b2,b2_}()
     val+ [b3_:bit](test_b3 | bool_b3) = testBitBits (bs_v,i2u 3) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b3_base))) = test_b3
     prval () = testbit_buttombit {..}{b3,b3_}(test_b3_base)
     prval EQBIT () = eqbit_make {b3,b3_}()
     val+ [b4_:bit](test_b4 | bool_b4) = testBitBits (bs_v,i2u 4) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b4_base)))) = test_b4
     prval () = testbit_buttombit {..}{b4,b4_}(test_b4_base)
     prval EQBIT () = eqbit_make {b4,b4_}()
     val+ [b5_:bit](test_b5 | bool_b5) = testBitBits (bs_v,i2u 5) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b5_base))))) = test_b5
     prval () = testbit_buttombit {..}{b5,b5_}(test_b5_base)
     prval EQBIT () = eqbit_make {b5,b5_}()
     val+ [b6_:bit](test_b6 | bool_b6) = testBitBits (bs_v,i2u 6) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b6_base)))))) = test_b6
     prval () = testbit_buttombit {..}{b6,b6_}(test_b6_base)
     prval EQBIT () = eqbit_make {b6,b6_}()
     val+ [b7_:bit](test_b7 | bool_b7) = testBitBits (bs_v,i2u 7) 
     prval TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (TEST_BIT_BITS_ind (test_b7_base))))))) = test_b7
     prval () = testbit_buttombit {..}{b7,b7_}(test_b7_base)
     prval EQBIT () = eqbit_make {b7,b7_}()
   in (pidrbit7,pidrbit6,pidrbit5,pidrbit4,pidrbit3,pidrbit2,pidrbit1,pidrbit0,
       test_b0,test_b1,test_b2,test_b3,test_b4,test_b5,test_b6,test_b7
      | (bool_b7,bool_b6,bool_b5,bool_b4,bool_b3,bool_b2,bool_b1,bool_b0)) end


implement {p}{bs,cs} writePMR (pmr_v,perm | p,v) = let
    val+ (eqint | v0) = v
    val+ () = writePMR_impl (p,v0)
    prval () = $UN.castview2void (pmr_v)
  in end

implement {p}{bs} readPMR (pmr_v | p) = let
    val+ v = readPMR_impl (p)
    val+ [sta_v:int] v = g1ofg0_uint (v)
    prval bs_eq_v = $UN.proof_assert {BITSEQINT (8,bs,sta_v)}()
  in (bs_eq_v | v) end

implement {p}{bs,cs} writePDR (pdr_v,perm | p,v) = let
    val+ (eqint | v0) = v
    val+ () = writePDR_impl (p,v0)
    prval () = $UN.castview2void (pdr_v)
  in end

implement {p}{bs} readPDR (pdr_v | p) = let
    val+ v = readPDR_impl (p)
    val+ [sta_v:int] v = g1ofg0_uint (v)
    prval bs_eq_v = $UN.proof_assert {BITSEQINT (8,bs,sta_v)}()
  in (bs_eq_v | v) end

implement {p}{bs,cs} writePODR (podr_v,perm | p,v) = let
    val+ (eqint | v0) = v
    val+ () = writePODR_impl (p,v0)
    prval () = $UN.castview2void (podr_v)
  in end

implement {p}{bs} readPODR (podr_v | p) = let
    val+ v = readPODR_impl (p)
    val+ [sta_v:int] v = g1ofg0_uint (v)
    prval bs_eq_v = $UN.proof_assert {BITSEQINT (8,bs,sta_v)}()
  in (bs_eq_v | v) end

implement {p} readPIDR (p) = let
    val+ v = readPIDR_impl (p)
    val+ [sta_v:int] v = g1ofg0_uint (v)
    prval pow2 = POW2_N (POW2_N (POW2_N (POW2_N (
                 POW2_N (POW2_N (POW2_N (POW2_N (
                 POW2_0 ()))))))))
    prval () = $UN.prop_assert {sta_v < 256}()
    prval [bs:bits] bseqv = nat_eq_bits {8,256,sta_v}(pow2)
    prval pidr_p = $UN.proof_assert {PIDR_P (p,bs)}()
  in (pidr_p | (bseqv | v)) end

