
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


// PMR
(*
fn {bs,cs:bits}{p:IOPort}
  writePMR (!PMR_V (p,bs) >> PMR_V (p,cs),PMR_PERMIT (p,cs)
           | ioport_t p,bits_uint_t (8,cs))
   :<!wrt> void
*)

implement {bs,cs}{p}{b} changePMRBit {bn}
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

(*fn pmr2pmr_bits_ {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}{v:int}
   (pmr_v:PMR_V (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) | bs_v:bits_uint_t (8,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)))
   :(PMR_BIT_V (Pin (p,7),b7,bisect1),
     PMR_BIT_V (Pin (p,6),b6,bisect1),
     PMR_BIT_V (Pin (p,5),b5,bisect1),
     PMR_BIT_V (Pin (p,4),b4,bisect1),
     PMR_BIT_V (Pin (p,3),b3,bisect1),
     PMR_BIT_V (Pin (p,2),b2,bisect1),
     PMR_BIT_V (Pin (p,1),b1,bisect1),
     PMR_BIT_V (Pin (p,0),b0,bisect1),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),0,b0),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),1,b1),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),2,b2),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),3,b3),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),4,b4),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),5,b5),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),6,b6),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),7,b7)
    | @(bool (b0 == I),bool (b1 == I),bool (b2 == I),bool (b3 == I),
        bool (b4 == I),bool (b5 == I),bool (b6 == I),bool (b7 == I)))
*)
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
(*
fn {p:IOPort}{bs,cs:bits}{v: int}
  writePDR (PDR_PERMIT (p,cs),
            !PDR_V (p,bs) >> PDR_V (p,cs) |
            ioport_t p,bits_uint_t (8,cs)):<!wrt> void
*)

implement {bs,cs}{p}{b} changePDRBit {bn}
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

(*
fn {p:IOPort}{bs:bits}
  readPDR (!PDR_V (p,bs) | ioport_t p)
   :<!ref> bits_uint_t (8,bs)

fn {p:IOPort}{n:int}{b:bit}{r:bisectional}
  readPDRbit (!PDR_BIT_V (Pin (p,n),b,r) | pin:pin_t (p,n))
   :<!ref>bool (b==I)
*)
// PODR
(*
fn {p:IOPort}{bs,cs:bits}
  writePODR (PODR_PERMIT (p,cs),
             !PODR_V (p,bs) >> PODR_V (p,cs) |
             ioport_t p, bits_uint_t (8,cs)):void
*)

implement {bs,cs}{p}{b} changePODRBit {bn}
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

(*
fn {p:IOPort}{bs:bits}
  readPODR (PODR_V (p,bs) | ioport_t p)
   :bits_uint_t (8,bs)

fn {p:IOPort}{n:int}{b:bit}{r:bisectional}
  readPODRbit (!PODR_BIT_V (Pin (p,n),b,r) | pin:pin_t (p,n))
   :bool (b==I)
*)
// PIDR
(*
fn {p:IOPort} readPIDR (ioport_t p)
   :[bs:bits] (PIDR_P (p,bs) | bits_uint_t (8,bs))
*)
// GPIO
(*
fn readPinInput {p:IOPort}{n:int}{isel:bit}{s,r:bisectional}
   (PFS_V (Pin (p,n),Bits8 (O,isel,O,O,O,O,O,O)),
   !PMR_BIT_V (Pin (p,n),O,s),!PDR_BIT_V (Pin (p,n),O,r) | pin_t (p,n))
   : [input:bit] (PinInput (Pin (p,n),input) | bool (input==I))
*)
// レジスタ観の初期化関数には、-<lin>タグを付けて、一回だけ呼ばれることを保証する。

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

