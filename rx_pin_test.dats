

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
staload "Pin.dats"
//
  (* ****** ****** *)

//
// please write you program in this section
//

(* ****** ****** *)


datasort output_duration = output_duration of (bit,int)

datasort output_history =
 | output_hist_nil of ()
 | output_hist_cons of (output_history,output_duration)

absview OutputDurationView (Pin,output_duration)

dataview OutputHistoryView (Pin,output_history) =
 | {p:Pin}{d:output_duration}{hist:output_history}
   OutputHistCons (p,output_hist_cons (hist,d))
   of (OutputDurationView (p,d),OutputHistoryView (p,hist))

extern fn {p:Pin} newOutputHistoryView ():<> //<lin>
  (OutputHistoryView (p,output_hist_nil) | void)


extern fun wait_impl (term_millisec:uint): void = "ext#"

extern fn {pin:Pin}{b:bit}{hist:output_history}{t:int}
   wait (!PinOutputView (pin,b),
         !OutputHistoryView (pin,hist) >>
          OutputHistoryView (pin,output_hist_cons (hist,output_duration (b,t)))
        | term_millisec:uint t)
        : void

implement {pin}{b}{hist}{t}
   wait (output_v,hist_v | term_millisec)
 = let
   val+ () = wait_impl (term_millisec)
   prval () = $UN.castview2void (hist_v)
 in end

extern praxi {p:Pin} consumeOutputHistory // <lin>
       (OutputHistoryView (p,
        output_hist_cons (
        output_hist_cons (
        output_hist_cons (
        output_hist_cons (output_hist_nil,
        output_duration (I,500)),
        output_duration (O,250)),
        output_duration (I,400)),
        output_duration (O,0)))): void


prfn pow2_8__256 (): POW2 (8,256) =
  POW2_N (POW2_N (POW2_N (POW2_N (POW2_N (POW2_N (POW2_N (POW2_N POW2_0)))))))

prfn make_eqint_bits {n:nat | n < 256} (v:uint n): [bs:bits] BITSEQINT (8,bs,n) = let
    prval pow256 = pow2_8__256 ()
    prval () = pow2_lte {8,256}(pow256)
  in nat_eq_bits {8,256,n}(pow256) end

prfn bs_eq_even__bcons0 {n,v:int | (v%2) == 0 && 0 < n}{bs:bits}
     (bseqint:BITSEQINT (n,bs,v))
     : [bs':bits | bs == BitsCons (bs',O)] BITSEQINT (n-1,bs',v/2)
 = case+ bseqint of
   | BEQNIL () =/=> ()
   | BEQCONS (bs'eqint,B1EQ1 ()) =/=> ()
   | BEQCONS (bs'eqint,B0EQ0 ()) => let
       prval () = bits_eq_refl {bs}()
     in bs'eqint end

prfn {bs8:bits} bs8eq0__eq_bs8_all0 (bs8eq0:BITSEQINT (8,bs8,0)):
      [bs8 == BitsCons (BitsCons (BitsCons (BitsCons (
              BitsCons (BitsCons (BitsCons (BitsCons(BitsNil,
              O),O),O),O),O),O),O),O)] void
 = let
     prval EQINT () = eqint_make {0,0/2/2}()
     prval EQINT () = eqint_make {0,0/2/2/2/2}()
     prval EQINT () = eqint_make {0,0/2/2/2/2/2/2}()
     prval [bs7:bits] bs7eq0 = bs_eq_even__bcons0 (bs8eq0)
     prval [bs6:bits] bs6eq0 = bs_eq_even__bcons0 (bs7eq0)
     prval [bs5:bits] bs5eq0 = bs_eq_even__bcons0 (bs6eq0)
     prval [bs4:bits] bs4eq0 = bs_eq_even__bcons0 (bs5eq0)
     prval [bs3:bits] bs3eq0 = bs_eq_even__bcons0 (bs4eq0)
     prval [bs2:bits] bs2eq0 = bs_eq_even__bcons0 (bs3eq0)
     prval [bs1:bits] bs1eq0 = bs_eq_even__bcons0 (bs2eq0)
     prval [bs0:bits] bs0eq0 = bs_eq_even__bcons0 (bs1eq0)
     prval EQBITS () = eqbits_make {bs8,BitsCons (bs7,O)}()
     prval EQBITS () = eqbits_make {bs7,BitsCons (bs6,O)}()
     prval EQBITS () = eqbits_make {bs6,BitsCons (bs5,O)}()
     prval EQBITS () = eqbits_make {bs5,BitsCons (bs4,O)}()
     prval EQBITS () = eqbits_make {bs4,BitsCons (bs3,O)}()
     prval EQBITS () = eqbits_make {bs3,BitsCons (bs2,O)}()
     prval EQBITS () = eqbits_make {bs2,BitsCons (bs1,O)}()
     prval EQBITS () = eqbits_make {bs1,BitsCons (bs0,O)}()
   in case+ bs0eq0 of
      | BEQCONS {nm1}{_}{_}{_,_}(bsm1eq,_) =/=> let
          prval EQINT () = eqint_make {~1,nm1}()
        in bseqint_len_is_nat bsm1eq end
      | BEQNIL () => bits_eq_refl {bs8}()
   end


implement main0 () = let
    prval (pmr0,pmr1,pmr2,pmr3,pmr4,pmr5,pmrA,pmrB,pmrC,pmrE,pmrH,pmrJ,
          pmr0perm,pmr1perm,pmr2perm,pmr3perm,pmr4perm,pmr5perm,
          pmrAperm,pmrBperm,pmrCperm,pmrEperm,pmrHperm,pmrJperm)
         = rx110_initial_pmr_views ()
    prval (pfs00,pfs01,pfs02,pfs03,pfs04,pfs05,pfs06,pfs07,
          pfs10,pfs11,pfs12,pfs13,pfs14,pfs15,pfs16,pfs17,
          pfs20,pfs21,pfs22,pfs23,pfs24,pfs25,pfs26,pfs27,
          pfs30,pfs31,pfs32,pfs33,pfs34,pfs35,pfs36,pfs37,
          pfs40,pfs41,pfs42,pfs43,pfs44,pfs45,pfs46,pfs47,
          pfs50,pfs51,pfs52,pfs53,pfs54,pfs55,pfs56,pfs57,
          pfsA0,pfsA1,pfsA2,pfsA3,pfsA4,pfsA5,pfsA6,pfsA7,
          pfsB0,pfsB1,pfsB2,pfsB3,pfsB4,pfsB5,pfsB6,pfsB7,
          pfsC0,pfsC1,pfsC2,pfsC3,pfsC4,pfsC5,pfsC6,pfsC7,
          pfsE0,pfsE1,pfsE2,pfsE3,pfsE4,pfsE5,pfsE6,pfsE7,
          pfsH0,pfsH1,pfsH2,pfsH3,pfsH4,pfsH5,pfsH6,pfsH7,
          pfsJ0,pfsJ1,pfsJ2,pfsJ3,pfsJ4,pfsJ5,pfsJ6,pfsJ7)
         = rx110_initial_pfs_views ()
    prval (pdr0,pdr1,pdr2,pdr3,pdr4,pdr5,pdrA,pdrB,pdrC,pdrE,pdrH,pdrJ,
          pdr0perm,pdr1perm,pdr2perm,pdr3perm,pdr4perm,pdr5perm,
          pdrAperm,pdrBperm,pdrCperm,pdrEperm,pdrHperm,pdrJperm)
         = rx110_initial_pdr_views ()
    prval (podr0,podr1,podr2,podr3,podr4,podr5,
           podrA,podrB,podrC,podrE,podrH,podrJ,
          podr0perm,podr1perm,podr2perm,podr3perm,podr4perm,podr5perm,
          podrAperm,podrBperm,podrCperm,podrEperm,podrHperm,podrJperm)
         = rx110_initial_podr_views ()

    prval () = ioport_eq_int ()

    prval bint01 = BEQCONS (BEQCONS (BEQCONS (BEQCONS (
          BEQCONS (BEQCONS (BEQCONS (BEQCONS (BEQNIL (),
          B0EQ0 ()),B0EQ0 ()),B0EQ0 ()),B0EQ0 ()),
          B0EQ0 ()),B0EQ0 ()),B0EQ0 ()),B1EQ1 ()) //= bint01
    val+ beqint01 = (bint01 | i2u 0x01)
    prval podr_cert01 = bitspermcert_test_all (bitseqint__bitslen bint01)

    prval bint00 = BEQCONS (BEQCONS (BEQCONS (BEQCONS (
          BEQCONS (BEQCONS (BEQCONS (BEQCONS (BEQNIL (),
          B0EQ0 ()),B0EQ0 ()),B0EQ0 ()),B0EQ0 ()),
          B0EQ0 ()),B0EQ0 ()),B0EQ0 ()),B0EQ0 ())
    val+ beqint00 = (bint00 | i2u 0x00)
    prval podr_cert00 = bitspermcert_test_all (bitseqint__bitslen bint00)

    prval pdr_perm = (pdr0perm,bitspermcert_test_all (bitseqint__bitslen bint01))
    val+ () = writePDR (pdr0,pdr_perm | 0,beqint01)
    prval (pdr0perm,_) = pdr_perm
    //val+ () = changePDRBit (chgbit,pdr0,pdr0perm | (Port0,0),1)

    prval PMR_V (pmr07,pmr06,pmr05,pmr04,pmr03,pmr02,pmr01,pmr00) = pmr0
    prval PDR_V (pdr07,pdr06,pdr05,pdr04,pdr03,pdr02,pdr01,pdr00) = pdr0

    prval (hist | ()) = newOutputHistoryView ()

    prval podr_permit = (podr0perm,podr_cert01)
    val+ () = writePODR (podr0,podr_permit | 0,beqint01)
    prval (podr0perm,_) = podr_permit
    prval PODR_V (podr07,podr06,podr05,podr04,podr03,podr02,podr01,podr00) = podr0
    prval outview = (pfs00,pmr00,pdr00,podr00)
    val+ () = wait (outview,hist | i2u 500)
    prval (pfs00,pmr00,pdr00,podr00) = outview
    prval podr0 = PODR_V (podr07,podr06,podr05,podr04,podr03,podr02,podr01,podr00)

    prval podr_permit = (podr0perm,podr_cert00)
    val+ () = writePODR (podr0,podr_permit | 0,beqint00)
    prval (podr0perm,_) = podr_permit
    prval PODR_V (podr07,podr06,podr05,podr04,podr03,podr02,podr01,podr00) = podr0
    prval outview = (pfs00,pmr00,pdr00,podr00)
    val+ () = wait (outview,hist | i2u 250)
    prval (pfs00,pmr00,pdr00,podr00) = outview
    prval podr0 = PODR_V (podr07,podr06,podr05,podr04,podr03,podr02,podr01,podr00)

    prval podr_permit = (podr0perm,podr_cert01)
    val+ () = writePODR (podr0,podr_permit | 0,beqint01)
    prval (podr0perm,_) = podr_permit
    prval PODR_V (podr07,podr06,podr05,podr04,podr03,podr02,podr01,podr00) = podr0
    prval outview = (pfs00,pmr00,pdr00,podr00)
    val+ () = wait (outview,hist | i2u 400)
    prval (pfs00,pmr00,pdr00,podr00) = outview
    prval podr0 = PODR_V (podr07,podr06,podr05,podr04,podr03,podr02,podr01,podr00)

    prval podr_permit = (podr0perm,podr_cert00)
    val+ () = writePODR (podr0,podr_permit | 0,beqint00)
    prval (podr0perm,_) = podr_permit
    prval PODR_V (podr07,podr06,podr05,podr04,podr03,podr02,podr01,podr00) = podr0
    prval outview = (pfs00,pmr00,pdr00,podr00)
    val+ () = wait (outview,hist | i2u 0)
    prval (pfs00,pmr00,pdr00,podr00) = outview
    prval podr0 = PODR_V (podr07,podr06,podr05,podr04,podr03,podr02,podr01,podr00)

    prval () = consumeOutputHistory (hist)

    prval pdr0 = PDR_V (pdr07,pdr06,pdr05,pdr04,pdr03,pdr02,pdr01,pdr00)
    prval pmr0 = PMR_V (pmr07,pmr06,pmr05,pmr04,pmr03,pmr02,pmr01,pmr00)

    prval [bs00:bits] bint00 = make_eqint_bits (i2u 0x00)
    val+ bint00_val = (bint00 | i2u 0x00)

    prval podr_cert = bitspermcert_test_all (bitseqint__bitslen bint00)
    prval podr_permit = (podr0perm,podr_cert)
    val+ () = writePODR (podr0,podr_permit | 0,bint00_val)
    prval (podr0perm,_) = podr_permit
    
    prval pdr_perm = (pdr0perm,bitspermcert_test_all (bitseqint__bitslen bint00))
    val+ () = writePDR (pdr0,pdr_perm | 0,bint00_val)
    prval (pdr0perm,_) = pdr_perm
    
    prval () = bs8eq0__eq_bs8_all0 (bint00)
    prval  EQBITS () = eqbits_make {bs00,Bits8_all0}()
    
    prval () = rx110_consume_pmr_views (
                 pmr0,pmr1,pmr2,pmr3,pmr4,pmr5,pmrA,pmrB,pmrC,pmrE,pmrH,pmrJ,
                 pmr0perm,pmr1perm,pmr2perm,pmr3perm,pmr4perm,pmr5perm,
                 pmrAperm,pmrBperm,pmrCperm,pmrEperm,pmrHperm,pmrJperm)
    prval () = rx110_consume_pfs_views (
                 pfs00,pfs01,pfs02,pfs03,pfs04,pfs05,pfs06,pfs07,
                 pfs10,pfs11,pfs12,pfs13,pfs14,pfs15,pfs16,pfs17,
                 pfs20,pfs21,pfs22,pfs23,pfs24,pfs25,pfs26,pfs27,
                 pfs30,pfs31,pfs32,pfs33,pfs34,pfs35,pfs36,pfs37,
                 pfs40,pfs41,pfs42,pfs43,pfs44,pfs45,pfs46,pfs47,
                 pfs50,pfs51,pfs52,pfs53,pfs54,pfs55,pfs56,pfs57,
                 pfsA0,pfsA1,pfsA2,pfsA3,pfsA4,pfsA5,pfsA6,pfsA7,
                 pfsB0,pfsB1,pfsB2,pfsB3,pfsB4,pfsB5,pfsB6,pfsB7,
                 pfsC0,pfsC1,pfsC2,pfsC3,pfsC4,pfsC5,pfsC6,pfsC7,
                 pfsE0,pfsE1,pfsE2,pfsE3,pfsE4,pfsE5,pfsE6,pfsE7,
                 pfsH0,pfsH1,pfsH2,pfsH3,pfsH4,pfsH5,pfsH6,pfsH7,
                 pfsJ0,pfsJ1,pfsJ2,pfsJ3,pfsJ4,pfsJ5,pfsJ6,pfsJ7)
    
    prval () = rx110_consume_pdr_views (
                 pdr0,pdr1,pdr2,pdr3,pdr4,pdr5,pdrA,pdrB,pdrC,pdrE,pdrH,pdrJ,
                 pdr0perm,pdr1perm,pdr2perm,pdr3perm,pdr4perm,pdr5perm,
                 pdrAperm,pdrBperm,pdrCperm,pdrEperm,pdrHperm,pdrJperm)
    prval () = rx110_consume_podr_views (
                 podr0,podr1,podr2,podr3,podr4,podr5,
                 podrA,podrB,podrC,podrE,podrH,podrJ,
                 podr0perm,podr1perm,podr2perm,podr3perm,podr4perm,podr5perm,
                 podrAperm,podrBperm,podrCperm,podrEperm,podrHperm,podrJperm)
  in end
