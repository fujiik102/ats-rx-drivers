
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

fn configIOPin {pin:Pin}{rw,outv,bef_rw:bool} (pin:pin_t, rw:bool | GPIOView (id,bef_rw,outv)): (GPIOView (id,rw,outv) | void)
fn putIO {outv:bool}{bef_out:bit} (GPIOView (id,true,out) | id:Pin, bool outv): (GPIOView (id,true,outv) | void)
fn readIO {rw,outv,actualv:bool} (GPIOView (ud,rw,outv) | id:Pin): (GPIOView (id,rw,outv) | bool)

