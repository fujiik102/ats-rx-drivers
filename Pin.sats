// 端子制御ドライバ定義

staload "Bit.sats"

datasort IOPort =
 | Port0 of () | Port1 of () | Port2 of () | Port3 of ()
 | Port4 of () | Port5 of () | Port6 of () | Port7 of ()
 | Port8 of () | Port9 of () | PortA of () | PortB of ()
 | PortC of () | PortD of () | PortE of () | PortF of ()
 | PortG of () | PortH of () | PortI of () | PortJ of ()

stadef IOPort2int (p:IOPort):int =
  ifint (p==Port0, 0, ifint (p==Port1, 1,
  ifint (p==Port2, 2, ifint (p==Port3, 3,
  ifint (p==Port4, 4, ifint (p==Port5, 5,
  ifint (p==Port6, 6, ifint (p==Port7, 7,
  ifint (p==Port8, 8, ifint (p==Port9, 9,
  ifint (p==PortA,10, ifint (p==PortB,11,
  ifint (p==PortC,12, ifint (p==PortD,13,
  ifint (p==PortE,14, ifint (p==PortF,15,
  ifint (p==PortG,16, ifint (p==PortH,17,
  ifint (p==PortI,18, ifint (p==PortJ,19,
  ~1))))))))))))))))))))

typedef ioport_t (p:IOPort) = int (IOPort2int p)

datasort Pin = Pin of (IOPort, int)

typedef pin_t (p:IOPort, n:int) = @(ioport_t p, int n)


// PMR

absview PMR_BIT_V (Pin, bit)

stadef PMR_BIT_IOPORT     = O
stadef PMR_BIT_PERIPHERAL = I

dataview PMR_V (IOPort,bits) =
   {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
   PMR_V (p, Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) of
     (PMR_BIT_V (Pin (p,0), b0), PMR_BIT_V (Pin (p,1), b1),
      PMR_BIT_V (Pin (p,2), b2), PMR_BIT_V (Pin (p,3), b3),
      PMR_BIT_V (Pin (p,4), b4), PMR_BIT_V (Pin (p,5), b5),
      PMR_BIT_V (Pin (p,6), b6), PMR_BIT_V (Pin (p,7), b7))

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

// PFS関数は延期。PFS_Vのみ定義して、初期値の状態のみ取得できるようにする。
(*
// PWPR

absview PWPR_V (bits)

fn writePWPR {
    pfswe,b0wi,PFSWE,B0WI:bit
    | (pfswe==PFSWE) || (b0wi==O && B0WI==O)
  }(
    !PWPR_V (Bits8 (b0wi,pfswe,O,O,O,O,O,O)) >>
     PWPR_V (Bits8 (B0WI,PFSWE,O,O,O,O,O,O)) |
     bits8int_t (B0WI,PFSWE,O,O,O,O,O,O)
  ):void

fn {pfswe,b0wi:bit}
  readPWPR (!PWPR_V (Bits8 (b0wi,pfswe,O,O,O,O,O,O)))
   :bits8int_t (b0wi,pfswe,O,O,O,O,O,O)
*)

// PFS

absview PFS_V (Pin,bits)
(*
fn {p:IOPort}{pnum:int}
   {b0wi,asel,isel,psel4,psel3,psel2,psel1,psel0:bit}
  writePFS (
    !PWPR_V (Bits8 (O,O,O,O,O,O,I,b0wi)),
    !PFS_V (Pin (p,pnum),Bits8 (asel,isel,O,psel4,psel3,psel2,psel1,psel0)) >>
     PFS_V (Pin (p,pnum),Bits8 (O,O,O,O,O,O,O,O)),
    !PMR_BIT_V (Pin (p,pnum), O)
  | pin_t (p,pnum),
    bits8int_t (O,O,O,O,O,O,O,O)
  )
  :void

fn {p:IOPort}{pnum:int}{asel,isel,psel4,psel3,psel2,psel1,psel0:bit}
  readPFS (
    !PFS_V (Pin (p,pnum),Bits8 (asel,isel,O,psel4,psel3,psel2,psel1,psel0))
  | pin_t (p, pnum)
  )
  :bits8int_t (asel,isel,O,psel4,psel3,psel2,psel1,psel0)
*)

// TODO 周辺機器の重複禁止ビュー
//      最初に機器割り当て端子なしの観を発行する。
//       端子ごとの書き込み許可/禁止のpropが必要。


// PDR

stadef PDR_BIT_WRITABLE  = I
stadef PDR_BIT_READ_ONLY = O

absview PDR_BIT_V (Pin, bit)
dataview PDR_V (IOPort,bits) =
  {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
  PDR_V (p, Bits8 (b0,b1,b2,b3,b4,b5,b6,b7)) of
            (PDR_BIT_V (Pin (p,0),b0), PDR_BIT_V (Pin (p,1),b1),
             PDR_BIT_V (Pin (p,2),b2), PDR_BIT_V (Pin (p,3),b3),
             PDR_BIT_V (Pin (p,4),b4), PDR_BIT_V (Pin (p,5),b5),
             PDR_BIT_V (Pin (p,6),b6), PDR_BIT_V (Pin (p,7),b7))

absprop PDR_PERMISSION (IOPort,bit_permissions)

dataprop PDR_PERMIT (IOPort,bits) =
 | {p:IOPort}{perms:bit_permissions}{bs:bits}{v:int}
   PDR_PERMIT (p,bs)
    of (PDR_PERMISSION (p,perms),BIT_PERMS_PERMIT (8,perms,bs))

fn {p:IOPort}{bs,cs:bits}{v: int}
  writePDR (PDR_PERMIT (p,cs),
            !PDR_V (p,bs) >> PDR_V (p,cs) |
            ioport_t p,bits_int_t (8,cs)):void

fn {p:IOPort}{bs:bits}
  readPDR (!PDR_V (p,bs) | ioport_t p)
   : bits_int_t (8,bs)


// PODR

stadef PODR_BIT_HIGH   = I
stadef PODR_BIT_GROUND = O

absview PODR_BIT_V (Pin,bit)
dataview PODR_V (IOPort,bits) =
  {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
  PODR_V (p,Bits8 (b0,b1,b2,b3,b4,b5,b6,b7)) of
            (PODR_BIT_V (Pin (p,0),b0), PODR_BIT_V (Pin (p,1),b1),
             PODR_BIT_V (Pin (p,2),b2), PODR_BIT_V (Pin (p,3),b3),
             PODR_BIT_V (Pin (p,4),b4), PODR_BIT_V (Pin (p,5),b5),
             PODR_BIT_V (Pin (p,6),b6), PODR_BIT_V (Pin (p,7),b7))

absprop PODR_PERMISSION (IOPort,bit_permissions)

dataprop PODR_PERMIT (IOPort,bits) =
 | {p:IOPort}{perms:bit_permissions}{bs:bits}{v:int}
   PODR_PERMIT (p,bs)
    of (PODR_PERMISSION (p,perms),BIT_PERMS_PERMIT (8,perms,bs))

fn {p:IOPort}{bs,cs:bits}
  writePODR (PODR_PERMIT (p,cs),
             !PODR_V (p,bs) >> PODR_V (p,cs) |
             ioport_t p, bits_int_t (8,cs)):void

fn {p:IOPort}{bs:bits}
  readPODR (PODR_V (p,bs) | ioport_t p)
   :bits_int_t (8,bs)

////

// GPIO

viewdef GPIOView (p:Pin)(writable:bit)(out:bit) =
  (PMR_BIT_V (p, O), PDR_BIT_V (p, writable), PODR_BIT_V (p, out))

// TODO 出力電圧やオープンドレインなどの設定を表す観を作る。

fn getInitialPinViews (IOPortNotGetInitialView) :
    (GPIOView (Port0, 0) false false, GPIOView (Port0, 1),
     GPIOView (Port1, 0) false false, GPIOView (Port1, 1) | void)

fn configIOPin {pin:Pin}{rw,outv,bef_rw:bool} (pin:pin_t, rw:bool | GPIOView (id,bef_rw,outv)): (GPIOView (id,rw,outv) | void)
fn putIO {outv:bool}{bef_out:bit} (GPIOView (id,true,out) | id:Pin, bool outv): (GPIOView (id,true,outv) | void)
fn readIO {rw,outv,actualv:bool} (GPIOView (ud,rw,outv) | id:Pin): (GPIOView (id,rw,outv) | bool)

(*
 起動からの出力履歴を型に含ませる。
  後から含ませることはできる？
   別のスタンプ化した型を作って、関係する関数に型を追加すれば良い？
    それでも手間が多い？
     すべてのPinViewに追加するよりはマシ？
   追加するには、起動からの時間を管理する仕組みが必要
    取り敢えず面倒くさいから諦める。
  周辺機器に設定すると履歴が取れなくなる？
   周辺機器に設定したことを履歴に残しておけば良い。
*)

// TODO パッケージ毎の差異に対応するための初期absprop

//
// 実装
//


