// bit型定義は、別ファイルに分けるべき?

#define	INTMAX_HALF		1073741823
#define	UINTMAX_HALF	2147483647

datasort bit = | O | I
//sortdef bit = {b:int | 0 <= b; b <= 1} // nat2


dataprop bit_lte (bit, bit) =
 | {b:bit} it_lte_lte_refl (b, b) of ()
 | {b1,b2,b3:bit} bit_lte_tran (b1,b3) of
                  (bit_lte (b1,b2), bit_lte (b2,b3))
 | bit_lte_b1_b0 (I, O) of ()

datasort bits = BitsNil of () | BitsCons of (bit, bits)

dataprop BITSEQINT (int, bits, int) =
 | BEQNIL (0,BitsNil,0) of ()
 | {bs:bits}{n:int}{v:int | v <= INTMAX_HALF}
   BEQCONS0 (n+1,BitsCons (O, bs),v+v) of (BITSEQINT (n,bs,v))
 | {bs:bits}{n:int}{v:int | n <  INTMAX_HALF}
   BEQCONS1 (n+1,BitsCons (I, bs),v+v+1) of (BITSEQINT (n,bs,v))

dataprop BITSLEN (8,bits) =
 | BITSLENNIL (0,BitsNil) of ()
 | {n:int}{b:bit}{bs:bits}
   BITSLENCONS (n+1,BitsCons (b,bs)) of BITSLEN (n,bs)

dataprop BITEQBOOL (bit, bool) =
 | B0EQFALSE (O, false) of ()
 | B1EQTRUE  (I, true ) of ()

dataprop BITEQINT (bit, int) =
 | B0EQ0 (O, 0) of ()
 | B1EQ1 (I, 1) of ()
 
typedef bit_int_t (b:bit) = [v:int] (BITEQINT (b,v) | int v)

//stadef bit2int (b:bit): int = ifint (O == b, 0, 1)
stadef bit2bool (b:bit): bool = (I == b)
//stadef bool2bit (b:bool): bit = if b then I else O

stadef Bits8 (b7,b6,b5,b4,b3,b2,b1,b0:bit): bits =
  BitsCons (b0, BitsCons (b1, BitsCons (b2, BitsCons (b3,
  BitsCons (b4, BitsCons (b5, BitsCons (b6, BitsCons (b7,
  BitsNil))))))))

prfn bits_test1 () : BITSEQINT (0,BitsNil (),0)
prfn bits8_test2 () : BITSEQINT (8,Bits8 (O,O,O,O,O,O,O,O), 8, 0)
prfn bits8_test3 () : BITSEQINT (8,Bits8 (I,I,I,I,I,I,I,I), 8, 255)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (O,O,O,O,O,O,O,I), 8,  1)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (O,O,O,O,O,O,I,O), 8,  2)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (O,O,O,O,O,I,O,O), 8,  4)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (O,O,O,O,I,O,O,O), 8,  8)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (O,O,O,I,O,O,O,O), 8, 16)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (O,O,I,O,O,O,O,O), 8, 32)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (O,I,O,O,O,O,O,O), 8, 64)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (I,O,O,O,O,O,O,O), 8,128)

prfn bits_eq__ge_0 {bs:bits}{n,v:int}
  (BITSEQINT (n,bs,v)) : (v>=0)
prfn bitscons0_eq_double {bs:bits}{n,v:int}
  (BITSEQINT (n,bs,v)) : BITSEQINT (n+1,BitsCons (O,bs),v+v)
prfn bitscons0_eq__cons1_inc {bs:bits}{n,v:int}
  (BITSEQINT (BitsCons (O,bs),n,v)) : BITSEQINT (n,BitsCons (I,bs),v+1)

typedef bits_int_t (n:int,bs:bits) =
  [v:int] (BITSEQINT (n,bs,v) | int v)

typedef bits8int_t (b7,b6,b5,b4,b3,b2,b1,b0:bit) =
  bits_int_t (8,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0))

// TODO BITSEQINTの証明を自動で行ってくれるかどうかを確認する。
// TODO bitsのビット演算を定義する。動的なbits_t型が必要？

dataprop CHANGE_BIT_BITS (bits,int,bit,bits) =
 | {b:bit}{bs:bits} CHANGE_BIT_BITS_0 (bs,0,b,BitsCons (b,bs)) of ()
 | {b,c:bit}{bs,cs:bits}{n:int}
   CHANGE_BIT_BITS_N (BitsCons (c,bs),n+1,b,BitsCons (c,cs))
    of CHANGE_BIT_BITS (bs,n,b,cs)

fn {b:bit}{bs:bits}{n,bn:int}
  changeBitBits (bits_int_t (n,bs),int bn,bit_int_t b)
  : [bs':bits] (CHANGE_BIT_BITS (bs,bn,b,bs') | bits_int_t (n,bs'))

dataprop TEST_BIT_BITS (bits,int,bit) =
 | {b:bit}{bs:bits} WRITE_BIT_BITS_0 (BitsCons (b,bs),0,b) of ()
 | {b,c:bit}{bs:bits}{n:int}
   WRITE_BIT_BITS_N (BitsCons (c,bs),n+1,b)
    of WRITE_BIT_BITS (bs,n,b)

fn {bs:bits}{n,bn:int}
  testBitBits (bits_int_t (n,bs),int bn)
  : [b:bit | TEST_BIT_BITS (bn,bs,b)] (bool (b==I))


//
// インターフェイス
//

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
  -1))))))))))))))))))))

typedef ioport_t (p:IOPort) = int (IOPort2int p)

(*stadef bits2int (bs:bits):int = case bs of
 | BitsNil () => 0
 | BitsCons (b, bs) => bit2int (b) + bits2int (bs) * 2
*)
//sortdef Pin = {IOPort, int}
datasort Pin = Pin of (IOPort, int)
(*
dataprop PINEQINTPAIR (Pin, int, int) =
 | {p:IOPort}{n:nat | n < 8}
   PINEQ (Pin (p, n), IOPort2int (p), n) of ()
*)

typedef pin_t (p:IOPort, n:IntLt (8)) = @(ioport_t p, int n)

(*
viewdef BitsRegView (v:view, fbitview : int -> bit -> v,
                     b0:bit, b1:bit, b2:bit, b3:bit, b4:bit, b5:bit, b6:bit, b7:bit} =
            (fbitview 0 b0, fbitview 1 b1,fbitview 2 b2, fbitview 3 b3,
             fbitview 4 b4, fbitview 5 b5,fbitview 6 b6, fbitview 7 b7)
*)


// PMR

absview PMR_BIT_V (Pin, bit)

stadef PMR_BIT_IOPORT     = O
stadef PMR_BIT_PERIPHERAL = I

dataview PMR_V (IOPort,bit,bit,bit,bit,bit,bit,bit,bit) =
   {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
   PMR_V (p, b0, b1, b2, b3, b4, b5, b6, b7) of
     (PMR_BIT_V (Pin (p,0), b0), PMR_BIT_V (Pin (p,1), b1),
      PMR_BIT_V (Pin (p,2), b2), PMR_BIT_V (Pin (p,3), b3),
      PMR_BIT_V (Pin (p,4), b4), PMR_BIT_V (Pin (p,5), b5),
      PMR_BIT_V (Pin (p,6), b6), PMR_BIT_V (Pin (p,7), b7))

fn {b7,b6,b5,b4,b3,b2,b1,b0:bit}{c7,c6,c5,c4,c3,c2,c1,c0:bit}{v:int}{p:IOPort}
  writePMR (PMR_V (p,c7,c6,c5,c4,c3,c2,c1,c0) |
            ioport_t p, bits8int_t (b7,b6,b5,b4,b3,b2,b1,b0)):
           (PMR_V (p,b7,b6,b5,b4,b3,b2,b1,b0) | void)

fn {bs:bits}{p:IOPort}
  changePMRBit
   {bn:int | bn < 8}
   {bs':bits | CHANGE_BIT_BITS (bs,bn,b,bs')}
    (!PMR_V (p,bs) >> PMR_V (p,bs')
    | pin_t (p,bn),
      bit_int_t b)
      :void

fn {b7,b6,b5,b4,b3,b2,b1,b0:bit}{p:IOPort}
  readPMR (!PMR_V (p,b7,b6,b5,b4,b3,b2,b1,b0) | p:ioport_t p)
  : bits8int_t (b7,b6,b5,b4,b3,b2,b1,b0)



// PWPR

absview PWPR_V (bit,bit,bit,bit,bit,bit,bit,bit)

fn writePWPR {
    pfswe,b0wi,PFSWE,B0WI:bit
    | (pfswe==PFSWE) || (b0wi==O && B0WI==O)
  }(
    !PWPR_V (b0wi,pfswe,O,O,O,O,O,O) >>
     PWPR_V (B0WI,PFSWE,O,O,O,O,O,O) |
     bits8int_t (B0WI,PFSWE,O,O,O,O,O,O)
  ):void

fn {pfswe,b0wi:bit}
  readPFS (!PWPR_V (b0wi,pfswe,O,O,O,O,O,O))
   :bits8int_t (b0wi,pfswe,O,O,O,O,O,O)


// PFS

absview PFS_V (Pin,bit,bit,bit,bit,bit,bit,bit,bit)

(*
fn {p:IOPort}{pnum:int}
   {b0wi,asel,isel,psel4,psel3,psel2,psel1,psel0,
         ASEL,ISEL,PSEL4,PSEL3,PSEL2,PSEL1,PSEL0:bit}
  writePFS (
    !PWPR_V (O,O,O,O,O,O,I,b0wi),
    !PFS_V (Pin (p,pnum),asel,isel,O,psel4,psel3,psel2,psel1,psel0) >>
     PFS_V (Pin (p,pnum),ASEL,ISEL,O,PSEL4,PSEL3,PSEL2,PSEL1,PSEL0),
    !PMR_BIT_V (Pin (p,pnum), O)
  | pin_t (p,pnum),
    bits8int_t (ASEL,ISEL,O,PSEL4,PSEL3,PSEL2,PSEL1,PSEL0)
  ):void
*)

fn {p:IOPort}{pnum:int}
   {b0wi,asel,isel,psel4,psel3,psel2,psel1,psel0:bit}
  writePFS (
    !PWPR_V (O,O,O,O,O,O,I,b0wi),
    !PFS_V (Pin (p,pnum),asel,isel,O,psel4,psel3,psel2,psel1,psel0) >>
     PFS_V (Pin (p,pnum),O,O,O,O,O,O,O,O),
    !PMR_BIT_V (Pin (p,pnum), O)
  | pin_t (p,pnum),
    bits8int_t (O,O,O,O,O,O,O,O)
  )
  :void

fn {p:IOPort}{pnum:int}{asel,isel,psel4,psel3,psel2,psel1,psel0:bit}
  readPFS (
    !PFS_V (Pin (p,pnum),asel,isel,O,psel4,psel3,psel2,psel1,psel0)
  | pin_t (p, pnum)
  )
  :bits8int_t (asel,isel,O,psel4,psel3,psel2,psel1,psel0)

// TODO 周辺機器の重複禁止ビュー
//      最初に機器割り当て端子なしの観を発行する。
//       端子ごとの書き込み許可/禁止のpropが必要。
(*
datasort bit_permit = | BitPermBoth | BitPerm1 | BitPerm0

dataprop BITPERMITTED (bit_permit, bit) =
 | {b:bit} BITPERMBOTH (BitPermBoth,b) of ()
 | BITPERM1 (BitPerm1,I) of ()
 | BITPERM0 (BitPerm0,O) of ()

datasort bit_permits =
 | BitsPermNil of ()
 | BitsPermCons of (bit_permit, bit_permits)

dataprop BITSPERMITTED (int, bit_permits, bits) =
 | BITSPERMNIL (0, BitsPermNil, BitsNil) of ()
 | {n:int}{ps:bit_permits}{bs:bits}{p:ps:bit_permit}{b:bit}
   BITSPERMCONS (n+1,BitsPermCons (p,ps),BitsCons(b,bs)) of
     (BITPERMITTED (p,b), BITSPERMITTED (n,ps,bs))
*)
(*
dataprop TAKEBITS (int,bits,bits) =
 | {bs0:bits} TAKEBITS0 (0,bs0,BitsNil) of ()
 | {n:int}{bs0,bs1:bits}{b:bit}
   TAKEBITSN (n+1,BitsCons (b,bs0), BitsCons (b,bs1)) of TAKEBITS (n,bs0,bs1)

dataprop DROPBITS (int,bits,bits) =
 | {bs:bits} DROPBITS0 (0,bs,bs) of ()
 | {n:int}{bs0,bs1:bits}{b0,b1:bit}
   DROPBITSN (n+1,BitsCons (b0,bs0), BitsCons (b1,bs1)) of DROPBITS (n,bs0,bs1)

datasort bits_permit =
 | BitsPermitEverything of ()
 | BitsPermitLE of int
 | BitsPermitGE of int
 | BitsPermitAnd of (bits_permit, bits_permit)
 | BitsPermitOr of (bits_permit, bits_permit)

dataprop BITSPERMITTED (int, bits_permit, bits) =
 | {n,v:int}{bs:bits} BITSPERMEVERYTHING (n,BitsPermitEverything (),bs) of BITSEQINT (n,bs,v)
 | {n,s,v:int | v <= s}{bs:bits} BITSPERMLE (n,BitsPermitLE (s),bs) of BITSEQINT (n,bs,v)
 | {n,s,v:int | v >= s}{bs:bits} BITSPERMGE (n,BitsPermitLE (s),bs) of BITSEQINT (n,bs,v)
 | {n:int}{bs:bits}{p0,p1:bits_permit} BITSPERMEVAND (n,BitsPermitAnd (p0,p1),bs)
     of (BITSPERMITTED (n,p0,bs), BITSPERMITTED (n,p1,bs))
 | {n,or:int}{bs:bits}{p0,p1:bits_permit} BITSPERMEVOR (n,BitsPermitOr (p0,p1),bs)
     of por (BITSPERMITTED (n,p0,bs), BITSPERMITTED (n,p1,bs), or)

prfn BITSPERMEQ {n,s,v:int | s == v}{bs:bits} (BITSEQINT (n,bs,v)):
  BITSPERMITTED(n,BitsPermitAnd (BitsPermitLE (s),BitsPermitGE (s)) ,bs);

datasort bits_permits =
 | BitsPermitsNil of ()
 | BitsPermitsCons of (bits_permit, bits_permits)

dataprop BITPERMITTEDSS (int, bits_permits, bits) =
 | BITPERMITTEDSSNIL (0, BitsPermitsNil, BitsNil) of ()
 | {n,m:int}{ps:bits_permit}{pss:bits_permits}{bs,bsheads,bstail:bits}
   BITPERMITTEDSSCONS (n+m, BitsPermitsCons (ps,pss), bs) of
     (TAKEBITS (n,bs,bsheads), DROPBITS (n,bs,bstail),
      BITSPERMITTED (n,ps,bsheads), BITPERMITTEDSS (m,pss,bstail))
*)


// PDR

stadef PDR_BIT_WRITABLE  = I
stadef PDR_BIT_READ_ONLY = O

absview PDR_BIT_V (Pin, bit)
dataview PDR_V (IOPort,bit,bit,bit,bit,bit,bit,bit,bit) =
  {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
  PDR_V (p, b0, b1, b2, b3, b4, b5, b6, b7) of
            (PDR_BIT_V (Pin (p, 0), b0), PDR_BIT_V (Pin (p, 1), b1),
             PDR_BIT_V (Pin (p, 2), b2), PDR_BIT_V (Pin (p, 3), b3),
             PDR_BIT_V (Pin (p, 4), b4), PDR_BIT_V (Pin (p, 5), b5),
             PDR_BIT_V (Pin (p, 6), b6), PDR_BIT_V (Pin (p, 7), b7))


datasort permission = Permit | Prohibit

datasort bit_permission = BitPermission of
  (permission(*for 0*),permission(*for 1*))

dataprop BIT_PERM_PERMIT (bit_permission,bit) =
 | {p1:permission} BITPERM_0 (BitPermission (Permit,p1),O) of ()
 | {p0:permission} BITPERM_1 (BitPermission (p0,Permit),I) of ()

datasort bit_permissions = 
 | BitPermsNil of ()
 | BitPermsCons of (bit_permission,bit_permissions)

dataprop BIT_PERMS_PERMIT (int, bit_permissions, bits) =
 | BITPERMSPERM_NIL (0, BitPermsNil, BitsNil) of ()
 | {n:int}{p:bit_permission}{ps:bit_permissions}{b:bit}{bs:bits}
   BITPERMSPERM_CONS (n+1,BitPermsCons (p,ps),BitsCons (b,bs))
    of (BIT_PERM_PERMIT (p,b),BIT_PERMS_PERMIT (n,ps,bs))

//absprop PDR_PERMIT (Pin,bits_permits)
(*absprop PDR_PERMIT (Pin,
  bits_permit,bits_permit,bits_permit,bits_permit,
  bits_permit,bits_permit,bits_permit,bits_permit)*)
//praxi PDR_PERMIT ():(Pin,bits_permits)

(*propdef {p:pin}{p0,p1,p2,p3,p4,p5,p6,p7:bits_permit}
        {b7,b6,b5,b4,b3,b2,b1,b0:bit}{v:int}
  PDR_PERMIT (PDR_PERMIT (p,p0,p1,p2,p3,p4,p5,p6,p7),bit,bit,bit,bit,bit,bit,bit,bit,int) =
    (BITSPERMIT (1,p0,b0),BITSPERMIT (1,p1,b1),BITSPERMIT (1,p2,b2),BITSPERMIT (1,p3,b3),
     BITSPERMIT (1,p4,b4),BITSPERMIT (1,p5,b5),BITSPERMIT (1,p6,b6),BITSPERMIT (1,p7,b7),
     BITSEQINT (8,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),v))
*)

absprop PDR_PERMISSION (IOPort,bit_permissions)

dataprop PDR_PERMIT (IOPort,bits) =
 | {p:IOPort}{perms:bit_permissions}{bs:bits}{v:int}
   PDR_PERMIT (p,bs)
    of (PDR_PERMISSION (p,perms),BIT_PERMS_PERMIT (8,perms,bs))

fn {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0,c7,c6,c5,c4,c3,c2,c1,c0:bit}{v: int}
  writePDR (PDR_PERMIT (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)),
            !PDR_V (p,c7,c6,c5,c4,c3,c2,c1,c0) >> PDR_V (p,b7,b6,b5,b4,b3,b2,b1,b0) |
            ioport_t p, bits8int_t (b7,b6,b5,b4,b3,b2,b1,b0)):void

fn {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
  readPDR (!PDR_V (p,b7,b6,b5,b4,b3,b2,b1,b0) | ioport_t p)
  : bits8int_t (b7,b6,b5,b4,b3,b2,b1,b0)

//stadef writable2pdrbit (writable:bool) = bool2bit (writable)
stadef pdrbit2writable (b:bit) = bit2bool (b)


// PODR

stadef PODR_BIT_HIGH   = I
stadef PODR_BIT_GROUND = O

absview PODR_BIT_V (Pin, bit)
dataview PODR_V (IOPort,bit,bit,bit,bit,bit,bit,bit,bit) =
  {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
  PODR_V (p, b0, b1, b2, b3, b4, b5, b6, b7) of
            (PODR_BIT_V (Pin (p, 0), b0), PODR_BIT_V (Pin (p, 1), b1),
             PODR_BIT_V (Pin (p, 2), b2), PODR_BIT_V (Pin (p, 3), b3),
             PODR_BIT_V (Pin (p, 4), b4), PODR_BIT_V (Pin (p, 5), b5),
             PODR_BIT_V (Pin (p, 6), b6), PODR_BIT_V (Pin (p, 7), b7))

absprop PODR_PERMISSION (IOPort,bit_permissions)

dataprop PODR_PERMIT (IOPort,bits) =
 | {p:IOPort}{perms:bit_permissions}{bs:bits}{v:int}
   PODR_PERMIT (p,bs)
    of (PODR_PERMISSION (p,perms),BIT_PERMS_PERMIT (8,perms,bs))

fn {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0,c7,c6,c5,c4,c3,c2,c1,c0: bit}
  writePODR (PDR_PERMIT (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)),
             !PODR_V (p,c7,c6,c5,c4,c3,c2,c1,c0) >>
              PODR_V (p,b7,b6,b5,b4,b3,b2,b1,b0) |
             ioport_t p, bits8int_t (b7,b6,b5,b4,b3,b2,b1,b0)):void

fn {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0: bit}
  readPODR (PODR_V (p,b7,b6,b5,b4,b3,b2,b1,b0) | ioport_t p)
   :bits8int_t (b7,b6,b5,b4,b3,b2,b1,b0)


// GPIO

viewdef GPIOView (p:Pin)(writable:bit)(out:bit) =
  (PMR_BIT_V (p, O), PDR_BIT_V (p, writable), PODR_BIT_V (p, out)

// TODO 出力電圧やオープンドレインなどの設定を表す観を作る。

fn getInitialPinViews (IOPortNotGetInitialView) :
    (GPIOView (Port0, 0) false false, GPIOView (Port0, 1),
     GPIOView (Port1, 0) false false, GPIOView (Port1, 1) | void)

fn configIOPin {rw outv:bool} (id:Pin, rw:bool | GPIOView id _ outv): (GPIOView id rw outv | void)
fn putIO {outv:bool} (GPIOView id true _ | id:Pin, bool outv): (GPIOView id true outv | void)
fn readIO {rw outv actualv:bool} (GPIOView ud rw outv | id:Pin): (GPIOView id rw outv | bool)

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


