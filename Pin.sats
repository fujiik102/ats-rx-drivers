
// Pin control drivers

staload "Bit.sats"

// Target MCU
#define MCU_RX110
#define MCU_Package_Pins 64


datasort IOPort =
 | Port0 of () | Port1 of () | Port2 of () | Port3 of ()
 | Port4 of () | Port5 of () | Port6 of () | Port7 of ()
 | Port8 of () | Port9 of () | PortA of () | PortB of ()
 | PortC of () | PortD of () | PortE of () | PortF of ()
 | PortG of () | PortH of () | PortI of () | PortJ of ()

stacst IOPort2int (p:IOPort):int
praxi ioport_eq_int ():[
    IOPort2int Port0 == 0 && IOPort2int Port1 == 1 &&
    IOPort2int Port2 == 2 && IOPort2int Port3 == 3 &&
    IOPort2int Port4 == 4 && IOPort2int Port5 == 5 &&
    IOPort2int Port6 == 6 && IOPort2int Port7 == 7 &&
    IOPort2int Port8 == 8 && IOPort2int Port9 == 9 &&
    IOPort2int PortA == 10 && IOPort2int PortB == 11 &&
    IOPort2int PortC == 12 && IOPort2int PortD == 13 &&
    IOPort2int PortE == 14 && IOPort2int PortF == 15 &&
    IOPort2int PortG == 16 && IOPort2int PortH == 17 &&
    IOPort2int PortI == 18 && IOPort2int PortJ == 19
  ] void

typedef ioport_t (p:IOPort) = int (IOPort2int p)

datasort Pin = Pin of (IOPort,int)

typedef pin_t (p:IOPort,n:int) = @(ioport_t p, uint n)


stadef P0 (n:int):Pin = Pin (Port0,n)
stadef P1 (n:int):Pin = Pin (Port1,n)
stadef P2 (n:int):Pin = Pin (Port2,n)
stadef P3 (n:int):Pin = Pin (Port3,n)
stadef P4 (n:int):Pin = Pin (Port4,n)
stadef P5 (n:int):Pin = Pin (Port5,n)
stadef P6 (n:int):Pin = Pin (Port6,n)
stadef P7 (n:int):Pin = Pin (Port7,n)
stadef P8 (n:int):Pin = Pin (Port8,n)
stadef P9 (n:int):Pin = Pin (Port9,n)
stadef PA (n:int):Pin = Pin (PortA,n)
stadef PB (n:int):Pin = Pin (PortB,n)
stadef PC (n:int):Pin = Pin (PortC,n)
stadef PD (n:int):Pin = Pin (PortD,n)
stadef PE (n:int):Pin = Pin (PortE,n)
stadef PF (n:int):Pin = Pin (PortF,n)
stadef PG (n:int):Pin = Pin (PortG,n)
stadef PH (n:int):Pin = Pin (PortH,n)
stadef PI (n:int):Pin = Pin (PortI,n)
stadef PJ (n:int):Pin = Pin (PortJ,n)


// Special form of fractional (n/2^m only)
datasort bisectional = bisectional of (int,int)

stadef bisect1 = bisectional (1,0)

dataprop EQBISECTIONAL (bisectional, bisectional) = {r:bisectional} EQBISECTIONAL (r, r)
praxi eqbisectional_make {r,s:bisectional | r == s} () : EQBISECTIONAL (r,s)
praxi bisectional_eq_refl {r:bisectional} () : [r == r] void
praxi bisectional_eq_reduce {n,m:int | n <= INTMAX_HALF} ():
      [bisectional (n,m) == bisectional (n+n,m+1)] void

stacst bisectional_add_b : (bisectional,bisectional,bisectional) -> bool

praxi {n1,n2,m:int} bisectional_add_axi ():
      [bisectional_add_b (bisectional (n1,m),bisectional (n2,m),bisectional (n1+n2,m))] unit_p

praxi bisectional_add_axi_rev
 {n1,n2,n3,m:int | bisectional_add_b (bisectional (n1,m),bisectional (n2,m),bisectional (n3,m))}(): [n1+n2==n3] unit_p


stacst bisectional_half_b : (bisectional,bisectional) -> bool

praxi {n,m:int} bisectional_half_axi ():
      [bisectional_half_b (bisectional (n,m),bisectional (n,m+1))] unit_p

praxi {n,m,l:int} bisectional_half_axi_rev {bisectional_half_b (bisectional (n,m),bisectional (n,l))}(): [m+1==l] unit_p

// PMR

absview PMR_BIT_V (Pin,bit,bisectional)

praxi {p:Pin}{b:bit} divide_pmr_bit_v {r,s:bisectional | bisectional_half_b (r,s)}
      (PMR_BIT_V (p,b,r)) : (PMR_BIT_V (p,b,s),PMR_BIT_V (p,b,s))

praxi {p:Pin}{b:bit} merge_pmr_bit_v {r,s,t:bisectional | bisectional_add_b (r,s,t)}
      (PMR_BIT_V (p,b,r), PMR_BIT_V (p,b,s)):(PMR_BIT_V (p,b,t))


stadef PMR_BIT_IOPORT     = O
stadef PMR_BIT_PERIPHERAL = I

dataview PMR_V (IOPort,bits) =
    {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
    PMR_V (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) of
      (PMR_BIT_V (Pin (p,7),b7,bisect1), PMR_BIT_V (Pin (p,6),b6,bisect1),
       PMR_BIT_V (Pin (p,5),b5,bisect1), PMR_BIT_V (Pin (p,4),b4,bisect1),
       PMR_BIT_V (Pin (p,3),b3,bisect1), PMR_BIT_V (Pin (p,2),b2,bisect1),
       PMR_BIT_V (Pin (p,1),b1,bisect1), PMR_BIT_V (Pin (p,0),b0,bisect1))

absview PMR_PERMISSION (IOPort,bit_permissions)

viewdef PMR_PERMIT (p:IOPort,bs:bits) =
    [perms:bit_permissions]
    (PMR_PERMISSION (p,perms),BITS_PERMIT_CERTIFICATE (8,perms,bs))

fn {p:IOPort}{bs,cs:bits}
  writePMR (!PMR_V (p,bs) >> PMR_V (p,cs),
            !PMR_PERMIT (p,cs)
           | ioport_t p,bits_uint_t (8,cs))
   :<!wrt> void

fn {p:IOPort}{bs,cs:bits}{b:bit}
  changePMRBit {bn:int | bn < 8}
    (CHANGE_BIT_BITS (8,bs,bn,b,cs),
     !PMR_V (p,bs) >> PMR_V (p,cs),
     !PMR_PERMIT (p,cs)
    | pin_t (p,bn), bit_uint_t b):<!refwrt> void

fn {p:IOPort}{bs:bits}
  readPMR (!PMR_V (p,bs) | p:ioport_t p)
   :<!ref> bits_uint_t (8,bs)

fn pmr2pmr_bits {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}{v:int}
   (PMR_V (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) | bits_uint_t (8,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)))
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
    | @(bool (b7 == I),bool (b6 == I),bool (b5 == I),bool (b4 == I),
        bool (b3 == I),bool (b2 == I),bool (b1 == I),bool (b0 == I)))


// The PFS function is postponed.
// Define only PFS_V so that other functions can acquire the state of the initial value
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

// TODO Create duplicate prohibited view of peripheral devices.
//      Issues view with no device assignment pins first.
//       Propriety of writing / disabling per pins is required.


// PDR

stadef PDR_BIT_WRITABLE  = I
stadef PDR_BIT_READ_ONLY = O

absview PDR_BIT_V (Pin,bit,bisectional)

praxi {p:Pin}{b:bit} divide_pdr_bit_v {r,s:bisectional | bisectional_half_b (r,s)}
      (PDR_BIT_V (p,b,r)) : (PDR_BIT_V (p,b,s),PDR_BIT_V (p,b,s))

praxi {p:Pin}{b:bit} merge_pdr_bit_v {r,s,t:bisectional | bisectional_add_b (r,s,t)}
      (PDR_BIT_V (p,b,r), PDR_BIT_V (p,b,s)):(PDR_BIT_V (p,b,t))


dataview PDR_V (p:IOPort,bits) =
    {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
    PDR_V (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) of
      (PDR_BIT_V (Pin (p,7),b7,bisect1), PDR_BIT_V (Pin (p,6),b6,bisect1),
       PDR_BIT_V (Pin (p,5),b5,bisect1), PDR_BIT_V (Pin (p,4),b4,bisect1),
       PDR_BIT_V (Pin (p,3),b3,bisect1), PDR_BIT_V (Pin (p,2),b2,bisect1),
       PDR_BIT_V (Pin (p,1),b1,bisect1), PDR_BIT_V (Pin (p,0),b0,bisect1))

absview PDR_PERMISSION (IOPort,bit_permissions)

viewdef PDR_PERMIT (p:IOPort,bs:bits) =
    [perms:bit_permissions]
    (PDR_PERMISSION (p,perms),BITS_PERMIT_CERTIFICATE (8,perms,bs))

fn {p:IOPort}{bs,cs:bits}
  writePDR (!PDR_V (p,bs) >> PDR_V (p,cs),
            !PDR_PERMIT (p,cs)
           | ioport_t p,bits_uint_t (8,cs)):<!wrt> void

fn {p:IOPort}{bs,cs:bits}{b:bit}
  changePDRBit {bn:int | bn < 8}
    (CHANGE_BIT_BITS (8,bs,bn,b,cs),
     !PDR_V (p,bs) >> PDR_V (p,cs),
     !PDR_PERMIT (p,cs)
    | pin_t (p,bn), bit_uint_t b):<!refwrt> void

fn {p:IOPort}{bs:bits}
  readPDR (!PDR_V (p,bs) | ioport_t p)
   :<!ref> bits_uint_t (8,bs)

fn pdr2pdr_bits {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}{v:int}
   (PDR_V (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) | bits_uint_t (8,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)))
   :(PDR_BIT_V (Pin (p,7),b7,bisect1),
     PDR_BIT_V (Pin (p,6),b6,bisect1),
     PDR_BIT_V (Pin (p,5),b5,bisect1),
     PDR_BIT_V (Pin (p,4),b4,bisect1),
     PDR_BIT_V (Pin (p,3),b3,bisect1),
     PDR_BIT_V (Pin (p,2),b2,bisect1),
     PDR_BIT_V (Pin (p,1),b1,bisect1),
     PDR_BIT_V (Pin (p,0),b0,bisect1),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),0,b0),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),1,b1),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),2,b2),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),3,b3),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),4,b4),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),5,b5),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),6,b6),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),7,b7)
    | @(bool (b7 == I),bool (b6 == I),bool (b5 == I),bool (b4 == I),
        bool (b3 == I),bool (b2 == I),bool (b1 == I),bool (b0 == I)))


// PODR

stadef PODR_BIT_HIGH   = I
stadef PODR_BIT_GROUND = O

absview PODR_BIT_V (Pin,bit,bisectional)

praxi {p:Pin}{b:bit} divide_podr_bit_v {r,s:bisectional | bisectional_half_b (r,s)}
      (PODR_BIT_V (p,b,r)) : (PODR_BIT_V (p,b,s),PODR_BIT_V (p,b,s))

praxi {p:Pin}{b:bit} merge_podr_bit_v {r,s,t:bisectional | bisectional_add_b (r,s,t)}
    (PODR_BIT_V (p,b,r), PODR_BIT_V (p,b,s)):(PODR_BIT_V (p,b,t))


dataview PODR_V (p:IOPort,bits) =
    {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
    PODR_V (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) of
      (PODR_BIT_V (Pin (p,7),b7,bisect1), PODR_BIT_V (Pin (p,6),b6,bisect1),
       PODR_BIT_V (Pin (p,5),b5,bisect1), PODR_BIT_V (Pin (p,4),b4,bisect1),
       PODR_BIT_V (Pin (p,3),b3,bisect1), PODR_BIT_V (Pin (p,2),b2,bisect1),
       PODR_BIT_V (Pin (p,1),b1,bisect1), PODR_BIT_V (Pin (p,0),b0,bisect1))

absview PODR_PERMISSION (IOPort,bit_permissions)

viewdef PODR_PERMIT (p:IOPort,bs:bits) =
    [perms:bit_permissions]
    (PODR_PERMISSION (p,perms),BITS_PERMIT_CERTIFICATE (8,perms,bs))

fn {p:IOPort}{bs,cs:bits}
  writePODR (!PODR_V (p,bs) >> PODR_V (p,cs),
             !PODR_PERMIT (p,cs)
            | ioport_t p, bits_uint_t (8,cs)):<!wrt> void = "ext#"

fn {p:IOPort}{bs,cs:bits}{b:bit}
  changePODRBit {bn:int | bn < 8}
    (CHANGE_BIT_BITS (8,bs,bn,b,cs),
     !PODR_V (p,bs) >> PODR_V (p,cs),
     !PODR_PERMIT (p,cs)
    | pin_t (p,bn), bit_uint_t b):<!refwrt> void

fn {p:IOPort}{bs:bits}
  readPODR (!PODR_V (p,bs) | ioport_t p)
   :<!ref> bits_uint_t (8,bs)

fn podr2podr_bits {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}{v:int}
   (PODR_V (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) | bits_uint_t (8,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)))
   :(PODR_BIT_V (Pin (p,7),b7,bisect1),
     PODR_BIT_V (Pin (p,6),b6,bisect1),
     PODR_BIT_V (Pin (p,5),b5,bisect1),
     PODR_BIT_V (Pin (p,4),b4,bisect1),
     PODR_BIT_V (Pin (p,3),b3,bisect1),
     PODR_BIT_V (Pin (p,2),b2,bisect1),
     PODR_BIT_V (Pin (p,1),b1,bisect1),
     PODR_BIT_V (Pin (p,0),b0,bisect1),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),0,b0),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),1,b1),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),2,b2),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),3,b3),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),4,b4),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),5,b5),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),6,b6),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),7,b7)
    | @(bool (b7 == I),bool (b6 == I),bool (b5 == I),bool (b4 == I),
        bool (b3 == I),bool (b2 == I),bool (b1 == I),bool (b0 == I)))

// PIDR

absprop PIDR_BIT_P (Pin,bit)
dataprop PIDR_P (p:IOPort,bits) =
    {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
    PIDR_P (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) of
      (PIDR_BIT_P (Pin (p,7),b7), PIDR_BIT_P (Pin (p,6),b6),
       PIDR_BIT_P (Pin (p,5),b5), PIDR_BIT_P (Pin (p,4),b4),
       PIDR_BIT_P (Pin (p,3),b3), PIDR_BIT_P (Pin (p,2),b2),
       PIDR_BIT_P (Pin (p,1),b1), PIDR_BIT_P (Pin (p,0),b0))

fn {p:IOPort} readPIDR (ioport_t p)
   :<!ref> [bs:bits] (PIDR_P (p,bs) | bits_uint_t (8,bs))

fn pidr2pidr_bits {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}{v:int}
   (PIDR_P (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) | bits_uint_t (8,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)))
   :(PIDR_BIT_P (Pin (p,7),b7),
     PIDR_BIT_P (Pin (p,6),b6),
     PIDR_BIT_P (Pin (p,5),b5),
     PIDR_BIT_P (Pin (p,4),b4),
     PIDR_BIT_P (Pin (p,3),b3),
     PIDR_BIT_P (Pin (p,2),b2),
     PIDR_BIT_P (Pin (p,1),b1),
     PIDR_BIT_P (Pin (p,0),b0),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),0,b0),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),1,b1),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),2,b2),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),3,b3),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),4,b4),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),5,b5),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),6,b6),
     TEST_BIT_BITS (Bits8 (b7,b6,b5,b4,b3,b2,b1,b0),7,b7)
    | @(bool (b7 == I),bool (b6 == I),bool (b5 == I),bool (b4 == I),
        bool (b3 == I),bool (b2 == I),bool (b1 == I),bool (b0 == I)))

// GPIO

viewdef PinOutputView (p:Pin,output:bit) =
  [isel:bit][s,r,t:bisectional]
  (PFS_V (p,Bits8 (O,isel,O,O,O,O,O,O)),
   PMR_BIT_V (p,O,s),PDR_BIT_V (p,I,r),PODR_BIT_V (p,output,t))


absprop PinInput (Pin,bit)

fn readPinInput {p:IOPort}{n:int}{isel:bit}{s,r:bisectional}
   (!PFS_V (Pin (p,n),Bits8 (O,isel,O,O,O,O,O,O)),
   !PMR_BIT_V (Pin (p,n),O,s),!PDR_BIT_V (Pin (p,n),O,r) | pin_t (p,n))
   :<!ref> [input:bit] (PinInput (Pin (p,n),input) | bool (input==I))

stadef Bits8_all0 () : bits = Bits8 (O,O,O,O,O,O,O,O)
stadef Bits8_all1 () : bits = Bits8 (I,I,I,I,I,I,I,I)
stadef BitPerms8_all () : bit_permissions =
    BitPermissions8 (Permit,Permit,Permit,Permit,Permit,Permit,Permit,Permit,
                     Permit,Permit,Permit,Permit,Permit,Permit,Permit,Permit)

#if defined(MCU_RX110)
#if (MCU_Package_Pins == 64)
praxi rx110_initial_pmr_views () :
   (PMR_V (Port0,Bits8_all0),PMR_V (Port1,Bits8_all0),
    PMR_V (Port2,Bits8_all0),PMR_V (Port3,Bits8_all0),
    PMR_V (Port4,Bits8_all0),PMR_V (Port5,Bits8_all0),
    PMR_V (PortA,Bits8_all0),PMR_V (PortB,Bits8_all0),
    PMR_V (PortC,Bits8_all0),PMR_V (PortE,Bits8_all0),
    PMR_V (PortH,Bits8_all0),PMR_V (PortJ,Bits8_all0),
    PMR_PERMISSION (Port0,BitPerms8_all), PMR_PERMISSION (Port1,BitPerms8_all),
    PMR_PERMISSION (Port2,BitPerms8_all), PMR_PERMISSION (Port3,BitPerms8_all),
    PMR_PERMISSION (Port4,BitPerms8_all), PMR_PERMISSION (Port5,BitPerms8_all),
    PMR_PERMISSION (PortA,BitPerms8_all), PMR_PERMISSION (PortB,BitPerms8_all),
    PMR_PERMISSION (PortC,BitPerms8_all), PMR_PERMISSION (PortE,BitPerms8_all),
    PMR_PERMISSION (PortH,BitPerms8_all), PMR_PERMISSION (PortJ,BitPerms8_all)
   )

praxi rx110_consume_pmr_views (
    PMR_V (Port0,Bits8_all0),PMR_V (Port1,Bits8_all0),
    PMR_V (Port2,Bits8_all0),PMR_V (Port3,Bits8_all0),
    PMR_V (Port4,Bits8_all0),PMR_V (Port5,Bits8_all0),
    PMR_V (PortA,Bits8_all0),PMR_V (PortB,Bits8_all0),
    PMR_V (PortC,Bits8_all0),PMR_V (PortE,Bits8_all0),
    PMR_V (PortH,Bits8_all0),PMR_V (PortJ,Bits8_all0),
    PMR_PERMISSION (Port0,BitPerms8_all), PMR_PERMISSION (Port1,BitPerms8_all),
    PMR_PERMISSION (Port2,BitPerms8_all), PMR_PERMISSION (Port3,BitPerms8_all),
    PMR_PERMISSION (Port4,BitPerms8_all), PMR_PERMISSION (Port5,BitPerms8_all),
    PMR_PERMISSION (PortA,BitPerms8_all), PMR_PERMISSION (PortB,BitPerms8_all),
    PMR_PERMISSION (PortC,BitPerms8_all), PMR_PERMISSION (PortE,BitPerms8_all),
    PMR_PERMISSION (PortH,BitPerms8_all), PMR_PERMISSION (PortJ,BitPerms8_all)
   ): void

praxi rx110_initial_pfs_views (): //<lin>
   (PFS_V (Pin (Port0,0),Bits8_all0),PFS_V (Pin (Port0,1),Bits8_all0),
    PFS_V (Pin (Port0,2),Bits8_all0),PFS_V (Pin (Port0,3),Bits8_all0),
    PFS_V (Pin (Port0,4),Bits8_all0),PFS_V (Pin (Port0,5),Bits8_all0),
    PFS_V (Pin (Port0,6),Bits8_all0),PFS_V (Pin (Port0,7),Bits8_all0),
    PFS_V (Pin (Port1,0),Bits8_all0),PFS_V (Pin (Port1,1),Bits8_all0),
    PFS_V (Pin (Port1,2),Bits8_all0),PFS_V (Pin (Port1,3),Bits8_all0),
    PFS_V (Pin (Port1,4),Bits8_all0),PFS_V (Pin (Port1,5),Bits8_all0),
    PFS_V (Pin (Port1,6),Bits8_all0),PFS_V (Pin (Port1,7),Bits8_all0),
    PFS_V (Pin (Port2,0),Bits8_all0),PFS_V (Pin (Port2,1),Bits8_all0),
    PFS_V (Pin (Port2,2),Bits8_all0),PFS_V (Pin (Port2,3),Bits8_all0),
    PFS_V (Pin (Port2,4),Bits8_all0),PFS_V (Pin (Port2,5),Bits8_all0),
    PFS_V (Pin (Port2,6),Bits8_all0),PFS_V (Pin (Port2,7),Bits8_all0),
    PFS_V (Pin (Port3,0),Bits8_all0),PFS_V (Pin (Port3,1),Bits8_all0),
    PFS_V (Pin (Port3,2),Bits8_all0),PFS_V (Pin (Port3,3),Bits8_all0),
    PFS_V (Pin (Port3,4),Bits8_all0),PFS_V (Pin (Port3,5),Bits8_all0),
    PFS_V (Pin (Port3,6),Bits8_all0),PFS_V (Pin (Port3,7),Bits8_all0),
    PFS_V (Pin (Port4,0),Bits8_all0),PFS_V (Pin (Port4,1),Bits8_all0),
    PFS_V (Pin (Port4,2),Bits8_all0),PFS_V (Pin (Port4,3),Bits8_all0),
    PFS_V (Pin (Port4,4),Bits8_all0),PFS_V (Pin (Port4,5),Bits8_all0),
    PFS_V (Pin (Port4,6),Bits8_all0),PFS_V (Pin (Port4,7),Bits8_all0),
    PFS_V (Pin (Port5,0),Bits8_all0),PFS_V (Pin (Port5,1),Bits8_all0),
    PFS_V (Pin (Port5,2),Bits8_all0),PFS_V (Pin (Port5,3),Bits8_all0),
    PFS_V (Pin (Port5,4),Bits8_all0),PFS_V (Pin (Port5,5),Bits8_all0),
    PFS_V (Pin (Port5,6),Bits8_all0),PFS_V (Pin (Port5,7),Bits8_all0),
    PFS_V (Pin (PortA,0),Bits8_all0),PFS_V (Pin (PortA,1),Bits8_all0),
    PFS_V (Pin (PortA,2),Bits8_all0),PFS_V (Pin (PortA,3),Bits8_all0),
    PFS_V (Pin (PortA,4),Bits8_all0),PFS_V (Pin (PortA,5),Bits8_all0),
    PFS_V (Pin (PortA,6),Bits8_all0),PFS_V (Pin (PortA,7),Bits8_all0),
    PFS_V (Pin (PortB,0),Bits8_all0),PFS_V (Pin (PortB,1),Bits8_all0),
    PFS_V (Pin (PortB,2),Bits8_all0),PFS_V (Pin (PortB,3),Bits8_all0),
    PFS_V (Pin (PortB,4),Bits8_all0),PFS_V (Pin (PortB,5),Bits8_all0),
    PFS_V (Pin (PortB,6),Bits8_all0),PFS_V (Pin (PortB,7),Bits8_all0),
    PFS_V (Pin (PortC,0),Bits8_all0),PFS_V (Pin (PortC,1),Bits8_all0),
    PFS_V (Pin (PortC,2),Bits8_all0),PFS_V (Pin (PortC,3),Bits8_all0),
    PFS_V (Pin (PortC,4),Bits8_all0),PFS_V (Pin (PortC,5),Bits8_all0),
    PFS_V (Pin (PortC,6),Bits8_all0),PFS_V (Pin (PortC,7),Bits8_all0),
    PFS_V (Pin (PortE,0),Bits8_all0),PFS_V (Pin (PortE,1),Bits8_all0),
    PFS_V (Pin (PortE,2),Bits8_all0),PFS_V (Pin (PortE,3),Bits8_all0),
    PFS_V (Pin (PortE,4),Bits8_all0),PFS_V (Pin (PortE,5),Bits8_all0),
    PFS_V (Pin (PortE,6),Bits8_all0),PFS_V (Pin (PortE,7),Bits8_all0),
    PFS_V (Pin (PortH,0),Bits8_all0),PFS_V (Pin (PortH,1),Bits8_all0),
    PFS_V (Pin (PortH,2),Bits8_all0),PFS_V (Pin (PortH,3),Bits8_all0),
    PFS_V (Pin (PortH,4),Bits8_all0),PFS_V (Pin (PortH,5),Bits8_all0),
    PFS_V (Pin (PortH,6),Bits8_all0),PFS_V (Pin (PortH,7),Bits8_all0),
    PFS_V (Pin (PortJ,0),Bits8_all0),PFS_V (Pin (PortJ,1),Bits8_all0),
    PFS_V (Pin (PortJ,2),Bits8_all0),PFS_V (Pin (PortJ,3),Bits8_all0),
    PFS_V (Pin (PortJ,4),Bits8_all0),PFS_V (Pin (PortJ,5),Bits8_all0),
    PFS_V (Pin (PortJ,6),Bits8_all0),PFS_V (Pin (PortJ,7),Bits8_all0)
   )

praxi rx110_consume_pfs_views (
    PFS_V (Pin (Port0,0),Bits8_all0),PFS_V (Pin (Port0,1),Bits8_all0),
    PFS_V (Pin (Port0,2),Bits8_all0),PFS_V (Pin (Port0,3),Bits8_all0),
    PFS_V (Pin (Port0,4),Bits8_all0),PFS_V (Pin (Port0,5),Bits8_all0),
    PFS_V (Pin (Port0,6),Bits8_all0),PFS_V (Pin (Port0,7),Bits8_all0),
    PFS_V (Pin (Port1,0),Bits8_all0),PFS_V (Pin (Port1,1),Bits8_all0),
    PFS_V (Pin (Port1,2),Bits8_all0),PFS_V (Pin (Port1,3),Bits8_all0),
    PFS_V (Pin (Port1,4),Bits8_all0),PFS_V (Pin (Port1,5),Bits8_all0),
    PFS_V (Pin (Port1,6),Bits8_all0),PFS_V (Pin (Port1,7),Bits8_all0),
    PFS_V (Pin (Port2,0),Bits8_all0),PFS_V (Pin (Port2,1),Bits8_all0),
    PFS_V (Pin (Port2,2),Bits8_all0),PFS_V (Pin (Port2,3),Bits8_all0),
    PFS_V (Pin (Port2,4),Bits8_all0),PFS_V (Pin (Port2,5),Bits8_all0),
    PFS_V (Pin (Port2,6),Bits8_all0),PFS_V (Pin (Port2,7),Bits8_all0),
    PFS_V (Pin (Port3,0),Bits8_all0),PFS_V (Pin (Port3,1),Bits8_all0),
    PFS_V (Pin (Port3,2),Bits8_all0),PFS_V (Pin (Port3,3),Bits8_all0),
    PFS_V (Pin (Port3,4),Bits8_all0),PFS_V (Pin (Port3,5),Bits8_all0),
    PFS_V (Pin (Port3,6),Bits8_all0),PFS_V (Pin (Port3,7),Bits8_all0),
    PFS_V (Pin (Port4,0),Bits8_all0),PFS_V (Pin (Port4,1),Bits8_all0),
    PFS_V (Pin (Port4,2),Bits8_all0),PFS_V (Pin (Port4,3),Bits8_all0),
    PFS_V (Pin (Port4,4),Bits8_all0),PFS_V (Pin (Port4,5),Bits8_all0),
    PFS_V (Pin (Port4,6),Bits8_all0),PFS_V (Pin (Port4,7),Bits8_all0),
    PFS_V (Pin (Port5,0),Bits8_all0),PFS_V (Pin (Port5,1),Bits8_all0),
    PFS_V (Pin (Port5,2),Bits8_all0),PFS_V (Pin (Port5,3),Bits8_all0),
    PFS_V (Pin (Port5,4),Bits8_all0),PFS_V (Pin (Port5,5),Bits8_all0),
    PFS_V (Pin (Port5,6),Bits8_all0),PFS_V (Pin (Port5,7),Bits8_all0),
    PFS_V (Pin (PortA,0),Bits8_all0),PFS_V (Pin (PortA,1),Bits8_all0),
    PFS_V (Pin (PortA,2),Bits8_all0),PFS_V (Pin (PortA,3),Bits8_all0),
    PFS_V (Pin (PortA,4),Bits8_all0),PFS_V (Pin (PortA,5),Bits8_all0),
    PFS_V (Pin (PortA,6),Bits8_all0),PFS_V (Pin (PortA,7),Bits8_all0),
    PFS_V (Pin (PortB,0),Bits8_all0),PFS_V (Pin (PortB,1),Bits8_all0),
    PFS_V (Pin (PortB,2),Bits8_all0),PFS_V (Pin (PortB,3),Bits8_all0),
    PFS_V (Pin (PortB,4),Bits8_all0),PFS_V (Pin (PortB,5),Bits8_all0),
    PFS_V (Pin (PortB,6),Bits8_all0),PFS_V (Pin (PortB,7),Bits8_all0),
    PFS_V (Pin (PortC,0),Bits8_all0),PFS_V (Pin (PortC,1),Bits8_all0),
    PFS_V (Pin (PortC,2),Bits8_all0),PFS_V (Pin (PortC,3),Bits8_all0),
    PFS_V (Pin (PortC,4),Bits8_all0),PFS_V (Pin (PortC,5),Bits8_all0),
    PFS_V (Pin (PortC,6),Bits8_all0),PFS_V (Pin (PortC,7),Bits8_all0),
    PFS_V (Pin (PortE,0),Bits8_all0),PFS_V (Pin (PortE,1),Bits8_all0),
    PFS_V (Pin (PortE,2),Bits8_all0),PFS_V (Pin (PortE,3),Bits8_all0),
    PFS_V (Pin (PortE,4),Bits8_all0),PFS_V (Pin (PortE,5),Bits8_all0),
    PFS_V (Pin (PortE,6),Bits8_all0),PFS_V (Pin (PortE,7),Bits8_all0),
    PFS_V (Pin (PortH,0),Bits8_all0),PFS_V (Pin (PortH,1),Bits8_all0),
    PFS_V (Pin (PortH,2),Bits8_all0),PFS_V (Pin (PortH,3),Bits8_all0),
    PFS_V (Pin (PortH,4),Bits8_all0),PFS_V (Pin (PortH,5),Bits8_all0),
    PFS_V (Pin (PortH,6),Bits8_all0),PFS_V (Pin (PortH,7),Bits8_all0),
    PFS_V (Pin (PortJ,0),Bits8_all0),PFS_V (Pin (PortJ,1),Bits8_all0),
    PFS_V (Pin (PortJ,2),Bits8_all0),PFS_V (Pin (PortJ,3),Bits8_all0),
    PFS_V (Pin (PortJ,4),Bits8_all0),PFS_V (Pin (PortJ,5),Bits8_all0),
    PFS_V (Pin (PortJ,6),Bits8_all0),PFS_V (Pin (PortJ,7),Bits8_all0)
   ): void

praxi rx110_initial_pdr_views ():
   (PDR_V (Port0,Bits8_all0),PDR_V (Port1,Bits8_all0),
    PDR_V (Port2,Bits8_all0),PDR_V (Port3,Bits8_all0),
    PDR_V (Port4,Bits8_all0),PDR_V (Port5,Bits8_all0),
    PDR_V (PortA,Bits8_all0),PDR_V (PortB,Bits8_all0),
    PDR_V (PortC,Bits8_all0),PDR_V (PortE,Bits8_all0),
    PDR_V (PortH,Bits8_all0),PDR_V (PortJ,Bits8_all0),
    PDR_PERMISSION (Port0,BitPerms8_all), PDR_PERMISSION (Port1,BitPerms8_all),
    PDR_PERMISSION (Port2,BitPerms8_all), PDR_PERMISSION (Port3,BitPerms8_all),
    PDR_PERMISSION (Port4,BitPerms8_all), PDR_PERMISSION (Port5,BitPerms8_all),
    PDR_PERMISSION (PortA,BitPerms8_all), PDR_PERMISSION (PortB,BitPerms8_all),
    PDR_PERMISSION (PortC,BitPerms8_all), PDR_PERMISSION (PortE,BitPerms8_all),
    PDR_PERMISSION (PortH,BitPerms8_all), PDR_PERMISSION (PortJ,BitPerms8_all)
   )

praxi rx110_consume_pdr_views (
    PDR_V (Port0,Bits8_all0),PDR_V (Port1,Bits8_all0),
    PDR_V (Port2,Bits8_all0),PDR_V (Port3,Bits8_all0),
    PDR_V (Port4,Bits8_all0),PDR_V (Port5,Bits8_all0),
    PDR_V (PortA,Bits8_all0),PDR_V (PortB,Bits8_all0),
    PDR_V (PortC,Bits8_all0),PDR_V (PortE,Bits8_all0),
    PDR_V (PortH,Bits8_all0),PDR_V (PortJ,Bits8_all0),
    PDR_PERMISSION (Port0,BitPerms8_all), PDR_PERMISSION (Port1,BitPerms8_all),
    PDR_PERMISSION (Port2,BitPerms8_all), PDR_PERMISSION (Port3,BitPerms8_all),
    PDR_PERMISSION (Port4,BitPerms8_all), PDR_PERMISSION (Port5,BitPerms8_all),
    PDR_PERMISSION (PortA,BitPerms8_all), PDR_PERMISSION (PortB,BitPerms8_all),
    PDR_PERMISSION (PortC,BitPerms8_all), PDR_PERMISSION (PortE,BitPerms8_all),
    PDR_PERMISSION (PortH,BitPerms8_all), PDR_PERMISSION (PortJ,BitPerms8_all)
   ): void

praxi rx110_initial_podr_views ():
   (PODR_V (Port0,Bits8_all0),PODR_V (Port1,Bits8_all0),
    PODR_V (Port2,Bits8_all0),PODR_V (Port3,Bits8_all0),
    PODR_V (Port4,Bits8_all0),PODR_V (Port5,Bits8_all0),
    PODR_V (PortA,Bits8_all0),PODR_V (PortB,Bits8_all0),
    PODR_V (PortC,Bits8_all0),PODR_V (PortE,Bits8_all0),
    PODR_V (PortH,Bits8_all0),PODR_V (PortJ,Bits8_all0),
    PODR_PERMISSION (Port0,BitPerms8_all), PODR_PERMISSION (Port1,BitPerms8_all),
    PODR_PERMISSION (Port2,BitPerms8_all), PODR_PERMISSION (Port3,BitPerms8_all),
    PODR_PERMISSION (Port4,BitPerms8_all), PODR_PERMISSION (Port5,BitPerms8_all),
    PODR_PERMISSION (PortA,BitPerms8_all), PODR_PERMISSION (PortB,BitPerms8_all),
    PODR_PERMISSION (PortC,BitPerms8_all), PODR_PERMISSION (PortE,BitPerms8_all),
    PODR_PERMISSION (PortH,BitPerms8_all), PODR_PERMISSION (PortJ,BitPerms8_all)
   )

praxi rx110_consume_podr_views (
    PODR_V (Port0,Bits8_all0),PODR_V (Port1,Bits8_all0),
    PODR_V (Port2,Bits8_all0),PODR_V (Port3,Bits8_all0),
    PODR_V (Port4,Bits8_all0),PODR_V (Port5,Bits8_all0),
    PODR_V (PortA,Bits8_all0),PODR_V (PortB,Bits8_all0),
    PODR_V (PortC,Bits8_all0),PODR_V (PortE,Bits8_all0),
    PODR_V (PortH,Bits8_all0),PODR_V (PortJ,Bits8_all0),
    PODR_PERMISSION (Port0,BitPerms8_all), PODR_PERMISSION (Port1,BitPerms8_all),
    PODR_PERMISSION (Port2,BitPerms8_all), PODR_PERMISSION (Port3,BitPerms8_all),
    PODR_PERMISSION (Port4,BitPerms8_all), PODR_PERMISSION (Port5,BitPerms8_all),
    PODR_PERMISSION (PortA,BitPerms8_all), PODR_PERMISSION (PortB,BitPerms8_all),
    PODR_PERMISSION (PortC,BitPerms8_all), PODR_PERMISSION (PortE,BitPerms8_all),
    PODR_PERMISSION (PortH,BitPerms8_all), PODR_PERMISSION (PortJ,BitPerms8_all)
   ): void

#endif
#endif


