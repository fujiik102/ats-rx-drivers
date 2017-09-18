
// Pin control drivers

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

typedef ioport_uint_t (p:IOPort) = uint (IOPort2int p)

datasort Pin = Pin of (IOPort,int)

typedef pin_uint_t (p:IOPort,n:int) = @(ioport_uint_t p, uint n)


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

stadef bisect1 = bisectional (0,1)

dataprop EQBISECTIONAL (bisectional, bisectional) = {r:bisectional} EQBISECTIONAL (r, r)
praxi eqbisectional_make {r,s:bisectional | r == s} () : EQBISECTIONAL (r,s)
praxi bisectional_eq_refl {r:bisectional} () : [r == r] void
praxi bisectional_eq_reduce {n,m:int | n <= INTMAX_HALF} ():
      [bisectional (n,m) == bisectional (n+n,m+1)] void

stacst bisectional_add_b : (bisectional,bisectional,bisectional) -> bool

praxi {n1,n2,m:int} bisectional_add_axi ():
      [bisectional_add_b (bisectional (n1,m),bisectional (n2,m),bisectional (n1+n2,m))] unit_p

stacst bisectional_half_b : (bisectional,bisectional) -> bool

praxi {n,m:int} bisectional_half_axi ():
      [bisectional_half_b (bisectional (n,m),bisectional (n,m+1))] unit_p

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
      (PMR_BIT_V (Pin (p,7),b0,bisect1), PMR_BIT_V (Pin (p,6),b1,bisect1),
       PMR_BIT_V (Pin (p,5),b2,bisect1), PMR_BIT_V (Pin (p,4),b3,bisect1),
       PMR_BIT_V (Pin (p,3),b4,bisect1), PMR_BIT_V (Pin (p,2),b5,bisect1),
       PMR_BIT_V (Pin (p,1),b6,bisect1), PMR_BIT_V (Pin (p,0),b7,bisect1))

absprop PMR_PERMISSION (IOPort,bit_permissions)

propdef PMR_PERMIT (p:IOPort,bs:bits) =
    [perms:bit_permissions]
    (PMR_PERMISSION (p,perms),BITS_PERMIT_CERTIFICATE (8,perms,bs))

fn {bs,cs:bits}{p:IOPort}
  writePMR (PMR_V (p,bs), PMR_PERMIT (p,cs) | ioport_uint_t p, bits_uint_t (8,cs))
   :(PMR_V (p,cs) | void)

fn {bs,cs:bits}{p:IOPort}{b:bit}
  changePMRBit {bn:int | bn < 8}
    (CHANGE_BIT_BITS (8,bs,bn,b,cs),
     !PMR_V (p,bs) >> PMR_V (p,cs),
     PMR_PERMIT (p,cs)
    | pin_uint_t (p,bn), bit_uint_t b):void

fn {bs:bits}{p:IOPort}
  readPMR (!PMR_V (p,bs) | p:ioport_uint_t p)
   :bits_uint_t (8,bs)

fn {p:IOPort}{n:int}{b:bit}{r:bisectional}
  readPMRbit (!PMR_BIT_V (Pin (p,n),b,r) | pin:pin_uint_t (p,n))
   :bool (b==I)

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
  | pin_uint_t (p,pnum),
    bits8int_t (O,O,O,O,O,O,O,O)
  )
  :void

fn {p:IOPort}{pnum:int}{asel,isel,psel4,psel3,psel2,psel1,psel0:bit}
  readPFS (
    !PFS_V (Pin (p,pnum),Bits8 (asel,isel,O,psel4,psel3,psel2,psel1,psel0))
  | pin_uint_t (p, pnum)
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
      (PDR_BIT_V (Pin (p,7),b0,bisect1), PDR_BIT_V (Pin (p,6),b1,bisect1),
       PDR_BIT_V (Pin (p,5),b2,bisect1), PDR_BIT_V (Pin (p,4),b3,bisect1),
       PDR_BIT_V (Pin (p,3),b4,bisect1), PDR_BIT_V (Pin (p,2),b5,bisect1),
       PDR_BIT_V (Pin (p,1),b6,bisect1), PDR_BIT_V (Pin (p,0),b7,bisect1))

absprop PDR_PERMISSION (IOPort,bit_permissions)

propdef PDR_PERMIT (p:IOPort,bs:bits) =
    [perms:bit_permissions]
    (PDR_PERMISSION (p,perms),BITS_PERMIT_CERTIFICATE (8,perms,bs))

fn {p:IOPort}{bs,cs:bits}{v: int}
  writePDR (PDR_PERMIT (p,cs),
            !PDR_V (p,bs) >> PDR_V (p,cs) |
            ioport_uint_t p,bits_uint_t (8,cs)):void

fn {p:IOPort}{bs:bits}
  readPDR (!PDR_V (p,bs) | ioport_uint_t p)
   : bits_uint_t (8,bs)

fn {p:IOPort}{n:int}{b:bit}{r:bisectional}
  readPDRbit (!PDR_BIT_V (Pin (p,n),b,r) | pin:pin_uint_t (p,n))
   :bool (b==I)

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
      (PODR_BIT_V (Pin (p,7),b0,bisect1), PODR_BIT_V (Pin (p,6),b1,bisect1),
       PODR_BIT_V (Pin (p,5),b2,bisect1), PODR_BIT_V (Pin (p,4),b3,bisect1),
       PODR_BIT_V (Pin (p,3),b4,bisect1), PODR_BIT_V (Pin (p,2),b5,bisect1),
       PODR_BIT_V (Pin (p,1),b6,bisect1), PODR_BIT_V (Pin (p,0),b7,bisect1))

absprop PODR_PERMISSION (IOPort,bit_permissions)

propdef PODR_PERMIT (p:IOPort,bs:bits) =
    [perms:bit_permissions]
    (PODR_PERMISSION (p,perms),BITS_PERMIT_CERTIFICATE (8,perms,bs))

fn {p:IOPort}{bs,cs:bits}
  writePODR (PODR_PERMIT (p,cs),
             !PODR_V (p,bs) >> PODR_V (p,cs) |
             ioport_uint_t p, bits_uint_t (8,cs)):void

fn {p:IOPort}{bs:bits}
  readPODR (PODR_V (p,bs) | ioport_uint_t p)
   :bits_uint_t (8,bs)

fn {p:IOPort}{n:int}{b:bit}{r:bisectional}
  readPODRbit (!PODR_BIT_V (Pin (p,n),b,r) | pin:pin_uint_t (p,n))
   :bool (b==I)

// PIDR

absprop PIDR_BIT_P (Pin,bit)
dataprop PIDR_P (p:IOPort,bits) =
    {p:IOPort}{b7,b6,b5,b4,b3,b2,b1,b0:bit}
    PIDR_P (p,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0)) of
      (PIDR_BIT_P (Pin (p,7),b0), PIDR_BIT_P (Pin (p,6),b1),
       PIDR_BIT_P (Pin (p,5),b2), PIDR_BIT_P (Pin (p,4),b3),
       PIDR_BIT_P (Pin (p,3),b4), PIDR_BIT_P (Pin (p,2),b5),
       PIDR_BIT_P (Pin (p,1),b6), PIDR_BIT_P (Pin (p,0),b7))

fn {p:IOPort} readPIDR (ioport_uint_t p)
   :[bs:bits] (PIDR_P (p,bs) | bits_uint_t (8,bs))

// GPIO

viewdef PinOutputView (p:Pin,output:bit) =
  [isel:bit][s,r,t:bisectional]
  (PFS_V (p,Bits8 (O,isel,O,O,O,O,O,O)),
   PMR_BIT_V (p,O,s),PDR_BIT_V (p,I,r),PODR_BIT_V (p,output,t))


absprop PinInput (Pin,bit)

fn readPinInput {p:IOPort}{n:int}{isel:bit}{s,r:bisectional}
   (PFS_V (Pin (p,n),Bits8 (O,isel,O,O,O,O,O,O)),
   !PMR_BIT_V (Pin (p,n),O,s),!PDR_BIT_V (Pin (p,n),O,r) | pin_uint_t (p,n))
   : [input:bit] (PinInput (Pin (p,n),input) | bool (input==I))

////

// TODO Make a view expressing the setting of output voltage and open drain etc.
(*
fn getInitialPinViews () : //<lin>
    (GPIOView (P0 0,O,I),
     GPIOView (P0 1,I,O),
     GPIOView (P1 0,O,O),
     GPIOView (P1 1,I,I)
     | void)
*)

// TODO make initial absprops.
////
fn rx110_64pins_initial_views ():<lin> (
    PODR_PERMISSION (Port0,BitPermissions8 (Permit,Permit,Permit,Permit,Permit,Permit,Permit,Permit)),
    PODR_V          (Port0,Bits8(O,O,O,O,O,O,O,O)),
    
)


