// bit関連の定義


#define INTBITS				32
#define	INTMAX     		2147483647
#define	INTMAX_HALF		1073741823
#define	UINTMAX_HALF	2147483647

datasort bit = | O | I

// TODO 使ってないので消す。
dataprop bit_lte (bit, bit) =
 | {b:bit}        bit_lte_lte_refl (b, b) of ()
 | {b1,b2,b3:bit} bit_lte_tran (b1,b3) of
                    (bit_lte (b1,b2), bit_lte (b2,b3))
 |                bit_lte_b1_b0 (I, O) of ()

datasort bits = BitsNil of () | BitsCons of (bit, bits)

// TODO BITEQINTをベースにした定義に変更する？
dataprop BITSEQINT (int, bits, int) =
 | BEQNIL (0,BitsNil,0) of ()
 | {n:int}{bs:bits}{v:int | v <= INTMAX_HALF}
   BEQCONS0 (n+1,BitsCons (O, bs),v+v) of (BITSEQINT (n,bs,v))
 | {n:int}{bs:bits}{v:int | v <= INTMAX_HALF}
   BEQCONS1 (n+1,BitsCons (I, bs),v+v+1) of (BITSEQINT (n,bs,v))

dataprop BITSLEN (bits,int) =
 | BITSLENNIL (BitsNil,0) of ()
 | {n:int}{b:bit}{bs:bits}
   BITSLENCONS (BitsCons (b,bs),n+1) of BITSLEN (bs,n)

dataprop BITEQBOOL (bit, bool) =
 | B0EQFALSE (O, false) of ()
 | B1EQTRUE  (I, true ) of ()

dataprop BITEQINT (bit, int) =
 | B0EQ0 (O, 0) of ()
 | B1EQ1 (I, 1) of ()

// TODO prfnに変更して証明する。
praxi {v:int} beqint_bit_eq {b,c:bit | b == c} (BITEQINT (b,v)):BITEQINT (c,v)

typedef bit_uint_t (b:bit) = [v:int] (BITEQINT (b,v) | uint v)

stadef Bits8 (b7,b6,b5,b4,b3,b2,b1,b0:bit): bits =
  BitsCons (b0, BitsCons (b1, BitsCons (b2, BitsCons (b3,
  BitsCons (b4, BitsCons (b5, BitsCons (b6, BitsCons (b7,
  BitsNil))))))))

prfn bits_test1    () : BITSEQINT (0,BitsNil (),0)
prfn bits8_test2   () : BITSEQINT (8,Bits8 (O,O,O,O,O,O,O,O),   0)
prfn bits8_test3   () : BITSEQINT (8,Bits8 (I,I,I,I,I,I,I,I), 255)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (O,O,O,O,O,O,O,I),   1)
prfn bits8_test4_2 () : BITSEQINT (8,Bits8 (O,O,O,O,O,O,I,O),   2)
prfn bits8_test4_3 () : BITSEQINT (8,Bits8 (O,O,O,O,O,I,O,O),   4)
prfn bits8_test4_4 () : BITSEQINT (8,Bits8 (O,O,O,O,I,O,O,O),   8)
prfn bits8_test4_5 () : BITSEQINT (8,Bits8 (O,O,O,I,O,O,O,O),  16)
prfn bits8_test4_6 () : BITSEQINT (8,Bits8 (O,O,I,O,O,O,O,O),  32)
prfn bits8_test4_7 () : BITSEQINT (8,Bits8 (O,I,O,O,O,O,O,O),  64)
prfn bits8_test4_8 () : BITSEQINT (8,Bits8 (I,O,O,O,O,O,O,O), 128)

(*
prfn bits_eq__ge_0 {bs:bits}{n,v:int}
  (BITSEQINT (n,bs,v)) : [v>=0] void
*)
prfn bitscons0_eq_double {bs:bits}{n,v:int | v <= INTMAX_HALF}
  (BITSEQINT (n,bs,v)) : BITSEQINT (n+1,BitsCons (O,bs),v+v)
prfn bitscons0_eq__cons1_inc {bs:bits}{n,v:int}
  (BITSEQINT (n,BitsCons (O,bs),v)) : BITSEQINT (n,BitsCons (I,bs),v+1)

typedef bits_uint_t (n:int,bs:bits) =
  [v:int] (BITSEQINT (n,bs,v) | uint v)

typedef bits8_uint_t (b7,b6,b5,b4,b3,b2,b1,b0:bit) =
  bits_uint_t (8,Bits8 (b7,b6,b5,b4,b3,b2,b1,b0))

dataprop EQBITS (bits, bits) = {bs:bits} EQBITS (bs, bs)
praxi eqbits_make {bs,cs:bits | bs == cs} (): EQBITS (bs,cs)


dataprop EQBIT (bit, bit) = {b:bit} EQBIT (b, b)
praxi eqbit_make {b,c:bit | b == c} (): EQBIT (b,c)

praxi bit_eq_refl {b:bit} ():[b == b] void
praxi bits_eq_refl {bs:bits} ():[bs == bs] void



prfun le_plus_nat {n,m:int | n <= m}{p:nat} ():[n <= m+p] void

dataprop POW2 (int,int) =
 | POW2_0 (0,1) of ()
 | {n,v:int} POW2_N (n+1,v+v) of POW2 (n,v)

prfun pow2_total {n:nat} ():[npow:int] POW2 (n,npow)
praxi pow2_domain_nat {n,npow:int} (POW2 (n,npow)):[0 <= n] void

prfun pow2_range_lte_1 {n:nat}{npow:int} (pow:POW2 (n,npow)):[1 <= npow] void
prfn pow2_lte {n,npow:int} (pow2:POW2 (n,npow)):[0 <= n][1 <= npow] void
prfun pow2_injective {n,npow1,npow2:nat} (pow1:POW2 (n,npow1), pow2:POW2 (n,npow2)):[npow1==npow2] void
prfn beqint_is_nat {n,v:int}{bs:bits}
  (beqint_fst:BITSEQINT (n,bs,v)):[0 <= v] void

dataprop NAT_EVEN (int) =
 | NEVENbas (0) of ()
 | {n:nat} NEVENind (n+2) of NAT_EVEN (n)

dataprop NAT_ODD (int) =
 | NODDbas (1) of ()
 | {n:nat} NODDind (n+2) of NAT_ODD (n)

prfn {n:int} neven_nat (ev:NAT_EVEN (n)):[0 <= n] void
prfn {n:int} nodd_gte_1 (odd:NAT_ODD (n)):[1 <= n] void
prfun nodd_prev_is_even {n:nat} (odd:NAT_ODD (n)):NAT_EVEN (n-1)

datasort oddity = EVEN | ODD

dataprop NAT_ODDITY (int,oddity) =
 | {n:int} NATeven (n,EVEN) of NAT_EVEN (n)
 | {n:int} NATodd  (n,ODD)  of NAT_ODD  (n)

prfun natoddity_total {n:nat} ():[o:oddity] NAT_ODDITY (n,o)
prfun nat_half {n:nat} (ev:NAT_EVEN (n)):[h:nat | h+h == n] int h
prfn double_v_lt_2pow_succ__v_lt_2pow {v,n,npow_succ,npow:nat | v+v < npow_succ}
                                      (pow2:POW2(n,npow),pow2succ:POW2 (n+1,npow_succ)):[v < npow] void
prfun nat_eq_bits {n,npow,v:nat | v < npow}{v <= INTMAX}
  (pow2:POW2 (n,npow)):[bs:bits] BITSEQINT (n,bs,v)


dataprop CHANGE_BIT_BITS (int,bits,int,bit,bits) =
 | {n:int}{b,c:bit}{bs:bits} CHANGE_BIT_BITS_bas
     (n+1,BitsCons (b,bs),n,c,BitsCons (c,bs)) of (BITSLEN (bs,n))
 | {n,bn:int}{b,c:bit}{bs,cs:bits}
   CHANGE_BIT_BITS_ind(n+1,BitsCons (c,bs),bn,b,BitsCons (c,cs))
    of CHANGE_BIT_BITS (n,bs,bn,b,cs)

dataprop TEST_BIT_BITS (bits,int,bool) =
 | {bn:int}{b:bit}{bs:bits} TEST_BIT_BITS_bas (BitsCons (b,bs),bn,b == I)
     of (BITSLEN (bs,bn))
 | {test:bool}{b:bit}{bs:bits}{bn:int}
   TEST_BIT_BITS_ind (BitsCons (b,bs),bn,test) of TEST_BIT_BITS (bs,bn,test)



fn {b:bit}{bs:bits}
  changeBitBits {n,bn:nat | bn < n; n < INTBITS} (bits_uint_t (n,bs),uint bn,bit_uint_t b)
  : [bs':bits] (CHANGE_BIT_BITS (n,bs,bn,b,bs') | bits_uint_t (n,bs'))

fn {bs:bits}
  setBitBits {n,bn:nat | bn < n; n < INTBITS} (bits_uint_t (n,bs),uint bn)
  : [cs:bits] (CHANGE_BIT_BITS (n,bs,bn,I,cs) | bits_uint_t (n,cs))

fn {bs:bits}
  clearBitBits {n,bn:nat | bn < n; n < INTBITS} (bits_uint_t (n,bs),uint bn)
  : [bs':bits] (CHANGE_BIT_BITS (n,bs,bn,O,bs') | bits_uint_t (n,bs'))

fn {bs:bits}
  testBitBits {n,bn:nat | bn < n}{n < INTBITS} (bits_uint_t (n,bs),uint bn)
  : [b:bool] (TEST_BIT_BITS (bs,bn,b) | bool b)

// TODO prfnに変更して証明する。
praxi {bs,cs:bits}{n,bn:int} chgbit_bit_eq {b,c:bit | b == c}
       (CHANGE_BIT_BITS (n,bs,bn,b,cs)):
        CHANGE_BIT_BITS (n,bs,bn,c,cs)


dataprop BIT_LOR (bit,bit,bit) =
 | BIT_LOR_II (I,I,I) of ()
 | BIT_LOR_IO (I,O,I) of ()
 | BIT_LOR_OI (O,I,I) of ()
 | BIT_LOR_OO (O,O,O) of ()

dataprop BITS_LOR (bits,bits,bits) =
 | BITS_LOR_NIL  (BitsNil,BitsNil,BitsNil) of ()
 | {b,c,d:bit}{bs,cs,ds:bits}
   BITS_LOR_CONS (BitsCons (b,bs),BitsCons (c,cs),BitsCons (d,ds))
    of (BIT_LOR (b,c,d), BITS_LOR (bs,cs,ds))

fn {n:int}{bs,cs:bits} bits_uint_lor (n:bits_uint_t (n,bs),m:bits_uint_t (n,cs)):
   [ds:bits] (BITS_LOR (bs,cs,ds) | bits_uint_t (n,ds))


dataprop BIT_LAND (bit,bit,bit) =
 | BIT_LAND_II (I,I,I) of ()
 | BIT_LAND_IO (I,O,O) of ()
 | BIT_LAND_OI (O,I,O) of ()
 | BIT_LAND_OO (O,O,O) of ()

dataprop BITS_LAND (bits,bits,bits) =
 | BITS_LAND_NIL  (BitsNil,BitsNil,BitsNil) of ()
 | {b,c,d:bit}{bs,cs,ds:bits}
   BITS_LAND_CONS (BitsCons (b,bs),BitsCons (c,cs),BitsCons (d,ds))
    of (BIT_LAND (b,c,d), BITS_LAND (bs,cs,ds))

fn {n:int}{bs,cs:bits} bits_uint_land (n:bits_uint_t (n,bs),m:bits_uint_t (n,cs)):
   [ds:bits] (BITS_LAND (bs,cs,ds) | bits_uint_t (n,ds))


dataprop SINGLE_BIT_BITS (int,int,bits) =
 | {n:int}{bs:bits}    SINGLE_BIT_BITS_bas (n+1,n, BitsCons (I,bs))
                                        of (BITSEQINT (n,bs,0))
 | {n,bn:int}{bs:bits} SINGLE_BIT_BITS_ind (n+1,bn,BitsCons (O,bs))
                                        of (SINGLE_BIT_BITS (n,bn,bs))

// 1 << bn
fn {n,bn:int} make_single_bit (bn:uint bn):
  [bs:bits] (SINGLE_BIT_BITS (n,bn,bs) | bits_uint_t (n,bs))


dataprop BIT_NOT (bit,bit) =
 | BIT_NOT1 (I,O)
 | BIT_NOT0 (O,I)

dataprop BITS_NOT (bits,bits) =
 | BITS_NOT_NIL  (BitsNil,BitsNil) of ()
 | {b,c:bit}{bs,cs:bits}
   BITS_NOT_CONS (BitsCons (b,bs),BitsCons (c,cs))
    of (BIT_NOT (b,c), BITS_NOT (bs,cs))

stadef neq_bit_bit (b,c:bit):bool = ~(b == c)
stadef != = neq_bit_bit

praxi bit_not_I_eq_O ():[I != O] void
praxi bit_not_eq_comm {b,c:bit | b != c} ():[c != b] void

fn {n:int}{bs:bits} bits_uint_not (n:bits_uint_t (n,bs)):
   [cs:bits] (BITS_NOT (bs,cs) | bits_uint_t (n,cs))



// TODO bit_permission関連の証明を書く。
datasort permission = Permit | Prohibit

datasort bit_permission = BitPermission of
  (permission(*of 0*),permission(*of 1*))

datasort bit_permissions = 
 | BitPermsNil of ()
 | BitPermsCons of (bit_permission,bit_permissions)

stadef BitPermissions8 (b7_0,b7_1,b6_0,b6_1,b5_0,b5_1,b4_0,b4_1,
                        b3_0,b3_1,b2_0,b2_1,b1_0,b1_1,b0_0,b0_1:permission): bit_permissions =
  BitPermsCons (BitPermission (b0_0,b0_1),BitPermsCons (BitPermission (b1_0,b1_1),
  BitPermsCons (BitPermission (b2_0,b2_1),BitPermsCons (BitPermission (b3_0,b3_1),
  BitPermsCons (BitPermission (b4_0,b4_1),BitPermsCons (BitPermission (b5_0,b5_1), BitPermsCons (BitPermission(b4_0,b4_1),
  BitPermsCons (BitPermission (b6_0,b6_1),BitPermsCons (BitPermission (b7_0,b7_1),
  BitPermsNil ())))))))))

// TODO 許可された　にするべき？
dataprop BIT_REQUIRE_PERMISSION (bit_permission,bit) =
 | {p1:permission} BITREQPERM_0 (BitPermission (Permit,p1),O) of ()
 | {p0:permission} BITREQPERM_1 (BitPermission (p0,Permit),I) of ()

dataprop BIT_REQUIRE_PERMISSIONS (int,bit_permissions,bits) =
 | BITREQPERMS_NIL (0, BitPermsNil, BitsNil) of ()
 | {n:int}{p:bit_permission}{ps:bit_permissions}{b:bit}{bs:bits}
   BITREQPERMS_CONS (n+1,BitPermsCons (p,ps),BitsCons (b,bs))
    of (BIT_REQUIRE_PERMISSION (p,b),BIT_REQUIRE_PERMISSIONS (n,ps,bs))


prfn breqperm_0 {bs:bits}(
    BIT_REQUIRE_PERMISSIONS (8,BitPermissions8 (
        Prohibit,Permit, Prohibit,Permit, Prohibit,Permit, Prohibit,Permit,
        Prohibit,Permit, Prohibit,Permit, Prohibit,Permit, Prohibit,Permit),
      bs))
    : [bs == Bits8 (O,O,O,O,O,O,O,O)] void

prfn breqperm_1 {bs:bits}(
    BIT_REQUIRE_PERMISSIONS (8,BitPermissions8 (
        Prohibit,Permit, Prohibit,Permit, Prohibit,Permit, Prohibit,Permit,
        Prohibit,Permit, Prohibit,Permit, Prohibit,Permit, Permit,Prohibit),
      bs))
    : [bs == Bits8 (O,O,O,O,O,O,O,I)] void

prfn breqperm_2 {bs:bits}(
    BIT_REQUIRE_PERMISSIONS (8,BitPermissions8 (
        Prohibit,Permit, Prohibit,Permit, Prohibit,Permit, Prohibit,Permit,
        Prohibit,Permit, Prohibit,Permit, Permit,Prohibit, Prohibit,Permit),
      bs))
    : [bs == Bits8 (O,O,O,O,O,O,I,O)] void

prfn breqperm_128 {bs:bits}(
    BIT_REQUIRE_PERMISSIONS (8,BitPermissions8 (
        Permit,Prohibit, Prohibit,Permit, Prohibit,Permit, Prohibit,Permit,
        Prohibit,Permit, Prohibit,Permit, Prohibit,Permit, Prohibit,Permit),
      bs))
    : [bs == Bits8 (I,O,O,O,O,O,O,O)] void

prfn breqperm_255 {bs:bits}(
    BIT_REQUIRE_PERMISSIONS (8,BitPermissions8 (
        Permit,Prohibit, Permit,Prohibit, Permit,Prohibit, Permit,Prohibit,
        Permit,Prohibit, Permit,Prohibit, Permit,Prohibit, Permit,Prohibit),
      bs))
    : [bs == Bits8 (I,I,I,I,I,I,I,I)] void

prfn breqperm_all {bs:bits}(BITSLEN (bs,8)):
    BIT_REQUIRE_PERMISSIONS (8,BitPermissions8 (
        Permit,Permit, Permit,Permit, Permit,Permit, Permit,Permit,
        Permit,Permit, Permit,Permit, Permit,Permit, Permit,Permit),
      bs)

prfn breqperm_inhaditat {any_prop:prop}{n:int}{bs:bits}{ps:bit_permissions}
    (BIT_REQUIRE_PERMISSIONS (n,
       BitPermsCons(BitPermission (Prohibit,Prohibit), ps),
       bs)): any_prop
