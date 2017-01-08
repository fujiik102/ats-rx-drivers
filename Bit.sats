// bit関連の定義

#define INTBITS				32
#define	INTMAX     		2147483647
#define	INTMAX_HALF		1073741823
#define	UINTMAX_HALF	2147483647

datasort bit = | O | I

dataprop bit_lte (bit, bit) =
 | {b:bit}        bit_lte_lte_refl (b, b) of ()
 | {b1,b2,b3:bit} bit_lte_tran (b1,b3) of
                    (bit_lte (b1,b2), bit_lte (b2,b3))
 |                bit_lte_b1_b0 (I, O) of ()

datasort bits = BitsNil of () | BitsCons of (bit, bits)

dataprop BITSEQINT (int, bits, int) =
 | BEQNIL (0,BitsNil,0) of ()
 | {n:int}{bs:bits}{v:int | v <= INTMAX_HALF}
   BEQCONS0 (n+1,BitsCons (O, bs),v+v) of (BITSEQINT (n,bs,v))
 | {n:int}{bs:bits}{v:int | v <= INTMAX_HALF}
   BEQCONS1 (n+1,BitsCons (I, bs),v+v+1) of (BITSEQINT (n,bs,v))

dataprop BITSLEN (int,bits) =
 | BITSLENNIL (0,BitsNil) of ()
 | {n:int}{b:bit}{bs:bits}
   BITSLENCONS (n+1,BitsCons (b,bs)) of BITSLEN (n,bs)

dataprop BITEQBOOL (bit, bool) =
 | B0EQFALSE (O, false) of ()
 | B1EQTRUE  (I, true ) of ()

dataprop BITEQINT (bit, int) =
 | B0EQ0 (O, 0) of ()
 | B1EQ1 (I, 1) of ()

praxi {v:int} beqint_bit_eq {b,c:bit | b == c} (BITEQINT (b,v)):BITEQINT (c,v)

typedef bit_int_t (b:bit) = [v:int] (BITEQINT (b,v) | int v)

stadef Bits8 (b7,b6,b5,b4,b3,b2,b1,b0:bit): bits =
  BitsCons (b0, BitsCons (b1, BitsCons (b2, BitsCons (b3,
  BitsCons (b4, BitsCons (b5, BitsCons (b6, BitsCons (b7,
  BitsNil))))))))

prfn bits_test1 () : BITSEQINT (0,BitsNil (),0)
prfn bits8_test2 () : BITSEQINT (8,Bits8 (O,O,O,O,O,O,O,O), 0)
prfn bits8_test3 () : BITSEQINT (8,Bits8 (I,I,I,I,I,I,I,I), 255)
prfn bits8_test4_1 () : BITSEQINT (8,Bits8 (O,O,O,O,O,O,O,I),  1)
prfn bits8_test4_2 () : BITSEQINT (8,Bits8 (O,O,O,O,O,O,I,O),  2)
prfn bits8_test4_3 () : BITSEQINT (8,Bits8 (O,O,O,O,O,I,O,O),  4)
prfn bits8_test4_4 () : BITSEQINT (8,Bits8 (O,O,O,O,I,O,O,O),  8)
prfn bits8_test4_5 () : BITSEQINT (8,Bits8 (O,O,O,I,O,O,O,O), 16)
prfn bits8_test4_6 () : BITSEQINT (8,Bits8 (O,O,I,O,O,O,O,O), 32)
prfn bits8_test4_7 () : BITSEQINT (8,Bits8 (O,I,O,O,O,O,O,O), 64)
prfn bits8_test4_8 () : BITSEQINT (8,Bits8 (I,O,O,O,O,O,O,O), 128)

(*
prfn bits_eq__ge_0 {bs:bits}{n,v:int}
  (BITSEQINT (n,bs,v)) : [v>=0] void
*)
prfn bitscons0_eq_double {bs:bits}{n,v:int | v <= INTMAX_HALF}
  (BITSEQINT (n,bs,v)) : BITSEQINT (n+1,BitsCons (O,bs),v+v)
prfn bitscons0_eq__cons1_inc {bs:bits}{n,v:int}
  (BITSEQINT (n,BitsCons (O,bs),v)) : BITSEQINT (n,BitsCons (I,bs),v+1)

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


praxi {bs,cs:bits}{n:int} chgbit_bit_eq {b,c:bit | b == c}
       (CHANGE_BIT_BITS (bs,n,b,cs)):
        CHANGE_BIT_BITS (bs,n,c,cs)


fn {b:bit}{bs:bits}
  changeBitBits {n,bn:nat | bn < n}{n < INTBITS} (bits_int_t (n,bs),int bn,bit_int_t b)
  : [bs':bits] (CHANGE_BIT_BITS (bs,bn,b,bs') | bits_int_t (n,bs'))

fn {bs:bits}
  setBitBits {n,bn:nat | bn < n}{n < INTBITS} (bits_int_t (n,bs),int bn)
  : [cs:bits] (CHANGE_BIT_BITS (bs,bn,I,cs) | bits_int_t (n,cs))

fn {bs:bits}
  clearBitBits {n,bn:nat | bn < n}{n < INTBITS} (bits_int_t (n,bs),int bn)
  : [bs':bits] (CHANGE_BIT_BITS (bs,bn,O,bs') | bits_int_t (n,bs'))

dataprop TEST_BIT_BITS (bits,int,bit) =
 | {b:bit}{bs:bits} TEST_BIT_BITS_0 (BitsCons (b,bs),0,b) of ()
 | {b,c:bit}{bs:bits}{n:int}
   TEST_BIT_BITS_N (BitsCons (c,bs),n+1,b)
    of TEST_BIT_BITS (bs,n,b)

fn {bs:bits}
  testBitBits {n,bn:nat | bn < n}{n < INTBITS} (bits_int_t (n,bs),int bn)
  : [b:bit] (TEST_BIT_BITS (bs,bn,b) | bool (b==I))

datasort permission = Permit | Prohibit

datasort bit_permission = BitPermission of
  (permission(*for 0*),permission(*for 1*))

dataprop BIT_PERM_PERMIT (bit_permission,bit) =
 | {p1:permission} BITPERM_0 (BitPermission (Permit,p1),O) of ()
 | {p0:permission} BITPERM_1 (BitPermission (p0,Permit),I) of ()

datasort bit_permissions = 
 | BitPermsNil of ()
 | BitPermsCons of (bit_permission,bit_permissions)

dataprop BIT_PERMS_PERMIT (int,bit_permissions,bits) =
 | BITPERMSPERM_NIL (0, BitPermsNil, BitsNil) of ()
 | {n:int}{p:bit_permission}{ps:bit_permissions}{b:bit}{bs:bits}
   BITPERMSPERM_CONS (n+1,BitPermsCons (p,ps),BitsCons (b,bs))
    of (BIT_PERM_PERMIT (p,b),BIT_PERMS_PERMIT (n,ps,bs))


