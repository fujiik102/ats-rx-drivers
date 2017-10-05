


prfn {n:int} le_plus_1 ():[n <= n + 1] void = ()
prfn {n:int} le_refl   ():[n <= n]     void = ()
prfn {n:int} plus_0    ():[n == n + 0] void = ()



prfun le_plus_nat {n,m:int | n <= m}{p:nat} .<p>. ():[n <= m+p] void =
  sif 0 < p then let
      prval () = le_plus_nat {n,m}{p-1} ()
    in le_plus_1<n> () end
  else let
      prval () = plus_0<m> ()
    in (* nothing *) end

dataprop POW2 (int,int) =
 | POW2_0 (0,1) of ()
 | {n,v:int} POW2_N (n+1,v+v) of POW2 (n,v)

prfun pow2_total {n:nat} .<n>. ():[npow:int] POW2 (n,npow) =
  sif 0 < n then POW2_N (pow2_total {n-1} ())
            else POW2_0 ()

extern praxi pow2_0_domain_nat {n:int} (POW2 (n,0)):[0 <= n] void
prfun pow2_not_0_domain_nat {n,npow:int | npow != 0} .<abs npow>.
                            (npow2:POW2 (n,npow)):[0 <= n] void
 = sif 0 <= n then ()
   else case+ npow2 of
       | POW2_0 () =/=> ()
       | POW2_N (n'pow) =/=> let prval () = pow2_not_0_domain_nat (n'pow) in end  

(*
prfun pow2_unique_lemma {n:nat}{npow1,npow2:int} .<n>.
      (pow1:POW2 (n,npow1),pow2:POW2 (n,npow2)) : [npow1==npow2] void
 = case+ (pow1,pow2) of
   | (POW2_0 (),POW2_0 ()) => ()
   | (POW2_N (pow1'),POW2_N (pow2')) =>
     sif 0 < n then pow2_unique_lemma (pow1',pow2')
     else let in sif 0 != npow1 then let
       prval () = pow2_not_0_domain_nat (pow1')
     in end else let in sif 0 != npow2 then let
       prval () = pow2_not_0_domain_nat (pow2')
     in end else () end end
   | (POW2_N (pow1'),POW2_0 ()) =/=> ()
   | (POW2_0 (),POW2_N (pow2')) =/=> ()
*)

prfn {n,npow:int} pow2_domain_nat (pow2:POW2 (n,npow)):[0 <= n] void
 = sif 0 !=   npow then pow2_not_0_domain_nat (pow2) else pow2_0_domain_nat(pow2)

prfun pow2_range_lte_1 {n:nat}{npow:int} .<n>. (pow:POW2 (n,npow)):[1 <= npow] void
 = case+ pow of
   | POW2_0 ()        => () // 1 <= 1
   | POW2_N (pow_ind) => let
       prval () = pow2_domain_nat (pow_ind)
       prval () = pow2_range_lte_1 (pow_ind)
     in  end // 1 <= npow_ind -> 1 <= npow_ind+npow_ind

prfn pow2_lte {n,npow:int} (pow2:POW2 (n,npow)):[0 <= n][1 <= npow] void
 = let
     prval () = pow2_domain_nat (pow2)
     prval () = pow2_range_lte_1 (pow2)
   in end

prfun pow2_injective {n,npow1,npow2:nat} .<n>. (pow1:POW2 (n,npow1), pow2:POW2 (n,npow2)):[npow1==npow2] void
 = sif 0 < n then let
       prval POW2_N (pow1') = pow1
       prval POW2_N (pow2') = pow2
     in pow2_injective (pow1',pow2') end
   else case+ (pow1,pow2) of
        | (POW2_0 (), POW2_0 ()) => () // 0 == 0
        | (POW2_N (pow_ind), _) =/=> let prval () = pow2_lte (pow_ind) in end // 0 == n && 0 <= n-1
        | (_, POW2_N (pow_ind)) =/=> let prval () = pow2_lte (pow_ind) in end // 0 == n && 0 <= n-1

prfn npow_lte_int31 {npow:nat}
      (pow2:POW2 (31,npow)): [npow <= 2147483648] void
 = let
    prfn npow_double {n,npow,nmax:nat | npow <= nmax/2}
      (pow2:POW2 (n,npow)):[npow+npow <= nmax] POW2 (n+1,npow+npow)
     = POW2_N pow2
    prval pow2' = npow_double {30,1073741824,2147483648}(npow_double {29,536870912,1073741824}(
                  npow_double {28,268435456,536870912}(npow_double {27,134217728,268435456}(
                  npow_double {26,67108864,134217728}(npow_double {25,33554432,67108864}(
                  npow_double {24,16777216,33554432}(npow_double {23,8388608,16777216}(
                  npow_double {22,4194304,8388608}(npow_double {21,2097152,4194304}(
                  npow_double {20,1048576,2097152}(npow_double {19,524288,1048576}(
                  npow_double {18,262144,524288}(npow_double {17,131072,262144}(
                  npow_double {16,65536,131072}(npow_double {15,32768,65536}(
                  npow_double {14,16384,32768}(npow_double {13,8192,16384}(
                  npow_double {12,4096,8192}(npow_double {11,2048,4096}(
                  npow_double {10,1024,2048}(npow_double {9,512,1024}(
                  npow_double {8,256,512}(npow_double {7,128,256}(
                  npow_double {6,64,128}(npow_double {5,32,64}(
                  npow_double {4,16,32}(npow_double {3,8,16}(
                  npow_double {2,4,8}(npow_double {1,2,4}(
                  npow_double {0,1,2}(POW2_0 (
                  ))))))))))))))))))))))))))))))))
    prval () = pow2_injective(pow2,pow2')
 in  end

prfun npow_monotonically_increasing {n,m,npow,mpow:nat | n < m}
      .<m>. (pow2_n:POW2 (n,npow),pow2_m:POW2 (m,mpow)):[npow < mpow] void
 = case+ pow2_m of
   | POW2_0 ()           =/=> () // (n < m) && (0 = m)
   | POW2_N (pow2_m_ind) =>   let
       prval () = pow2_lte (pow2_m_ind)
     in case+ pow2_n of
        | POW2_0 ()           => () // (0 = n) && (0 <= m-1)
        | POW2_N (pow2_n_ind) => let
            prval () = pow2_lte (pow2_n_ind)
          in npow_monotonically_increasing (pow2_n_ind, pow2_m_ind) end
     end

prfun npow_intmax {n,npow,m:nat | n < INTBITS; m < npow}
      .<INTBITS - n>. (pow2:POW2 (n,npow)): [m <= INTMAX] void
 = sif (31 == n) then npow_lte_int31 (pow2)
   else let
        prval () = pow2_lte (POW2_N (pow2))
        prval () = npow_intmax{n+1,npow+npow,m+m} (POW2_N (pow2))
   in npow_monotonically_increasing (pow2,POW2_N (pow2)) end

prfn beqint_is_nat {n,v:int}{bs:bits}
  (beqint_fst:BITSEQINT (n,bs,v)):[0 <= v] void =
let
  prfun aux {n,v:int}{bs:bits} .<bs>. (beqint:BITSEQINT (n,bs,v)):[0 <= v] void =
    case+ beqint of
    | BEQNIL   ()       => le_refl ()   // 0 <= 0
    | BEQCONS (beqind,B0EQ0 ()) => aux (beqind) // (0 <= n) -> (0 <= n+0)
    | BEQCONS (beqind,B1EQ1 ()) => aux (beqind) // (0 <= n) -> (0 <= n+1)
in aux (beqint_fst) end

dataprop NAT_EVEN (int) =
 | NEVENbas (0) of ()
 | {n:nat} NEVENind (n+2) of NAT_EVEN (n)

dataprop NAT_ODD (int) =
 | NODDbas (1) of ()
 | {n:nat} NODDind (n+2) of NAT_ODD (n)

prfn {n:int} neven_nat (ev:NAT_EVEN (n)):[0 <= n] void
 = case+ ev of
   | NEVENbas ()       => le_refl ()
   | NEVENind {n'} (_) => le_plus_nat {0,n'}{2} ()

prfn {n:int} nodd_gte_1 (odd:NAT_ODD (n)):[1 <= n] void
 = sif 1 <= n then ()
       else case+ odd of
       | NODDbas ()       =/=> () // 1 < 1
       | NODDind {n'} (_) =/=> () // 0 <= n' && n'+2 < 1

prfun nodd_prev_is_even {n:nat} .<n>. (odd:NAT_ODD (n)):NAT_EVEN (n-1)
 = case+ odd of
   | NODDbas ()       => NEVENbas ()
   | NODDind (oddind) => let
       prval () = nodd_gte_1 (oddind)
     in NEVENind (nodd_prev_is_even (oddind)) end

datasort oddity = EVEN | ODD

dataprop NAT_ODDITY (int,oddity) =
 | {n:int} NATeven (n,EVEN) of NAT_EVEN (n)
 | {n:int} NATodd  (n,ODD)  of NAT_ODD  (n)

prfun natoddity_total {n:nat} .<n>. ():[o:oddity] NAT_ODDITY (n,o)
 = sif      n == 0 then NATeven (NEVENbas ())
   else sif n == 1 then NATodd  (NODDbas  ())
   else     case+ natoddity_total {n-2} () of
            | NATeven (ev)  => NATeven (NEVENind (ev))
            | NATodd  (odd) => let prval () = nodd_gte_1 (odd)
                               in NATodd  (NODDind  (odd)) end

prfun nat_half {n:nat} .<n>. (ev:NAT_EVEN (n)):[h:nat | h+h == n] int h
 = case+ ev of
   | NEVENbas ()   => 0 // 0+0 == 0
   | NEVENind {n'} (ev) => let prval () = neven_nat<n'> (ev)
                           in nat_half {n'} (ev) + 1 (* h+h == n' -> h+1 + h+1 == n'+2 *) end

prfn double_v_lt_2pow_succ__v_lt_2pow {v,n,npow_succ,npow:nat | v+v < npow_succ}
                                      (pow2:POW2(n,npow),pow2succ:POW2 (n+1,npow_succ)):[v < npow] void
 = let
     prval () = pow2_injective (POW2_N (pow2), pow2succ)// npow_succ == npow+npow
   in end // v+v < npow+npow -> v < npow

prfun nat_eq_bits {n,npow,v:nat | v < npow}{v <= INTMAX} .<n>.
  (pow2:POW2 (n,npow)):[bs:bits] BITSEQINT (n,bs,v) =
  sif 0 < n then let
      prval POW2_N {n',npow'} (pow2ind) = pow2
      prval () = pow2_lte (pow2ind)
    in case+ natoddity_total {v} () of
       | NATeven (ev) => let
           prval [h:int](_) = nat_half {v} (ev)
           prval () = double_v_lt_2pow_succ__v_lt_2pow {h,n',npow,npow'} (pow2ind,pow2) // h < npow'
         in BEQCONS (nat_eq_bits {n',npow',h} (pow2ind),B0EQ0) end
       | NATodd  (odd) => let
           prval (ev) = nodd_prev_is_even (odd)
           prval () = nodd_gte_1 (odd)
           prval [h:int](_) = nat_half {v-1} (ev)
           prval () = double_v_lt_2pow_succ__v_lt_2pow {h,n',npow,npow'} (pow2ind,pow2) // h < npow'
         in BEQCONS (nat_eq_bits {n',npow',h} (pow2ind),B1EQ1) end
    end
  else let
      prval () = pow2_injective (pow2, POW2_0 ())
    in BEQNIL () end

