/-
A Lean-checked computational certificate for the matrix-congruence core of

  "A Trace and Companion-Matrix Solution to the July 2010 IBM Ponder This
   Challenge"

This file proves, by verified computation inside Lean, the finite congruence
claims used in the paper for the companion matrix

      [ 3  0 -1 ]
  A = [ 1  0  0 ].
      [ 0  1  0 ]

The real/trigonometric Pisot and rounding parts of the paper are not formalized
in this file.  In particular, the final theorem here certifies the congruence
`tr(A^n) = 0 mod 10^9`, not the analytic statement about
`round ((1 + 2 * cos (20 degrees))^n)`.
-/

namespace IBMPonderThis

structure Mat3 where
  a00 : Nat
  a01 : Nat
  a02 : Nat
  a10 : Nat
  a11 : Nat
  a12 : Nat
  a20 : Nat
  a21 : Nat
  a22 : Nat
deriving Repr

def idMat (m : Nat) : Mat3 :=
  { a00 := 1 % m, a01 := 0, a02 := 0
    a10 := 0, a11 := 1 % m, a12 := 0
    a20 := 0, a21 := 0, a22 := 1 % m }

def A (m : Nat) : Mat3 :=
  { a00 := 3 % m, a01 := 0, a02 := (m - 1) % m
    a10 := 1 % m, a11 := 0, a12 := 0
    a20 := 0, a21 := 1 % m, a22 := 0 }

def mulMod (m : Nat) (X Y : Mat3) : Mat3 :=
  { a00 := (X.a00 * Y.a00 + X.a01 * Y.a10 + X.a02 * Y.a20) % m
    a01 := (X.a00 * Y.a01 + X.a01 * Y.a11 + X.a02 * Y.a21) % m
    a02 := (X.a00 * Y.a02 + X.a01 * Y.a12 + X.a02 * Y.a22) % m
    a10 := (X.a10 * Y.a00 + X.a11 * Y.a10 + X.a12 * Y.a20) % m
    a11 := (X.a10 * Y.a01 + X.a11 * Y.a11 + X.a12 * Y.a21) % m
    a12 := (X.a10 * Y.a02 + X.a11 * Y.a12 + X.a12 * Y.a22) % m
    a20 := (X.a20 * Y.a00 + X.a21 * Y.a10 + X.a22 * Y.a20) % m
    a21 := (X.a20 * Y.a01 + X.a21 * Y.a11 + X.a22 * Y.a21) % m
    a22 := (X.a20 * Y.a02 + X.a21 * Y.a12 + X.a22 * Y.a22) % m }

def powMod (m : Nat) (X : Mat3) (n : Nat) : Mat3 :=
  match n with
  | 0 => idMat m
  | n' + 1 =>
      let half := powMod m X ((n' + 1) / 2)
      let square := mulMod m half half
      if (n' + 1) % 2 = 0 then square else mulMod m square X
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n') (by decide)

def matEq (X Y : Mat3) : Bool :=
  (X.a00 == Y.a00) &&
  (X.a01 == Y.a01) &&
  (X.a02 == Y.a02) &&
  (X.a10 == Y.a10) &&
  (X.a11 == Y.a11) &&
  (X.a12 == Y.a12) &&
  (X.a20 == Y.a20) &&
  (X.a21 == Y.a21) &&
  (X.a22 == Y.a22)

def traceMod (m : Nat) (X : Mat3) : Nat :=
  (X.a00 + X.a11 + X.a22) % m

def ten9 : Nat := 1000000000
def sharpL : Nat := 21700000000
def sharpN : Nat := 21699999999
def coarseM : Nat := 24998400000000000
def coarseN : Nat := 24998399999999999

theorem A_pow_7_identity_mod_2 :
    matEq (powMod 2 (A 2) 7) (idMat 2) = true := by
  native_decide

theorem A_pow_1_not_identity_mod_2 :
    matEq (powMod 2 (A 2) 1) (idMat 2) = false := by
  native_decide

theorem A_pow_62_identity_mod_5 :
    matEq (powMod 5 (A 5) 62) (idMat 5) = true := by
  native_decide

theorem A_pow_1_not_identity_mod_5 :
    matEq (powMod 5 (A 5) 1) (idMat 5) = false := by
  native_decide

theorem A_pow_2_not_identity_mod_5 :
    matEq (powMod 5 (A 5) 2) (idMat 5) = false := by
  native_decide

theorem A_pow_31_not_identity_mod_5 :
    matEq (powMod 5 (A 5) 31) (idMat 5) = false := by
  native_decide

theorem A_pow_7_times_2_pow_8_identity_mod_2_pow_9 :
    matEq (powMod (2 ^ 9) (A (2 ^ 9)) (7 * 2 ^ 8)) (idMat (2 ^ 9)) = true := by
  native_decide

theorem A_pow_62_times_5_pow_8_identity_mod_5_pow_9 :
    matEq (powMod (5 ^ 9) (A (5 ^ 9)) (62 * 5 ^ 8)) (idMat (5 ^ 9)) = true := by
  native_decide

theorem A_pow_sharpL_identity_mod_10_pow_9 :
    matEq (powMod ten9 (A ten9) sharpL) (idMat ten9) = true := by
  native_decide

theorem trace_A_pow_sharpN_zero_mod_10_pow_9 :
    traceMod ten9 (powMod ten9 (A ten9) sharpN) = 0 := by
  native_decide

theorem A_pow_coarseM_identity_mod_10_pow_9 :
    matEq (powMod ten9 (A ten9) coarseM) (idMat ten9) = true := by
  native_decide

theorem trace_A_pow_coarseN_zero_mod_10_pow_9 :
    traceMod ten9 (powMod ten9 (A ten9) coarseN) = 0 := by
  native_decide

end IBMPonderThis
