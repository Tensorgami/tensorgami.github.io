import IBMPonderThis.Certificate
import IBMPonderThis.RealBridge
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.style.nativeDecide false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

namespace IBMPonderThisFinal

open Matrix

def toZModMat (m : Nat) (X : IBMPonderThis.Mat3) : Matrix (Fin 3) (Fin 3) (ZMod m)
  | ⟨0, _⟩, ⟨0, _⟩ => X.a00
  | ⟨0, _⟩, ⟨1, _⟩ => X.a01
  | ⟨0, _⟩, ⟨2, _⟩ => X.a02
  | ⟨1, _⟩, ⟨0, _⟩ => X.a10
  | ⟨1, _⟩, ⟨1, _⟩ => X.a11
  | ⟨1, _⟩, ⟨2, _⟩ => X.a12
  | ⟨2, _⟩, ⟨0, _⟩ => X.a20
  | ⟨2, _⟩, ⟨1, _⟩ => X.a21
  | ⟨2, _⟩, ⟨2, _⟩ => X.a22

lemma toZModMat_id (m : Nat) :
    toZModMat m (IBMPonderThis.idMat m) = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [toZModMat, IBMPonderThis.idMat]

lemma toZModMat_mul (m : Nat) (X Y : IBMPonderThis.Mat3) :
    toZModMat m (IBMPonderThis.mulMod m X Y) =
      toZModMat m X * toZModMat m Y := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [toZModMat, IBMPonderThis.mulMod, Matrix.mul_apply, Fin.sum_univ_three]

lemma toZModMat_powMod (m : Nat) (X : IBMPonderThis.Mat3) (n : Nat) :
    toZModMat m (IBMPonderThis.powMod m X n) = toZModMat m X ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [IBMPonderThis.powMod, toZModMat_id]
      | succ n' =>
          simp only [IBMPonderThis.powMod]
          have hhalf :
              toZModMat m (IBMPonderThis.powMod m X ((n' + 1) / 2)) =
                toZModMat m X ^ ((n' + 1) / 2) :=
            ih ((n' + 1) / 2) (Nat.div_lt_self (Nat.succ_pos n') (by decide))
          by_cases heven : (n' + 1) % 2 = 0
          · rw [if_pos heven]
            rw [toZModMat_mul, hhalf]
            have hn : n' + 1 = (n' + 1) / 2 + (n' + 1) / 2 := by omega
            calc
              toZModMat m X ^ ((n' + 1) / 2) * toZModMat m X ^ ((n' + 1) / 2)
                  = toZModMat m X ^ ((n' + 1) / 2 + (n' + 1) / 2) := by
                    rw [pow_add]
              _ = toZModMat m X ^ (n' + 1) := by rw [← hn]
          · rw [if_neg heven, toZModMat_mul]
            rw [toZModMat_mul, hhalf]
            have hn : n' + 1 = (n' + 1) / 2 + (n' + 1) / 2 + 1 := by omega
            calc
              toZModMat m X ^ ((n' + 1) / 2) * toZModMat m X ^ ((n' + 1) / 2) *
                    toZModMat m X
                  = toZModMat m X ^ ((n' + 1) / 2 + (n' + 1) / 2) *
                    toZModMat m X := by
                    rw [pow_add]
              _ = toZModMat m X ^ ((n' + 1) / 2 + (n' + 1) / 2 + 1) := by
                    rw [pow_succ]
              _ = toZModMat m X ^ (n' + 1) := by rw [← hn]

def zmodA (m : Nat) : Matrix (Fin 3) (Fin 3) (ZMod m) :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 3
    | 0, 1 => 0
    | 0, 2 => -1
    | 1, 0 => 1
    | 1, 1 => 0
    | 1, 2 => 0
    | 2, 0 => 0
    | 2, 1 => 1
    | 2, 2 => 0
    | _, _ => 0

lemma toZModMat_A_ten9 :
    toZModMat IBMPonderThis.ten9 (IBMPonderThis.A IBMPonderThis.ten9) =
      zmodA IBMPonderThis.ten9 := by
  native_decide

lemma trace_toZModMat (m : Nat) (X : IBMPonderThis.Mat3) :
    Matrix.trace (toZModMat m X) = (IBMPonderThis.traceMod m X : ZMod m) := by
  simp [Matrix.trace, toZModMat, IBMPonderThis.traceMod, Fin.sum_univ_three]

lemma zmodA_ten9_cayley :
    zmodA IBMPonderThis.ten9 ^ 3 = 3 • zmodA IBMPonderThis.ten9 ^ 2 - 1 := by
  native_decide

lemma zmodA_ten9_trace_recurrence (n : Nat) :
    Matrix.trace (zmodA IBMPonderThis.ten9 ^ (n + 3)) =
      3 * Matrix.trace (zmodA IBMPonderThis.ten9 ^ (n + 2)) -
        Matrix.trace (zmodA IBMPonderThis.ten9 ^ n) := by
  let A := zmodA IBMPonderThis.ten9
  have hmat : A ^ (n + 3) = 3 • A ^ (n + 2) - A ^ n := by
    calc
      A ^ (n + 3) = A ^ n * A ^ 3 := by rw [pow_add]
      _ = A ^ n * (3 • A ^ 2 - 1) := by rw [zmodA_ten9_cayley]
      _ = 3 • A ^ (n + 2) - A ^ n := by
        rw [show A ^ (n + 2) = A ^ n * A ^ 2 by rw [pow_add]]
        noncomm_ring
  rw [hmat, Matrix.trace_sub, Matrix.trace_smul]
  simp [A]

lemma zmodA_ten9_trace_zero :
    Matrix.trace (zmodA IBMPonderThis.ten9 ^ 0) = (3 : ZMod IBMPonderThis.ten9) := by
  native_decide

lemma zmodA_ten9_trace_one :
    Matrix.trace (zmodA IBMPonderThis.ten9 ^ 1) = (3 : ZMod IBMPonderThis.ten9) := by
  native_decide

lemma zmodA_ten9_trace_two :
    Matrix.trace (zmodA IBMPonderThis.ten9 ^ 2) = (9 : ZMod IBMPonderThis.ten9) := by
  native_decide

theorem traceInt_eq_zmodA_ten9_trace (n : Nat) :
    (IBMPonderThisBridge.traceInt n : ZMod IBMPonderThis.ten9) =
      Matrix.trace (zmodA IBMPonderThis.ten9 ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          simpa [IBMPonderThisBridge.traceInt] using zmodA_ten9_trace_zero.symm
      | 1 =>
          simpa [IBMPonderThisBridge.traceInt] using zmodA_ten9_trace_one.symm
      | 2 =>
          simpa [IBMPonderThisBridge.traceInt] using zmodA_ten9_trace_two.symm
      | k + 3 =>
          rw [IBMPonderThisBridge.traceInt, zmodA_ten9_trace_recurrence]
          have h2 :
              (IBMPonderThisBridge.traceInt (k + 2) : ZMod IBMPonderThis.ten9) =
                Matrix.trace (zmodA IBMPonderThis.ten9 ^ (k + 2)) :=
            ih (k + 2) (by omega)
          have h0 :
              (IBMPonderThisBridge.traceInt k : ZMod IBMPonderThis.ten9) =
                Matrix.trace (zmodA IBMPonderThis.ten9 ^ k) :=
            ih k (by omega)
          norm_num [h2, h0]

theorem traceInt_sharpN_zmod_zero :
    (IBMPonderThisBridge.traceInt IBMPonderThis.sharpN : ZMod IBMPonderThis.ten9) = 0 := by
  rw [traceInt_eq_zmodA_ten9_trace]
  rw [← toZModMat_A_ten9]
  rw [← toZModMat_powMod]
  rw [trace_toZModMat]
  norm_num [IBMPonderThis.trace_A_pow_sharpN_zero_mod_10_pow_9]

theorem ibm_ponder_this_main :
    (1000000000 : ℤ) ∣
      round (IBMPonderThisBridge.alpha ^ 21699999999) := by
  rw [IBMPonderThisBridge.round_alpha_sharpN_eq_traceInt]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (IBMPonderThisBridge.traceInt IBMPonderThis.sharpN) IBMPonderThis.ten9).mp
    traceInt_sharpN_zmod_zero

end IBMPonderThisFinal
