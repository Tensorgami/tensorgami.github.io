import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

open Nat

namespace ExtractingFirstPrime

def firstGcd (m : ℕ) : ℕ :=
  Nat.gcd ((m ! : ℕ) ^ (m ! : ℕ) - 1) ((2 * m) !)

def exponentFilterT (d : ℕ) : ℕ :=
  d ^ d / Nat.gcd (d ^ d) (d !)

def largestDPowerDividing (d t : ℕ) : ℕ :=
  Nat.findGreatest (fun a => d ^ a ∣ t) t

def extractedPrime (m : ℕ) : ℕ :=
  let d := firstGcd m
  let t := exponentFilterT d
  let a := largestDPowerDividing d t
  d / Nat.gcd (t / d ^ a) d

def minExponent (m : ℕ) : ℕ :=
  firstGcd m - ((firstGcd m) !).factorization (firstGcd m).minFac

lemma firstGcd_pos (m : ℕ) : 0 < firstGcd m := by
  unfold firstGcd
  exact Nat.gcd_pos_of_pos_right _ (Nat.factorial_pos (2 * m))

lemma bertrand_strict {m : ℕ} (hm : 2 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ m < p ∧ p < 2 * m := by
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  refine ⟨p, hp, hmp, lt_of_le_of_ne hp2m ?_⟩
  intro hp_eq
  have hp_even : Even p := by
    rw [hp_eq]
    exact even_two_mul m
  have : p = 2 := hp.even_iff.mp hp_even
  omega

lemma two_mul_dvd_factorial_self {q : ℕ} (hq : 3 ≤ q) :
    2 * q ∣ q ! := by
  have h2 : 2 ∣ (q - 1) ! := Nat.dvd_factorial (by norm_num) (by omega)
  rcases h2 with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  calc
    q ! = ((q - 1) + 1) ! := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
    _ = ((q - 1) + 1) * (q - 1) ! := by
      rw [Nat.factorial_succ]
    _ = q * (q - 1) ! := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
    _ = q * (2 * c) := by rw [hc]
    _ = (2 * q) * c := by ring

lemma pred_prime_dvd_factorial_of_between_nonexceptional {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hmp : m < p) (hp2m : p < 2 * m)
    (h_ex : ¬(m = 3 ∧ p = 5)) :
    p - 1 ∣ m ! := by
  by_cases hp5 : p = 5
  · have hm4 : m = 4 := by
      by_contra hm_ne
      have : m = 3 := by omega
      exact h_ex ⟨this, hp5⟩
    subst m
    subst p
    norm_num
  · have hp_ne_four : p ≠ 4 := by
      intro h
      rw [h] at hp
      norm_num at hp
    have hpgt5 : 5 < p := by
      omega
    have hpne2 : p ≠ 2 := by omega
    let q := (p - 1) / 2
    have htwoq : 2 * q = p - 1 := Nat.two_mul_div_two_of_even (hp.even_sub_one hpne2)
    have hq3 : 3 ≤ q := by omega
    have hqm : q ≤ m := by omega
    rw [← htwoq]
    exact (two_mul_dvd_factorial_self hq3).trans (Nat.factorial_dvd_factorial hqm)

lemma factorial_pow_modEq_one_of_between {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hmp : m < p) (hp2m : p < 2 * m) :
    (m ! : ℕ) ^ (m ! : ℕ) ≡ 1 [MOD p] := by
  by_cases h_ex : m = 3 ∧ p = 5
  · rcases h_ex with ⟨rfl, rfl⟩
    norm_num
  · have hnotdvd : ¬p ∣ m ! := by
      rw [hp.dvd_factorial]
      omega
    have hcop : (m !).Coprime p := (hp.coprime_iff_not_dvd.mpr hnotdvd).symm
    have hflt : (m ! : ℕ) ^ (p - 1) ≡ 1 [MOD p] :=
      Nat.ModEq.pow_card_sub_one_eq_one hp hcop
    obtain ⟨c, hc⟩ :=
      pred_prime_dvd_factorial_of_between_nonexceptional hm hp hmp hp2m h_ex
    calc
      (m ! : ℕ) ^ (m ! : ℕ) ≡ ((m ! : ℕ) ^ (p - 1)) ^ c [MOD p] := by
        rw [hc, pow_mul]
      _ ≡ 1 ^ c [MOD p] := hflt.pow c
      _ ≡ 1 [MOD p] := by
        simpa using (Nat.ModEq.refl (1 : ℕ) : 1 ≡ 1 [MOD p])

lemma dvd_first_factor_of_between {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hmp : m < p) (hp2m : p < 2 * m) :
    p ∣ (m ! : ℕ) ^ (m ! : ℕ) - 1 := by
  have hmod := factorial_pow_modEq_one_of_between hm hp hmp hp2m
  have hle : 1 ≤ (m ! : ℕ) ^ (m ! : ℕ) := by
    exact one_le_pow₀ (Nat.succ_le_of_lt (Nat.factorial_pos m))
  exact (Nat.modEq_iff_dvd' hle).mp hmod.symm

lemma prime_dvd_firstGcd_of_between {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hmp : m < p) (hp2m : p < 2 * m) :
    p ∣ firstGcd m := by
  apply Nat.dvd_gcd
  · exact dvd_first_factor_of_between hm hp hmp hp2m
  · exact hp.dvd_factorial.mpr (by omega)

lemma between_of_prime_dvd_firstGcd {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hpd : p ∣ firstGcd m) :
    m < p ∧ p < 2 * m := by
  let X := (m ! : ℕ) ^ (m ! : ℕ)
  have hA : p ∣ X - 1 := by
    simpa [firstGcd, X] using hpd.trans
      (Nat.gcd_dvd_left ((m ! : ℕ) ^ (m ! : ℕ) - 1) ((2 * m) !))
  have hB : p ∣ (2 * m) ! := by
    simpa [firstGcd] using hpd.trans
      (Nat.gcd_dvd_right ((m ! : ℕ) ^ (m ! : ℕ) - 1) ((2 * m) !))
  have hp_le_2m : p ≤ 2 * m := hp.dvd_factorial.mp hB
  have hm_lt_p : m < p := by
    by_contra hnot
    have hplem : p ≤ m := le_of_not_gt hnot
    have hp_dvd_fact : p ∣ m ! := hp.dvd_factorial.mpr hplem
    have hp_dvd_X : p ∣ X := dvd_pow hp_dvd_fact (Nat.factorial_ne_zero m)
    have hsub : X - (X - 1) = 1 := by
      have hXpos : 0 < X := pow_pos (Nat.factorial_pos m) _
      omega
    have hp_dvd_one : p ∣ 1 := by
      simpa [hsub] using Nat.dvd_sub hp_dvd_X hA
    exact hp.not_dvd_one hp_dvd_one
  have hp_lt_2m : p < 2 * m := by
    refine lt_of_le_of_ne hp_le_2m ?_
    intro hp_eq
    have hp_even : Even p := by
      rw [hp_eq]
      exact even_two_mul m
    have : p = 2 := hp.even_iff.mp hp_even
    omega
  exact ⟨hm_lt_p, hp_lt_2m⟩

lemma factorization_two_mul_factorial_eq_one_of_between {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hmp : m < p) (hp2m : p < 2 * m) :
    ((2 * m) !).factorization p = 1 := by
  have hlog : Nat.log p (2 * m) < 2 := by
    apply Nat.log_lt_of_lt_pow (by omega : 2 * m ≠ 0)
    have hp_sq : 2 * m < p ^ 2 := by
      nlinarith [hm, hmp]
    simpa [pow_two] using hp_sq
  rw [Nat.factorization_factorial hp hlog]
  have hdiv : 2 * m / p = 1 := by
    apply Nat.div_eq_of_lt_le (k := 1) (n := p) (m := 2 * m)
    · omega
    · omega
  rw [show (2 : ℕ) = 1 + 1 by norm_num]
  rw [Finset.sum_Ico_succ_top (by norm_num : 1 ≤ 1)]
  simp [hdiv]

lemma firstGcd_squarefree {m : ℕ} (hm : 3 ≤ m) :
    Squarefree (firstGcd m) := by
  apply Nat.squarefree_of_factorization_le_one (firstGcd_pos m).ne'
  intro q
  by_cases hq : q.Prime
  · by_cases hqd : q ∣ firstGcd m
    · have hleB :
          (firstGcd m).factorization q ≤ (((2 * m) !).factorization q) := by
        have hdvdB : firstGcd m ∣ (2 * m) ! := by
          simpa [firstGcd] using
            Nat.gcd_dvd_right ((m ! : ℕ) ^ (m ! : ℕ) - 1) ((2 * m) !)
        exact ((Nat.factorization_le_iff_dvd
          (firstGcd_pos m).ne' (Nat.factorial_ne_zero (2 * m))).2 hdvdB) q
      have hbetween := between_of_prime_dvd_firstGcd hm hq hqd
      exact hleB.trans_eq
        (factorization_two_mul_factorial_eq_one_of_between hm hq hbetween.1 hbetween.2)
    · have hzero : (firstGcd m).factorization q = 0 :=
        (Nat.factorization_eq_zero_iff _ _).2 (Or.inr (Or.inl hqd))
      omega
  · have hzero : (firstGcd m).factorization q = 0 :=
      (Nat.factorization_eq_zero_iff _ _).2 (Or.inl hq)
    omega

lemma firstGcd_ne_one {m : ℕ} (hm : 3 ≤ m) :
    firstGcd m ≠ 1 := by
  obtain ⟨p, hp, hmp, hp2m⟩ := bertrand_strict (by omega : 2 ≤ m)
  have hpd : p ∣ firstGcd m := prime_dvd_firstGcd_of_between hm hp hmp hp2m
  intro hd
  rw [hd] at hpd
  exact hp.not_dvd_one hpd

lemma minFac_firstGcd_prime {m : ℕ} (hm : 3 ≤ m) :
    (firstGcd m).minFac.Prime :=
  Nat.minFac_prime (firstGcd_ne_one hm)

lemma minFac_firstGcd_dvd {m : ℕ} :
    (firstGcd m).minFac ∣ firstGcd m :=
  Nat.minFac_dvd (firstGcd m)

lemma minFac_firstGcd_between {m : ℕ} (hm : 3 ≤ m) :
    m < (firstGcd m).minFac ∧ (firstGcd m).minFac < 2 * m :=
  between_of_prime_dvd_firstGcd hm (minFac_firstGcd_prime hm) minFac_firstGcd_dvd

lemma exponentFilterT_factorization_of_prime_dvd_firstGcd {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hpd : p ∣ firstGcd m) :
    (exponentFilterT (firstGcd m)).factorization p =
      firstGcd m - ((firstGcd m) !).factorization p := by
  let d := firstGcd m
  have hdpos : 0 < d := firstGcd_pos m
  have hdne : d ≠ 0 := hdpos.ne'
  have hsquare : Squarefree d := by
    simpa [d] using firstGcd_squarefree hm
  have hfacd : d.factorization p = 1 :=
    Nat.factorization_eq_one_of_squarefree hsquare hp (by simpa [d] using hpd)
  have hbetween := between_of_prime_dvd_firstGcd hm hp hpd
  have hf_lt_d : (d !).factorization p < d := by
    have hf_le : (d !).factorization p ≤ d / (p - 1) :=
      Nat.factorization_factorial_le_div_pred hp d
    exact hf_le.trans_lt (Nat.div_lt_self hdpos (by omega))
  unfold exponentFilterT
  change (d ^ d / Nat.gcd (d ^ d) (d !)).factorization p =
    d - (d !).factorization p
  rw [Nat.factorization_div (Nat.gcd_dvd_left (d ^ d) (d !))]
  rw [Nat.factorization_gcd (pow_ne_zero d hdne) (Nat.factorial_ne_zero d)]
  rw [Nat.factorization_pow]
  simp [hfacd, hf_lt_d.le]

lemma factorial_factorization_lt_at_non_minFac {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hpd : p ∣ firstGcd m)
    (hp_ne_min : p ≠ (firstGcd m).minFac) :
    ((firstGcd m) !).factorization p <
      ((firstGcd m) !).factorization (firstGcd m).minFac := by
  let d := firstGcd m
  let q := d.minFac
  have hdpos : 0 < d := firstGcd_pos m
  have hqprime : q.Prime := by
    simpa [d, q] using minFac_firstGcd_prime hm
  have hqdvd : q ∣ d := by
    simpa [d, q] using Nat.minFac_dvd d
  have hpbetween := between_of_prime_dvd_firstGcd hm hp hpd
  have hqbetween : m < q ∧ q < 2 * m := by
    simpa [d, q] using minFac_firstGcd_between hm
  have hqle : q ≤ p := Nat.minFac_le_of_dvd hp.two_le (by simpa [d] using hpd)
  have hq_lt_p : q < p := lt_of_le_of_ne hqle (by simpa [d, q] using hp_ne_min.symm)
  have hq_lt_pred : q < p - 1 := by
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
    rcases hpodd with ⟨a, ha⟩
    rcases hqodd with ⟨b, hb⟩
    omega
  have hq_lower : d / q ≤ (d !).factorization q := by
    have hmul : q * (d / q) = d := Nat.mul_div_cancel' hqdvd
    calc
      d / q ≤ ((d / q) !).factorization q + d / q := Nat.le_add_left _ _
      _ = ((q * (d / q)) !).factorization q :=
        (Nat.factorization_factorial_mul hqprime).symm
      _ = (d !).factorization q := by rw [hmul]
  have hp_upper : (d !).factorization p ≤ d / (p - 1) :=
    Nat.factorization_factorial_le_div_pred hp d
  have hdivlt : d / (p - 1) < d / q := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < p - 1)]
    have hdqpos : 0 < d / q := Nat.div_pos (Nat.le_of_dvd hdpos hqdvd) hqprime.pos
    calc
      d = q * (d / q) := (Nat.mul_div_cancel' hqdvd).symm
      _ < (d / q) * (p - 1) := by nlinarith
  exact hp_upper.trans_lt (hdivlt.trans_le hq_lower)

lemma exponentFilterT_minFac_factorization {m : ℕ} (hm : 3 ≤ m) :
    (exponentFilterT (firstGcd m)).factorization (firstGcd m).minFac =
      minExponent m := by
  unfold minExponent
  exact exponentFilterT_factorization_of_prime_dvd_firstGcd hm
    (minFac_firstGcd_prime hm) minFac_firstGcd_dvd

lemma minExponent_pos {m : ℕ} (hm : 3 ≤ m) :
    0 < minExponent m := by
  unfold minExponent
  have hdpos : 0 < firstGcd m := firstGcd_pos m
  have hf_le :
      ((firstGcd m) !).factorization (firstGcd m).minFac ≤
        firstGcd m / ((firstGcd m).minFac - 1) :=
    Nat.factorization_factorial_le_div_pred (minFac_firstGcd_prime hm) (firstGcd m)
  have hf_lt :
      ((firstGcd m) !).factorization (firstGcd m).minFac < firstGcd m :=
    hf_le.trans_lt (Nat.div_lt_self hdpos (by
      have hbetween := minFac_firstGcd_between hm
      omega))
  omega

lemma exponentFilterT_pos {m : ℕ} (hm : 3 ≤ m) :
    0 < exponentFilterT (firstGcd m) := by
  by_contra hnot
  have ht0 : exponentFilterT (firstGcd m) = 0 := Nat.eq_zero_of_not_pos hnot
  have hfac := exponentFilterT_minFac_factorization hm
  rw [ht0] at hfac
  have hpos := minExponent_pos hm
  simp at hfac
  omega

lemma exponentFilterT_non_minFac_factorization_gt {m p : ℕ}
    (hm : 3 ≤ m) (hp : p.Prime) (hpd : p ∣ firstGcd m)
    (hp_ne_min : p ≠ (firstGcd m).minFac) :
    minExponent m <
      (exponentFilterT (firstGcd m)).factorization p := by
  unfold minExponent
  rw [exponentFilterT_factorization_of_prime_dvd_firstGcd hm hp hpd]
  have hlt := factorial_factorization_lt_at_non_minFac hm hp hpd hp_ne_min
  have hbetween := minFac_firstGcd_between hm
  have hdpos : 0 < firstGcd m := firstGcd_pos m
  have hfq_lt_d : ((firstGcd m) !).factorization (firstGcd m).minFac < firstGcd m := by
    have hf_le :
        ((firstGcd m) !).factorization (firstGcd m).minFac ≤
          firstGcd m / ((firstGcd m).minFac - 1) :=
      Nat.factorization_factorial_le_div_pred (minFac_firstGcd_prime hm) (firstGcd m)
    exact hf_le.trans_lt (Nat.div_lt_self hdpos (by omega))
  omega

lemma firstGcd_pow_minExponent_dvd_exponentFilterT {m : ℕ} (hm : 3 ≤ m) :
    firstGcd m ^ minExponent m ∣ exponentFilterT (firstGcd m) := by
  let d := firstGcd m
  let t := exponentFilterT d
  have hdne : d ≠ 0 := (firstGcd_pos m).ne'
  have htpos : 0 < t := by simpa [t, d] using exponentFilterT_pos hm
  have htne : t ≠ 0 := htpos.ne'
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hdne) htne]
  intro r
  rw [Nat.factorization_pow]
  by_cases hrp : r.Prime
  · by_cases hrd : r ∣ d
    · have hfacd : d.factorization r = 1 := by
        exact Nat.factorization_eq_one_of_squarefree
          (by simpa [d] using firstGcd_squarefree hm) hrp (by simpa [d] using hrd)
      by_cases hrq : r = d.minFac
      · subst r
        simp [hfacd, d, t, exponentFilterT_minFac_factorization hm]
      · have hgt : minExponent m < t.factorization r := by
          simpa [d, t] using
            exponentFilterT_non_minFac_factorization_gt hm hrp (by simpa [d] using hrd)
              (by simpa [d] using hrq)
        simp [hfacd]
        exact hgt.le
    · have hfacd : d.factorization r = 0 :=
        (Nat.factorization_eq_zero_iff _ _).2 (Or.inr (Or.inl hrd))
      simp [hfacd]
  · have hfacd : d.factorization r = 0 :=
      (Nat.factorization_eq_zero_iff _ _).2 (Or.inl hrp)
    simp [hfacd]

lemma largestDPowerDividing_eq_minExponent {m : ℕ} (hm : 3 ≤ m) :
    largestDPowerDividing (firstGcd m) (exponentFilterT (firstGcd m)) =
      minExponent m := by
  let d := firstGcd m
  let t := exponentFilterT d
  let P : ℕ → Prop := fun a => d ^ a ∣ t
  have hdne : d ≠ 0 := (firstGcd_pos m).ne'
  have htpos : 0 < t := by simpa [t, d] using exponentFilterT_pos hm
  have htne : t ≠ 0 := htpos.ne'
  have hPmin : P (minExponent m) := by
    simpa [P, d, t] using firstGcd_pow_minExponent_dvd_exponentFilterT hm
  have hdgt1 : 1 < d := by
    have hdpos : 0 < d := by simpa [d] using firstGcd_pos m
    have hdne1 : d ≠ 1 := by simpa [d] using firstGcd_ne_one hm
    omega
  have hmin_le_pow : minExponent m ≤ d ^ minExponent m := by
    cases minExponent m with
    | zero => simp
    | succ e =>
        exact le_of_lt (Nat.lt_pow_self hdgt1)
  have hpow_le_t : d ^ minExponent m ≤ t := Nat.le_of_dvd htpos hPmin
  have hmin_le_t : minExponent m ≤ t := hmin_le_pow.trans hpow_le_t
  unfold largestDPowerDividing
  change Nat.findGreatest P t = minExponent m
  apply le_antisymm
  · by_contra hnot
    have hgt : minExponent m < Nat.findGreatest P t := Nat.lt_of_not_ge hnot
    have hPfg : P (Nat.findGreatest P t) :=
      Nat.findGreatest_spec (m := 0) (n := t) (P := P) (Nat.zero_le t) (by simp [P])
    let q := d.minFac
    have hqprime : q.Prime := by simpa [d, q] using minFac_firstGcd_prime hm
    have hqdvd : q ∣ d := by simpa [d, q] using Nat.minFac_dvd d
    have hfacd : d.factorization q = 1 :=
      Nat.factorization_eq_one_of_squarefree
        (by simpa [d] using firstGcd_squarefree hm) hqprime hqdvd
    have htq : t.factorization q = minExponent m := by
      simpa [d, t, q] using exponentFilterT_minFac_factorization hm
    have hfac_le :
        (d ^ Nat.findGreatest P t).factorization q ≤ t.factorization q :=
      ((Nat.factorization_le_iff_dvd (pow_ne_zero _ hdne) htne).2 hPfg) q
    rw [Nat.factorization_pow] at hfac_le
    simp [hfacd, htq] at hfac_le
    omega
  · exact Nat.le_findGreatest (P := P) hmin_le_t hPmin

lemma gcd_after_removing_minExponent_eq_div_minFac {m : ℕ} (hm : 3 ≤ m) :
    Nat.gcd
        (exponentFilterT (firstGcd m) / firstGcd m ^ minExponent m)
        (firstGcd m) =
      firstGcd m / (firstGcd m).minFac := by
  let d := firstGcd m
  let t := exponentFilterT d
  let e := minExponent m
  let q := d.minFac
  have hdpos : 0 < d := by simpa [d] using firstGcd_pos m
  have hdne : d ≠ 0 := hdpos.ne'
  have htpos : 0 < t := by simpa [t, d] using exponentFilterT_pos hm
  have hpowdvd : d ^ e ∣ t := by
    simpa [d, t, e] using firstGcd_pow_minExponent_dvd_exponentFilterT hm
  have hpowpos : 0 < d ^ e := pow_pos hdpos e
  have hupos : 0 < t / d ^ e :=
    Nat.div_pos (Nat.le_of_dvd htpos hpowdvd) hpowpos
  have hune : t / d ^ e ≠ 0 := hupos.ne'
  have hqprime : q.Prime := by simpa [d, q] using minFac_firstGcd_prime hm
  have hqdvd : q ∣ d := by simpa [d, q] using Nat.minFac_dvd d
  have hdqpos : 0 < d / q := Nat.div_pos (Nat.le_of_dvd hdpos hqdvd) hqprime.pos
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_right _ hdpos).ne' hdqpos.ne'
  intro r
  rw [Nat.factorization_gcd hune hdne]
  rw [Nat.factorization_div hpowdvd]
  rw [Nat.factorization_pow]
  rw [Nat.factorization_div hqdvd]
  by_cases hrp : r.Prime
  · by_cases hrd : r ∣ d
    · have hfacd : d.factorization r = 1 :=
        Nat.factorization_eq_one_of_squarefree
          (by simpa [d] using firstGcd_squarefree hm) hrp hrd
      by_cases hrq : r = q
      · subst r
        have htq : t.factorization q = e := by
          simpa [d, t, e, q] using exponentFilterT_minFac_factorization hm
        simp [hfacd, htq, hqprime.factorization]
      · have hgt : e < t.factorization r := by
          simpa [d, t, e, q] using
            exponentFilterT_non_minFac_factorization_gt hm hrp (by simpa [d] using hrd)
              (by simpa [d, q] using hrq)
        simp [hfacd, hqprime.factorization, hrq]
        omega
    · have hfacd : d.factorization r = 0 :=
        (Nat.factorization_eq_zero_iff _ _).2 (Or.inr (Or.inl hrd))
      simp [hfacd]
  · have hfacd : d.factorization r = 0 :=
      (Nat.factorization_eq_zero_iff _ _).2 (Or.inl hrp)
    simp [hfacd, hqprime.factorization, hrp]

lemma div_firstGcd_by_div_minFac {m : ℕ} (hm : 3 ≤ m) :
    firstGcd m / (firstGcd m / (firstGcd m).minFac) =
      (firstGcd m).minFac := by
  let d := firstGcd m
  let q := d.minFac
  have hdpos : 0 < d := by simpa [d] using firstGcd_pos m
  have hqprime : q.Prime := by simpa [d, q] using minFac_firstGcd_prime hm
  have hqdvd : q ∣ d := by simpa [d, q] using Nat.minFac_dvd d
  have hdqpos : 0 < d / q := Nat.div_pos (Nat.le_of_dvd hdpos hqdvd) hqprime.pos
  change d / (d / q) = q
  exact Nat.div_eq_of_eq_mul_left hdqpos (Nat.mul_div_cancel' hqdvd).symm

theorem extractedPrime_eq_minFac {m : ℕ} (hm : 3 ≤ m) :
    extractedPrime m = (firstGcd m).minFac := by
  simp [extractedPrime, largestDPowerDividing_eq_minExponent hm,
    gcd_after_removing_minExponent_eq_div_minFac hm, div_firstGcd_by_div_minFac hm]

theorem minFac_firstGcd_is_smallest_prime_gt {m : ℕ} (hm : 3 ≤ m) :
    (firstGcd m).minFac.Prime ∧
      m < (firstGcd m).minFac ∧
      ∀ p : ℕ, p.Prime → m < p → (firstGcd m).minFac ≤ p := by
  refine ⟨minFac_firstGcd_prime hm, (minFac_firstGcd_between hm).1, ?_⟩
  intro p hp hmp
  by_cases hp2m : p < 2 * m
  · exact Nat.minFac_le_of_dvd hp.two_le
      (prime_dvd_firstGcd_of_between hm hp hmp hp2m)
  · have hq2m := (minFac_firstGcd_between hm).2
    omega

theorem extractedPrime_is_smallest_prime_gt {m : ℕ} (hm : 3 ≤ m) :
    (extractedPrime m).Prime ∧
      m < extractedPrime m ∧
      ∀ p : ℕ, p.Prime → m < p → extractedPrime m ≤ p := by
  rw [extractedPrime_eq_minFac hm]
  exact minFac_firstGcd_is_smallest_prime_gt hm

end ExtractingFirstPrime
