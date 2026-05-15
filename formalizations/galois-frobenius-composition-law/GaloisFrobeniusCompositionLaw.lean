import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Tactic

/-!
# Separated polynomial composition

This file formalizes the main polynomial composition criterion from
`galois_frobenius_composition_law.tex`.

The main composition criterion is proved by polynomial division in an iterated
polynomial ring.  The surrounding lemmas formalize the Frobenius and basic
Galois-descent steps used in the note's proof strategy.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace SeparatedComposition

variable {k : Type*} [Field k]

def subst (q : k[X]) : k[X] →+* k[X] :=
  (Polynomial.aeval q : k[X] →ₐ[k] k[X]).toRingHom

@[simp] lemma subst_apply (q p : k[X]) : subst q p = p.comp q := by
  simp [subst, comp_eq_aeval]

@[simp] lemma subst_comp_C (q : k[X]) : (subst q).comp C = C := by
  ext c
  simp [subst]

theorem expand_comp_X_pow_injective {p : Nat} (hp : 0 < p) :
    Function.Injective (fun R : k[X] => R.comp ((X : k[X]) ^ p)) := by
  intro R S h
  have h' : (expand k p) R = (expand k p) S := by
    simpa [Polynomial.expand_eq_comp_X_pow] using h
  exact Polynomial.expand_injective (R := k) hp h'

theorem zero_derivative_iff_expand {p : Nat} [CharP k p] (hp : Ne p 0) (R : k[X]) :
    derivative R = 0 ↔ ∃ R1 : k[X], R = R1.comp ((X : k[X]) ^ p) := by
  constructor
  · intro hR
    refine ⟨Polynomial.contract p R, ?_⟩
    change R = (expand k p) (Polynomial.contract p R)
    exact (Polynomial.expand_contract p hR hp).symm
  · rintro ⟨R1, hR1⟩
    rw [hR1]
    change derivative ((expand k p) R1) = 0
    rw [Polynomial.derivative_expand]
    simp [CharP.cast_eq_zero]

theorem zero_derivative_iff_existsUnique_expand {p : Nat} [CharP k p] (hp : Ne p 0)
    (R : k[X]) :
    derivative R = 0 ↔ ∃! R1 : k[X], R = R1.comp ((X : k[X]) ^ p) := by
  constructor
  · intro hR
    let R0 := Polynomial.contract p R
    have hR0 : R = R0.comp ((X : k[X]) ^ p) := by
      change R = (expand k p) R0
      exact (Polynomial.expand_contract p hR hp).symm
    refine ExistsUnique.intro R0 hR0 ?_
    intro R2 hR2
    exact expand_comp_X_pow_injective (k := k) (Nat.pos_of_ne_zero hp) (hR2.symm.trans hR0)
  · rintro ⟨R1, hR1, _⟩
    exact (zero_derivative_iff_expand (k := k) hp R).mpr ⟨R1, hR1⟩

theorem frobenius_divisibility_descent_expand
    {R : Type*} [CommSemiring R] {p : Nat} (hp : Ne p 0) {D E : R[X]} :
    expand R p D ∣ expand R p E → D ∣ E := by
  rintro ⟨A, hA⟩
  refine ⟨Polynomial.contract p A, ?_⟩
  rw [mul_comm] at hA
  have hcontract := congrArg (Polynomial.contract p) hA
  rw [Polynomial.contract_expand p hp, Polynomial.contract_mul_expand hp A D] at hcontract
  simpa [mul_comm] using hcontract

lemma comp_eq_zero_iff_of_natDegree_pos {p q : k[X]} (hq : 0 < q.natDegree) :
    p.comp q = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    have hp_comp : p.comp q ≠ 0 := by
      by_cases hpdeg : p.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hpdeg]
        rw [eq_C_of_natDegree_eq_zero hpdeg] at hp
        simpa using hp
      · have hpos : 0 < p.natDegree := Nat.pos_of_ne_zero hpdeg
        intro hzero
        have hdeg := congrArg natDegree hzero
        rw [natDegree_comp, natDegree_zero] at hdeg
        exact Nat.ne_of_gt (Nat.mul_pos hpos hq) hdeg
    exact hp_comp h
  · intro h
    simp [h]

lemma comp_right_injective_of_natDegree_pos {q : k[X]} (hq : 0 < q.natDegree) :
    Function.Injective fun p : k[X] => p.comp q := by
  intro p r h
  have hz : (p - r).comp q = 0 := by
    simp [sub_comp, h]
  have : p - r = 0 := (comp_eq_zero_iff_of_natDegree_pos hq).mp hz
  exact sub_eq_zero.mp this

lemma map_aeval_injective_of_natDegree_pos {q : k[X]} (hq : 0 < q.natDegree) :
    Function.Injective (subst q) := by
  intro p r h
  exact comp_right_injective_of_natDegree_pos hq (by simpa using h)

lemma coeff_map_aeval_eq_zero_of_map_eq_C
    {q : k[X]} (hq : 0 < q.natDegree) {R : k[X][X]} {Q : k[X]} {n : ℕ}
    (hR : R.map (subst q) = C Q) (hn : n ≠ 0) :
    R.coeff n = 0 := by
  apply map_aeval_injective_of_natDegree_pos hq
  have hc := congrArg (fun P : k[X][X] => P.coeff n) hR
  simpa [coeff_map, coeff_C, hn] using hc

lemma eq_C_of_map_aeval_eq_C
    {q : k[X]} (hq : 0 < q.natDegree) {R : k[X][X]} {Q : k[X]}
    (hR : R.map (subst q) = C Q) :
    R = C (R.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [coeff_C, hn, coeff_map_aeval_eq_zero_of_map_eq_C hq hR hn]

lemma map_C_eval₂_X (P : k[X]) :
    eval₂ (subst (X : k[X])) (X : k[X]) (P.map C : k[X][X]) = P := by
  rw [eval₂_map]
  rw [subst_comp_C]
  exact
    (Polynomial.eval₂_algebraMap_X (R := k) (A := k[X]) P (AlgHom.id k k[X]))

lemma eval₂_map_C (P F : k[X]) :
    eval₂ (subst F) (X : k[X]) (P.map C : k[X][X]) = P := by
  rw [eval₂_map]
  rw [subst_comp_C]
  exact
    (Polynomial.eval₂_algebraMap_X (R := k) (A := k[X]) P (AlgHom.id k k[X]))

lemma eval₂_C_subst (A F : k[X]) :
    eval₂ (subst F) (X : k[X]) (C A : k[X][X]) = A.comp F := by
  simp

def genericDivisor (F : k[X]) : k[X][X] :=
  F.map C - C (X : k[X])

def separatedDivisor (F G : k[X]) : k[X][X] :=
  F.map C - C G

def outerRemainder (g f : k[X]) : k[X][X] :=
  (f.map C : k[X][X]) %ₘ genericDivisor g

def normalizedGenericDivisor (g : k[X]) : k[X][X] :=
  C (C g.leadingCoeff⁻¹) * genericDivisor g

def normalizedOuterRemainder (g f : k[X]) : k[X][X] :=
  (f.map C : k[X][X]) %ₘ normalizedGenericDivisor g

def genericFiberRatFunc (F : k[X]) : (RatFunc k)[X] :=
  (genericDivisor F).map (algebraMap k[X] (RatFunc k))

section BivariateEvaluation

variable {L : Type*} [CommRing L] [Algebra k L]

lemma eval₂_map_C_aeval (P : k[X]) (x y : L) :
    eval₂ ((Polynomial.aeval x : k[X] →ₐ[k] L).toRingHom) y (P.map C : k[X][X]) =
      Polynomial.aeval y P := by
  rw [eval₂_map]
  change eval₂ ((Polynomial.aeval x).toRingHom.comp C) y P = Polynomial.aeval y P
  rw [show ((Polynomial.aeval x).toRingHom.comp C : k →+* L) = algebraMap k L by
    ext a
    simp]
  rfl

lemma eval₂_C_aeval (Q : k[X]) (x y : L) :
    eval₂ ((Polynomial.aeval x : k[X] →ₐ[k] L).toRingHom) y (C Q : k[X][X]) =
      Polynomial.aeval x Q := by
  simp

lemma eval₂_separatedDivisor (F G : k[X]) (x y : L) :
    eval₂ ((Polynomial.aeval x : k[X] →ₐ[k] L).toRingHom) y (separatedDivisor F G) =
      Polynomial.aeval y F - Polynomial.aeval x G := by
  unfold separatedDivisor
  rw [eval₂_sub, eval₂_map_C_aeval, eval₂_C_aeval]

lemma eval₂_separatedTarget (P Q : k[X]) (x y : L) :
    eval₂ ((Polynomial.aeval x : k[X] →ₐ[k] L).toRingHom) y ((P.map C : k[X][X]) - C Q) =
      Polynomial.aeval y P - Polynomial.aeval x Q := by
  rw [eval₂_sub, eval₂_map_C_aeval, eval₂_C_aeval]

lemma separated_divisibility_aeval_eq
    {F G P Q : k[X]} {x y : L}
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q)
    (hfiber : Polynomial.aeval y F = Polynomial.aeval x G) :
    Polynomial.aeval y P = Polynomial.aeval x Q := by
  obtain ⟨A, hA⟩ := hdiv
  have hDzero :
      eval₂ ((Polynomial.aeval x : k[X] →ₐ[k] L).toRingHom) y (separatedDivisor F G) = 0 := by
    rw [eval₂_separatedDivisor, hfiber, sub_self]
  have htarget :
      eval₂ ((Polynomial.aeval x : k[X] →ₐ[k] L).toRingHom) y
          ((P.map C : k[X][X]) - C Q) = 0 := by
    rw [hA, eval₂_mul, hDzero, zero_mul]
  rw [eval₂_separatedTarget] at htarget
  exact sub_eq_zero.mp htarget

end BivariateEvaluation

section GaloisDescent

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

lemma algEquiv_apply_aeval (σ : L ≃ₐ[K] L) (x : L) (P : K[X]) :
    σ (Polynomial.aeval x P) = Polynomial.aeval (σ x) P := by
  simpa using (Polynomial.aeval_algHom_apply (σ : L →ₐ[K] L) x P).symm

lemma aeval_fixed_of_fixed (P : K[X]) {x : L}
    (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∀ σ : L ≃ₐ[K] L, σ (Polynomial.aeval x P) = Polynomial.aeval x P := by
  intro σ
  rw [algEquiv_apply_aeval, hx σ]

lemma galois_fixed_iff_mem_range [IsGalois K L] [FiniteDimensional K L] (x : L) :
    x ∈ Set.range (algebraMap K L) ↔ ∀ σ : L ≃ₐ[K] L, σ x = x := by
  simpa using (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) x)

lemma galois_fixed_descends [IsGalois K L] [FiniteDimensional K L] {x : L}
    (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∃ a : K, algebraMap K L a = x := by
  simpa [Set.mem_range] using (galois_fixed_iff_mem_range (K := K) (L := L) x).mpr hx

lemma galois_descends_of_aeval_conjugates
    [IsGalois K L] [FiniteDimensional K L] (P : K[X]) (x : L)
    (hx : ∀ σ : L ≃ₐ[K] L,
      Polynomial.aeval (σ x) P = Polynomial.aeval x P) :
    ∃ a : K, algebraMap K L a = Polynomial.aeval x P := by
  apply galois_fixed_descends
  intro σ
  rw [algEquiv_apply_aeval]
  exact hx σ

lemma separated_divisibility_conjugate_aeval_eq
    {F G P Q : K[X]} {α β : L}
    (hdiv : separatedDivisor F G ∣ (P.map C : K[X][X]) - C Q)
    (hfiber : Polynomial.aeval α F = Polynomial.aeval β G)
    (σ : L ≃ₐ[K] L) :
    Polynomial.aeval (σ α) P = Polynomial.aeval (σ β) Q := by
  have hfiberσ : Polynomial.aeval (σ α) F = Polynomial.aeval (σ β) G := by
    have h := congrArg σ hfiber
    rwa [algEquiv_apply_aeval, algEquiv_apply_aeval] at h
  exact separated_divisibility_aeval_eq (k := K) (L := L) (x := σ β) (y := σ α)
    hdiv hfiberσ

lemma galois_descends_from_separated_conjugates
    [IsGalois K L] [FiniteDimensional K L]
    {F G P Q : K[X]} {α β : L}
    (hdiv : separatedDivisor F G ∣ (P.map C : K[X][X]) - C Q)
    (hfiber : Polynomial.aeval α F = Polynomial.aeval β G)
    (hQconstant : ∀ σ : L ≃ₐ[K] L,
      Polynomial.aeval (σ β) Q = Polynomial.aeval β Q) :
    ∃ a : K, algebraMap K L a = Polynomial.aeval α P := by
  apply galois_fixed_descends
  intro σ
  rw [algEquiv_apply_aeval]
  have hconj := separated_divisibility_conjugate_aeval_eq
    (K := K) (L := L) hdiv hfiber σ
  have hbase := separated_divisibility_aeval_eq
    (k := K) (L := L) (x := β) (y := α) hdiv hfiber
  exact hconj.trans ((hQconstant σ).trans hbase.symm)

end GaloisDescent

section IntegralityDescent

variable {R Frac : Type*} [CommRing R] [CommRing Frac] [Algebra R Frac]
  [IsFractionRing R Frac]

lemma integral_fraction_field_descends [IsIntegrallyClosed R] {x : Frac}
    (hx : IsIntegral R x) :
    ∃ r : R, algebraMap R Frac r = x :=
  IsIntegrallyClosed.algebraMap_eq_of_integral hx

lemma isIntegral_aeval_of_isIntegral {A : Type*} [CommRing A] [Algebra R A]
    {x : A} (hx : IsIntegral R x) (P : R[X]) :
    IsIntegral R (Polynomial.aeval x P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa using IsIntegral.add hP hQ
  | monomial n a =>
      simpa [Polynomial.aeval_monomial] using
        IsIntegral.mul (isIntegral_algebraMap (A := A) (x := a))
        (IsIntegral.pow hx n)

lemma isIntegral_aeval_of_isIntegral_base {A : Type*} [CommRing A]
    [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A]
    {x : A} (hx : IsIntegral k[X] x) (P : k[X]) :
    IsIntegral k[X] (Polynomial.aeval x P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa using IsIntegral.add hP hQ
  | monomial n a =>
      have ha : IsIntegral k[X] (algebraMap k A a) := by
        rw [IsScalarTower.algebraMap_apply k k[X] A a]
        exact isIntegral_algebraMap
      simpa [Polynomial.aeval_monomial] using
        IsIntegral.mul ha (IsIntegral.pow hx n)

lemma isIntegral_of_monic_aeval_eq_zero {A : Type*} [CommRing A] [Algebra R A]
    {P : R[X]} (hP : P.Monic) {x : A} (hx : Polynomial.aeval x P = 0) :
    IsIntegral R x :=
  ⟨P, hP, hx⟩

lemma integral_aeval_fraction_field_descends [IsIntegrallyClosed R] {x : Frac}
    (hx : IsIntegral R x) (P : R[X]) :
    ∃ r : R, algebraMap R Frac r = Polynomial.aeval x P :=
  integral_fraction_field_descends (isIntegral_aeval_of_isIntegral hx P)

lemma integral_ratFunc_descends (x : RatFunc k)
    (hx : IsIntegral k[X] x) :
    ∃ P : k[X], algebraMap k[X] (RatFunc k) P = x :=
  integral_fraction_field_descends (R := k[X]) (Frac := RatFunc k) hx

lemma integral_aeval_ratFunc_descends {x : RatFunc k}
    (hx : IsIntegral k[X] x) (P : k[X][X]) :
    ∃ Q : k[X], algebraMap k[X] (RatFunc k) Q = Polynomial.aeval x P :=
  integral_aeval_fraction_field_descends (R := k[X]) (Frac := RatFunc k) hx P

lemma galois_fixed_integral_ratFunc_descends
    {L : Type*} [Field L] [Algebra (RatFunc k) L]
    [Algebra k[X] L] [IsScalarTower k[X] (RatFunc k) L]
    [IsGalois (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    {z : L}
    (hfixed : ∀ σ : L ≃ₐ[RatFunc k] L, σ z = z)
    (hintegral : IsIntegral k[X] z) :
    ∃ P : k[X], algebraMap k[X] L P = z := by
  obtain ⟨r, hr⟩ := galois_fixed_descends (K := RatFunc k) (L := L) hfixed
  have hrint : IsIntegral k[X] r := by
    rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective (RatFunc k) L)]
    simpa [hr] using hintegral
  obtain ⟨P, hP⟩ := integral_ratFunc_descends (k := k) r hrint
  refine ⟨P, ?_⟩
  calc
    algebraMap k[X] L P =
        algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) P) := by
      rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) L P]
    _ = algebraMap (RatFunc k) L r := by rw [hP]
    _ = z := hr

end IntegralityDescent

section GenericFiberGaloisBridge

variable {L : Type*} [Field L]
  [Algebra k L] [Algebra k[X] L] [Algebra (RatFunc k) L]
  [IsScalarTower k k[X] L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L]

omit [Algebra k L] [IsScalarTower k k[X] L] [IsScalarTower k (RatFunc k) L] in
lemma ratFunc_parameter_fixed (σ : L ≃ₐ[RatFunc k] L) :
    σ (algebraMap k[X] L (X : k[X])) = algebraMap k[X] L (X : k[X]) := by
  calc
    σ (algebraMap k[X] L (X : k[X])) =
        σ (algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) (X : k[X]))) := by
      rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) L]
    _ = algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) (X : k[X])) := by
      simp
    _ = algebraMap k[X] L (X : k[X]) := by
      rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) L]

omit [Algebra k[X] L] [IsScalarTower k k[X] L] [IsScalarTower k[X] (RatFunc k) L] in
lemma ratFuncAlgEquiv_apply_aeval_k (σ : L ≃ₐ[RatFunc k] L) (x : L) (P : k[X]) :
    σ (Polynomial.aeval x P) = Polynomial.aeval (σ x) P := by
  simpa using
    (algEquiv_apply_aeval (K := k) (L := L) (σ := (σ.restrictScalars k : L ≃ₐ[k] L))
      x P)

omit [IsScalarTower k k[X] L] in
lemma generic_fiber_relation_conjugate
    {F : k[X]} {α : L}
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X]))
    (σ : L ≃ₐ[RatFunc k] L) :
    Polynomial.aeval (σ α) F = algebraMap k[X] L (X : k[X]) := by
  calc
    Polynomial.aeval (σ α) F = σ (Polynomial.aeval α F) := by
      rw [ratFuncAlgEquiv_apply_aeval_k]
    _ = σ (algebraMap k[X] L (X : k[X])) := by rw [hα]
    _ = algebraMap k[X] L (X : k[X]) := ratFunc_parameter_fixed σ

omit [Algebra k L] [IsScalarTower k k[X] L] [IsScalarTower k (RatFunc k) L] in
lemma algebraMap_polynomial_to_ratFunc_extension_injective :
    Function.Injective (algebraMap k[X] L) := by
  intro P Q hPQ
  apply IsFractionRing.injective k[X] (RatFunc k)
  apply FaithfulSMul.algebraMap_injective (RatFunc k) L
  calc
    algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) P) =
        algebraMap k[X] L P := by
      rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) L P]
    _ = algebraMap k[X] L Q := hPQ
    _ = algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) Q) := by
      rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) L Q]

omit [IsScalarTower k (RatFunc k) L] in
lemma generic_root_transcendental
    {F : k[X]} {α : L}
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X])) :
    Transcendental k α := by
  have hinj : Function.Injective (algebraMap k[X] L) :=
    algebraMap_polynomial_to_ratFunc_extension_injective (k := k) (L := L)
  have hX : Transcendental k (algebraMap k[X] L (X : k[X])) :=
    (transcendental_algebraMap_iff hinj).mpr (Polynomial.transcendental_X k)
  have hFX : Transcendental k (Polynomial.aeval α F) := by
    rwa [hα]
  exact (transcendental_aeval_iff.mp hFX).1

omit [IsScalarTower k (RatFunc k) L] in
lemma generic_root_aeval_injective
    {F : k[X]} {α : L}
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X])) :
    Function.Injective (Polynomial.aeval α : k[X] →ₐ[k] L) :=
  transcendental_iff_injective.mp (generic_root_transcendental (k := k) (L := L) hα)

omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L] in
lemma aeval_parameter_eq_algebraMap (S : k[X]) :
    Polynomial.aeval (algebraMap k[X] L (X : k[X])) S = algebraMap k[X] L S := by
  simpa using
    (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k k[X] L) (X : k[X]) S)

omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L] in
lemma aeval_map_C_scalarTower (F : k[X]) (α : L) :
    Polynomial.aeval α (F.map C : k[X][X]) = Polynomial.aeval α F := by
  induction F using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp [Polynomial.map_add, hP, hQ]
  | monomial n a =>
      simp [Polynomial.aeval_monomial, IsScalarTower.algebraMap_apply k k[X] L a]

omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L] in
lemma aeval_genericDivisor_eq (F : k[X]) (α : L) :
    Polynomial.aeval α (genericDivisor F) =
      Polynomial.aeval α F - algebraMap k[X] L (X : k[X]) := by
  unfold genericDivisor
  rw [Polynomial.aeval_sub, aeval_map_C_scalarTower, Polynomial.aeval_C]

omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L] in
lemma aeval_genericDivisor_of_relation
    {F : k[X]} {α : L}
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X])) :
    Polynomial.aeval α (genericDivisor F) = 0 := by
  rw [aeval_genericDivisor_eq, hα, sub_self]

omit [Algebra k L] [IsScalarTower k k[X] L] [IsScalarTower k (RatFunc k) L] in
lemma aeval_genericFiberRatFunc_eq_genericDivisor (F : k[X]) (α : L) :
    Polynomial.aeval α (genericFiberRatFunc F) =
      Polynomial.aeval α (genericDivisor F) := by
  unfold genericFiberRatFunc
  rw [Polynomial.aeval_map_algebraMap]

omit [IsScalarTower k (RatFunc k) L] in
lemma genericFiberRatFunc_root_relation
    {F : k[X]} {α : L}
    (hroot : Polynomial.aeval α (genericFiberRatFunc F) = 0) :
    Polynomial.aeval α F = algebraMap k[X] L (X : k[X]) := by
  have hgeneric : Polynomial.aeval α (genericDivisor F) = 0 := by
    rwa [aeval_genericFiberRatFunc_eq_genericDivisor (k := k) (L := L)] at hroot
  rw [aeval_genericDivisor_eq] at hgeneric
  exact sub_eq_zero.mp hgeneric

omit [IsScalarTower k (RatFunc k) L] in
lemma polynomial_identity_of_generic_aeval
    {F P S : k[X]} {α : L}
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X]))
    (hS : algebraMap k[X] L S = Polynomial.aeval α P) :
    P = S.comp F := by
  apply generic_root_aeval_injective (k := k) (L := L) hα
  calc
    Polynomial.aeval α P = algebraMap k[X] L S := hS.symm
    _ = Polynomial.aeval (algebraMap k[X] L (X : k[X])) S :=
      (aeval_parameter_eq_algebraMap (k := k) (L := L) S).symm
    _ = Polynomial.aeval (Polynomial.aeval α F) S := by rw [hα]
    _ = Polynomial.aeval α (S.comp F) := by rw [Polynomial.aeval_comp]

omit [IsScalarTower k k[X] L] in
lemma separated_generic_aeval_fixed
    {F G P Q : k[X]} {α β : L}
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q)
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X]))
    (hβ : Polynomial.aeval β G = algebraMap k[X] L (X : k[X])) :
    ∀ σ : L ≃ₐ[RatFunc k] L, σ (Polynomial.aeval α P) = Polynomial.aeval α P := by
  intro σ
  have hfiberσ :
      Polynomial.aeval (σ α) F = Polynomial.aeval β G := by
    exact (generic_fiber_relation_conjugate (k := k) hα σ).trans hβ.symm
  have hconj :
      Polynomial.aeval (σ α) P = Polynomial.aeval β Q :=
    separated_divisibility_aeval_eq (k := k) (L := L) (x := β) (y := σ α)
      hdiv hfiberσ
  have hfiber :
      Polynomial.aeval α F = Polynomial.aeval β G := hα.trans hβ.symm
  have hbase :
      Polynomial.aeval α P = Polynomial.aeval β Q :=
    separated_divisibility_aeval_eq (k := k) (L := L) (x := β) (y := α)
      hdiv hfiber
  calc
    σ (Polynomial.aeval α P) = Polynomial.aeval (σ α) P := ratFuncAlgEquiv_apply_aeval_k σ α P
    _ = Polynomial.aeval β Q := hconj
    _ = Polynomial.aeval α P := hbase.symm

omit [IsScalarTower k k[X] L] in
lemma galois_ratFunc_descends_from_separated_generic_roots
    [IsGalois (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    {F G P Q : k[X]} {α β : L}
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q)
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X]))
    (hβ : Polynomial.aeval β G = algebraMap k[X] L (X : k[X])) :
    ∃ r : RatFunc k, algebraMap (RatFunc k) L r = Polynomial.aeval α P :=
  galois_fixed_descends (K := RatFunc k) (L := L)
    (separated_generic_aeval_fixed (k := k) (L := L) hdiv hα hβ)

lemma galois_polynomial_descends_from_separated_generic_roots
    [IsGalois (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    {F G P Q : k[X]} {α β : L}
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q)
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X]))
    (hβ : Polynomial.aeval β G = algebraMap k[X] L (X : k[X]))
    (hαint : IsIntegral k[X] α) :
    ∃ S : k[X], algebraMap k[X] L S = Polynomial.aeval α P :=
  galois_fixed_integral_ratFunc_descends (k := k) (L := L)
    (separated_generic_aeval_fixed (k := k) (L := L) hdiv hα hβ)
    (isIntegral_aeval_of_isIntegral_base hαint P)

theorem galois_composition_from_separated_generic_roots
    [IsGalois (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    {F G P Q : k[X]} {α β : L}
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q)
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X]))
    (hβ : Polynomial.aeval β G = algebraMap k[X] L (X : k[X]))
    (hαint : IsIntegral k[X] α) :
    ∃ S : k[X], P = S.comp F ∧ Q = S.comp G := by
  obtain ⟨S, hS⟩ :=
    galois_polynomial_descends_from_separated_generic_roots
      (k := k) (L := L) hdiv hα hβ hαint
  refine ⟨S, ?_, ?_⟩
  · exact polynomial_identity_of_generic_aeval (k := k) (L := L) hα hS
  · have hfiber : Polynomial.aeval α F = Polynomial.aeval β G := hα.trans hβ.symm
    have hPQ : Polynomial.aeval α P = Polynomial.aeval β Q :=
      separated_divisibility_aeval_eq (k := k) (L := L) (x := β) (y := α)
        hdiv hfiber
    exact polynomial_identity_of_generic_aeval (k := k) (L := L) hβ (hS.trans hPQ)

end GenericFiberGaloisBridge

def cubicPlusLinear : k[X] :=
  X ^ 3 + X

def cubicQuadraticFactor : k[X][X] :=
  X ^ 2 + C (X : k[X]) * X + C ((X : k[X]) ^ 2 + 1)

lemma cubicPlusLinear_natDegree :
    (cubicPlusLinear : k[X]).natDegree = 3 := by
  have hpoly :
      (cubicPlusLinear : k[X]) =
        C (1 : k) * X ^ 3 + C (0 : k) * X ^ 2 + C (1 : k) * X + C (0 : k) := by
    unfold cubicPlusLinear
    simp
  rw [hpoly]
  exact Polynomial.natDegree_cubic (R := k) (a := 1) (b := 0) (c := 1) (d := 0) one_ne_zero

lemma cubicPlusLinear_natDegree_pos :
    0 < (cubicPlusLinear : k[X]).natDegree := by
  rw [cubicPlusLinear_natDegree]
  norm_num

lemma cubicPlusLinear_monic :
    (cubicPlusLinear : k[X]).Monic := by
  have hpoly :
      (cubicPlusLinear : k[X]) =
        C (1 : k) * X ^ 3 + C (0 : k) * X ^ 2 + C (1 : k) * X + C (0 : k) := by
    unfold cubicPlusLinear
    simp
  rw [hpoly, Polynomial.Monic, Polynomial.leadingCoeff_cubic]
  exact one_ne_zero

theorem cubic_separated_factorization :
    separatedDivisor (cubicPlusLinear : k[X]) (cubicPlusLinear : k[X]) =
      (X - C (X : k[X])) * (cubicQuadraticFactor : k[X][X]) := by
  unfold separatedDivisor cubicPlusLinear cubicQuadraticFactor
  simp [Polynomial.map_add, Polynomial.map_pow]
  ring

lemma genericDivisor_monic {F : k[X]} (hF : F.Monic) (hFpos : 0 < F.natDegree) :
    (genericDivisor F).Monic := by
  classical
  unfold genericDivisor
  rw [sub_eq_add_neg]
  exact (hF.map C).add_of_left <| by
    calc
      degree (-(C (X : k[X]) : k[X][X])) = degree (C (X : k[X]) : k[X][X]) := degree_neg _
      _ ≤ (0 : WithBot ℕ) := degree_C_le
      _ < degree (F.map C : k[X][X]) := by
        rw [hF.degree_map C, degree_eq_natDegree hF.ne_zero]
        exact WithBot.coe_lt_coe.mpr hFpos

lemma isIntegral_of_genericDivisor_root {A : Type*} [CommRing A] [Algebra k[X] A]
    {F : k[X]} (hF : F.Monic) (hFpos : 0 < F.natDegree) {α : A}
    (hα : Polynomial.aeval α (genericDivisor F) = 0) :
    IsIntegral k[X] α :=
  isIntegral_of_monic_aeval_eq_zero (genericDivisor_monic hF hFpos) hα

lemma degree_C_lt_genericDivisor {g h : k[X]} (hg : g.Monic) (hgpos : 0 < g.natDegree) :
    degree (C h : k[X][X]) < degree (genericDivisor g) := by
  calc
    degree (C h : k[X][X]) ≤ (0 : WithBot Nat) := degree_C_le
    _ < degree (genericDivisor g) := by
      unfold genericDivisor
      rw [degree_sub_eq_left_of_degree_lt]
      · rw [hg.degree_map C, degree_eq_natDegree hg.ne_zero]
        exact WithBot.coe_lt_coe.mpr hgpos
      · calc
          degree (C (X : k[X]) : k[X][X]) ≤ (0 : WithBot Nat) := degree_C_le
          _ < degree (g.map C : k[X][X]) := by
            rw [hg.degree_map C, degree_eq_natDegree hg.ne_zero]
            exact WithBot.coe_lt_coe.mpr hgpos

lemma eval₂_genericDivisor (g : k[X]) :
    eval₂ (subst g) (X : k[X]) (genericDivisor g) = 0 := by
  simp [genericDivisor, eval₂_map_C]

lemma leadingCoeff_genericDivisor {g : k[X]} (hgpos : 0 < g.natDegree) :
    (genericDivisor g).leadingCoeff = C g.leadingCoeff := by
  have hg0 : g ≠ 0 := ne_zero_of_natDegree_gt hgpos
  unfold genericDivisor
  rw [Polynomial.leadingCoeff_sub_of_degree_lt]
  · rw [Polynomial.leadingCoeff_map]
  · calc
      degree (C (X : k[X]) : k[X][X]) ≤ (0 : WithBot Nat) := degree_C_le
      _ < degree (g.map C : k[X][X]) := by
        rw [Polynomial.degree_map g C, degree_eq_natDegree hg0]
        exact WithBot.coe_lt_coe.mpr hgpos

lemma degree_C_lt_genericDivisor_of_natDegree_pos {g h : k[X]} (hgpos : 0 < g.natDegree) :
    degree (C h : k[X][X]) < degree (genericDivisor g) := by
  have hg0 : g ≠ 0 := ne_zero_of_natDegree_gt hgpos
  calc
    degree (C h : k[X][X]) ≤ (0 : WithBot Nat) := degree_C_le
    _ < degree (genericDivisor g) := by
      unfold genericDivisor
      rw [degree_sub_eq_left_of_degree_lt]
      · rw [Polynomial.degree_map g C, degree_eq_natDegree hg0]
        exact WithBot.coe_lt_coe.mpr hgpos
      · calc
          degree (C (X : k[X]) : k[X][X]) ≤ (0 : WithBot Nat) := degree_C_le
          _ < degree (g.map C : k[X][X]) := by
            rw [Polynomial.degree_map g C, degree_eq_natDegree hg0]
            exact WithBot.coe_lt_coe.mpr hgpos

lemma normalizedGenericDivisor_monic {g : k[X]} (hgpos : 0 < g.natDegree) :
    (normalizedGenericDivisor g).Monic := by
  have hglc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hgpos)
  unfold normalizedGenericDivisor
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [leadingCoeff_genericDivisor hgpos]
  rw [← C_mul]
  simp [hglc]

lemma isIntegral_of_normalizedGenericDivisor_root {A : Type*} [CommRing A] [Algebra k[X] A]
    {g : k[X]} (hgpos : 0 < g.natDegree) {α : A}
    (hα : Polynomial.aeval α (normalizedGenericDivisor g) = 0) :
    IsIntegral k[X] α :=
  isIntegral_of_monic_aeval_eq_zero (normalizedGenericDivisor_monic hgpos) hα

section GenericFiberRelationIntegrality

variable {L : Type*} [Field L]
  [Algebra k L] [Algebra k[X] L] [Algebra (RatFunc k) L]
  [IsScalarTower k k[X] L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L]

omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L] in
lemma isIntegral_of_generic_fiber_relation
    {F : k[X]} (hFpos : 0 < F.natDegree) {α : L}
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X])) :
    IsIntegral k[X] α := by
  apply isIntegral_of_normalizedGenericDivisor_root (k := k) hFpos
  unfold normalizedGenericDivisor
  rw [Polynomial.aeval_mul, aeval_genericDivisor_of_relation (k := k) (L := L) hα,
    mul_zero]

theorem galois_composition_from_generic_fiber_relations
    [IsGalois (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    {F G P Q : k[X]} {α β : L}
    (hFpos : 0 < F.natDegree)
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q)
    (hα : Polynomial.aeval α F = algebraMap k[X] L (X : k[X]))
    (hβ : Polynomial.aeval β G = algebraMap k[X] L (X : k[X])) :
    ∃ S : k[X], P = S.comp F ∧ Q = S.comp G :=
  galois_composition_from_separated_generic_roots (k := k) (L := L)
    hdiv hα hβ (isIntegral_of_generic_fiber_relation (k := k) (L := L) hFpos hα)

end GenericFiberRelationIntegrality

lemma degree_C_lt_normalizedGenericDivisor {g h : k[X]} (hgpos : 0 < g.natDegree) :
    degree (C h : k[X][X]) < degree (normalizedGenericDivisor g) := by
  have hglc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hgpos)
  have hscalar : (C g.leadingCoeff⁻¹ : k[X]) ≠ 0 := by
    exact C_ne_zero.mpr (inv_ne_zero hglc)
  rw [show degree (normalizedGenericDivisor g) = degree (genericDivisor g) by
    unfold normalizedGenericDivisor
    rw [Polynomial.degree_C_mul hscalar]]
  exact degree_C_lt_genericDivisor_of_natDegree_pos hgpos

lemma swap_genericDivisor (F : k[X]) :
    Polynomial.Bivariate.swap (genericDivisor F) = C (-1 : k[X]) * X + C F := by
  unfold genericDivisor
  rw [map_sub]
  rw [Polynomial.Bivariate.swap_map_C, Polynomial.Bivariate.swap_X]
  rw [sub_eq_add_neg]
  rw [show C (-1 : k[X]) * (X : k[X][X]) = -(X : k[X][X]) by
    rw [show (-1 : k[X]) = -(1 : k[X]) by rfl]
    rw [C_neg, C_1]
    exact neg_one_mul (X : k[X][X])]
  ac_rfl

lemma swap_genericDivisor_irreducible (F : k[X]) :
    Irreducible (Polynomial.Bivariate.swap (genericDivisor F)) := by
  rw [swap_genericDivisor]
  have hne : (-1 : k[X]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hrel : IsRelPrime (-1 : k[X]) F :=
    IsRelPrime.neg_left (isRelPrime_one_left (x := F) : IsRelPrime (1 : k[X]) F)
  exact Polynomial.irreducible_C_mul_X_add_C hne hrel

lemma genericDivisor_irreducible (F : k[X]) : Irreducible (genericDivisor F) := by
  exact (MulEquiv.irreducible_iff (Polynomial.Bivariate.swap (R := k))).mp
    (swap_genericDivisor_irreducible F)

lemma genericDivisor_natDegree_ne_zero {F : k[X]} (hFpos : 0 < F.natDegree) :
    (genericDivisor F).natDegree ≠ 0 := by
  have hdegpos : (0 : WithBot Nat) < degree (genericDivisor F) := by
    simpa using degree_C_lt_genericDivisor_of_natDegree_pos (g := F) (h := 1) hFpos
  exact ne_of_gt (natDegree_pos_iff_degree_pos.mpr hdegpos)

lemma genericFiberRatFunc_irreducible {F : k[X]} (hFpos : 0 < F.natDegree) :
    Irreducible (genericFiberRatFunc F) := by
  have hirr : Irreducible (genericDivisor F) := genericDivisor_irreducible F
  have hprim : (genericDivisor F).IsPrimitive :=
    hirr.isPrimitive (genericDivisor_natDegree_ne_zero hFpos)
  exact (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc k) hprim).mp hirr

lemma derivative_genericDivisor (F : k[X]) :
    derivative (genericDivisor F) = (derivative F).map C := by
  unfold genericDivisor
  simp [Polynomial.derivative_map]

lemma derivative_genericDivisor_ne_zero {F : k[X]} (hFderiv : derivative F ≠ 0) :
    derivative (genericDivisor F) ≠ 0 := by
  rw [derivative_genericDivisor]
  exact Polynomial.map_ne_zero hFderiv

lemma map_ratFunc_ne_zero {P : k[X][X]} (hP : P ≠ 0) :
    P.map (algebraMap k[X] (RatFunc k)) ≠ 0 := by
  intro hmap
  exact hP ((Polynomial.map_eq_zero_iff
    (IsFractionRing.injective k[X] (RatFunc k))).mp hmap)

lemma derivative_genericFiberRatFunc_ne_zero {F : k[X]} (hFderiv : derivative F ≠ 0) :
    derivative (genericFiberRatFunc F) ≠ 0 := by
  unfold genericFiberRatFunc
  rw [Polynomial.derivative_map]
  exact map_ratFunc_ne_zero (derivative_genericDivisor_ne_zero hFderiv)

theorem separable_generic_fiber {F : k[X]} (hFpos : 0 < F.natDegree)
    (hFderiv : derivative F ≠ 0) :
    (genericFiberRatFunc F).Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero (genericFiberRatFunc_irreducible hFpos)]
  exact derivative_genericFiberRatFunc_ne_zero hFderiv

lemma generic_fiber_splitting_field_isGalois
    {F : k[X]} (hFpos : 0 < F.natDegree) (hFderiv : derivative F ≠ 0)
    {L : Type*} [Field L] [Algebra (RatFunc k) L]
    [(genericFiberRatFunc F).IsSplittingField (RatFunc k) L] :
    IsGalois (RatFunc k) L :=
  IsGalois.of_separable_splitting_field (p := genericFiberRatFunc F)
    (separable_generic_fiber hFpos hFderiv)

lemma isSeparable_of_aeval_eq_zero_of_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : K[X]} (hp : p.Separable) {x : L}
    (hx : Polynomial.aeval x p = 0) :
    IsSeparable K x :=
  hp.of_dvd (minpoly.dvd K x hx)

lemma isSeparable_of_aeval_mul_eq_zero_of_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p q : K[X]} (hp : p.Separable) (hq : q.Separable) {x : L}
    (hx : Polynomial.aeval x (p * q) = 0) :
    IsSeparable K x := by
  rw [Polynomial.aeval_mul] at hx
  cases mul_eq_zero.mp hx with
  | inl hpzero =>
      exact isSeparable_of_aeval_eq_zero_of_separable
        (K := K) (L := L) (p := p) hp hpzero
  | inr hqzero =>
      exact isSeparable_of_aeval_eq_zero_of_separable
        (K := K) (L := L) (p := q) hq hqzero

lemma splittingField_mul_isSeparable
    {K : Type*} [Field K] {p q : K[X]}
    (hp : p.Separable) (hq : q.Separable) :
    Algebra.IsSeparable K ((p * q).SplittingField) := by
  classical
  let L := (p * q).SplittingField
  have htop :
      IntermediateField.adjoin K ((p * q).rootSet L) =
        (⊤ : IntermediateField K L) := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.top_toSubalgebra]
    apply top_unique
    have hSFtop :
        Algebra.adjoin K ((p * q).rootSet L) = (⊤ : Subalgebra K L) := by
      exact Polynomial.SplittingField.adjoin_rootSet (p * q)
    rw [← hSFtop]
    exact IntermediateField.algebra_adjoin_le_adjoin K ((p * q).rootSet L)
  have hsepAdjoin :
      Algebra.IsSeparable K (IntermediateField.adjoin K ((p * q).rootSet L)) := by
    rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
    intro x hx
    exact isSeparable_of_aeval_mul_eq_zero_of_separable
      (K := K) (L := L) (p := p) (q := q) hp hq
      (Polynomial.aeval_eq_zero_of_mem_rootSet hx)
  have hsepTop : Algebra.IsSeparable K (⊤ : IntermediateField K L) := by
    rw [show (⊤ : IntermediateField K L) =
      IntermediateField.adjoin K ((p * q).rootSet L) from htop.symm]
    exact hsepAdjoin
  exact AlgEquiv.Algebra.isSeparable
    (IntermediateField.topEquiv (F := K) (E := L))

lemma splittingField_mul_isGalois
    {K : Type*} [Field K] {p q : K[X]}
    (hp : p.Separable) (hq : q.Separable) :
    IsGalois K ((p * q).SplittingField) := by
  rw [isGalois_iff]
  exact ⟨splittingField_mul_isSeparable hp hq, inferInstance⟩

lemma ratFunc_splittingField_isScalarTower (p : (RatFunc k)[X]) :
    IsScalarTower k k[X] p.SplittingField := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap (RatFunc k) p.SplittingField (algebraMap k (RatFunc k) x) =
    algebraMap (RatFunc k) p.SplittingField (algebraMap k[X] (RatFunc k) (C x))
  rw [IsScalarTower.algebraMap_eq k k[X] (RatFunc k)]
  simp

section GenericFiberSplittingRoots

variable {L : Type*} [Field L]
  [Algebra k L] [Algebra k[X] L] [Algebra (RatFunc k) L]
  [IsScalarTower k k[X] L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L]

omit [IsScalarTower k (RatFunc k) L] in
lemma exists_generic_fiber_relation_of_splits
    {F : k[X]} (hFpos : 0 < F.natDegree)
    (hFsplit : ((genericFiberRatFunc F).map (algebraMap (RatFunc k) L)).Splits) :
    ∃ α : L, Polynomial.aeval α F = algebraMap k[X] L (X : k[X]) := by
  have hdeg :
      degree ((genericFiberRatFunc F).map (algebraMap (RatFunc k) L)) ≠ 0 := by
    rw [degree_map_eq_of_injective (FaithfulSMul.algebraMap_injective (RatFunc k) L)]
    exact (degree_pos_of_irreducible (genericFiberRatFunc_irreducible (k := k) hFpos)).ne'
  obtain ⟨α, hα⟩ := hFsplit.exists_eval_eq_zero hdeg
  refine ⟨α, genericFiberRatFunc_root_relation (k := k) (L := L) ?_⟩
  simpa [Polynomial.eval_map_algebraMap] using hα

theorem galois_composition_from_generic_fiber_splits
    [IsGalois (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    {F G P Q : k[X]}
    (hFpos : 0 < F.natDegree) (hGpos : 0 < G.natDegree)
    (hFsplit : ((genericFiberRatFunc F).map (algebraMap (RatFunc k) L)).Splits)
    (hGsplit : ((genericFiberRatFunc G).map (algebraMap (RatFunc k) L)).Splits)
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q) :
    ∃ S : k[X], P = S.comp F ∧ Q = S.comp G := by
  obtain ⟨α, hα⟩ := exists_generic_fiber_relation_of_splits (k := k) (L := L) hFpos hFsplit
  obtain ⟨β, hβ⟩ := exists_generic_fiber_relation_of_splits (k := k) (L := L) hGpos hGsplit
  exact galois_composition_from_generic_fiber_relations (k := k) (L := L)
    hFpos hdiv hα hβ

end GenericFiberSplittingRoots

theorem separable_case_via_common_splitting_field
    {F G P Q : k[X]} (hF : 0 < F.natDegree) (hG : 0 < G.natDegree)
    (hFsep : derivative F ≠ 0) (hGsep : derivative G ≠ 0)
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q) :
    ∃ S : k[X], P = S.comp F ∧ Q = S.comp G := by
  let pF := genericFiberRatFunc F
  let pG := genericFiberRatFunc G
  let L := (pF * pG).SplittingField
  haveI : IsScalarTower k k[X] L :=
    ratFunc_splittingField_isScalarTower (k := k) (pF * pG)
  have hpFsep : pF.Separable := separable_generic_fiber (k := k) hF hFsep
  have hpGsep : pG.Separable := separable_generic_fiber (k := k) hG hGsep
  haveI : IsGalois (RatFunc k) L :=
    splittingField_mul_isGalois (K := RatFunc k) hpFsep hpGsep
  have hpF0 : pF ≠ 0 := (genericFiberRatFunc_irreducible (k := k) hF).ne_zero
  have hpG0 : pG ≠ 0 := (genericFiberRatFunc_irreducible (k := k) hG).ne_zero
  have hprod0 : pF * pG ≠ 0 := mul_ne_zero hpF0 hpG0
  have hFsplit : (pF.map (algebraMap (RatFunc k) L)).Splits := by
    exact (Polynomial.SplittingField.splits (pF * pG)).of_dvd
      (Polynomial.map_ne_zero hprod0) (by
        rw [Polynomial.map_mul]
        exact dvd_mul_right _ _)
  have hGsplit : (pG.map (algebraMap (RatFunc k) L)).Splits := by
    exact (Polynomial.SplittingField.splits (pF * pG)).of_dvd
      (Polynomial.map_ne_zero hprod0) (by
        rw [Polynomial.map_mul]
        exact dvd_mul_left _ _)
  exact galois_composition_from_generic_fiber_splits (k := k) (L := L)
    hF hG hFsplit hGsplit hdiv

lemma separatedDivisor_monic {F G : k[X]} (hF : F.Monic) (hFpos : 0 < F.natDegree) :
    (separatedDivisor F G).Monic := by
  classical
  unfold separatedDivisor
  rw [sub_eq_add_neg]
  exact (hF.map C).add_of_left <| by
    calc
      degree (-(C G : k[X][X])) = degree (C G : k[X][X]) := degree_neg _
      _ ≤ (0 : WithBot ℕ) := degree_C_le
      _ < degree (F.map C : k[X][X]) := by
        rw [hF.degree_map C, degree_eq_natDegree hF.ne_zero]
        exact WithBot.coe_lt_coe.mpr hFpos

lemma map_genericDivisor (F G : k[X]) :
    (genericDivisor F).map (subst G) = separatedDivisor F G := by
  ext n
  simp [genericDivisor, separatedDivisor, coeff_map, coeff_sub]

lemma map_map_C_aeval (P G : k[X]) :
    (P.map C : k[X][X]).map (subst G) = P.map C := by
  ext n
  simp [coeff_map, coeff_map]

lemma monic_case
    {F G P Q : k[X]} (hF : F.Monic) (hFpos : 0 < F.natDegree) (hG : 0 < G.natDegree)
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q) :
    ∃ S : k[X], P = S.comp F ∧ Q = S.comp G := by
  let Dgen := genericDivisor F
  let R := (P.map C : k[X][X]) %ₘ Dgen
  have hDgen : Dgen.Monic := genericDivisor_monic hF hFpos
  have hDsep : (separatedDivisor F G).Monic := separatedDivisor_monic hF hFpos
  have hmapD : Dgen.map (subst G) = separatedDivisor F G := by
    simpa [Dgen] using map_genericDivisor F G
  have hmapP : (P.map C : k[X][X]).map (subst G) = P.map C := map_map_C_aeval P G
  have hmapR :
      R.map (subst G) =
        ((P.map C : k[X][X]).map (subst G)) %ₘ
          (Dgen.map (subst G)) := by
    simpa [R, Dgen] using
      (Polynomial.map_modByMonic (subst G) hDgen :
        ((P.map C : k[X][X]) %ₘ Dgen).map (subst G) =
          ((P.map C : k[X][X]).map (subst G)) %ₘ
            (Dgen.map (subst G)))
  have hrem_eq :
      (P.map C : k[X][X]) %ₘ separatedDivisor F G = C Q := by
    have hsubzero :
        ((P.map C : k[X][X]) - C Q) %ₘ separatedDivisor F G = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hDsep).mpr hdiv
    have hsub :
        ((P.map C : k[X][X]) - C Q) %ₘ separatedDivisor F G =
          ((P.map C : k[X][X]) %ₘ separatedDivisor F G) -
            ((C Q : k[X][X]) %ₘ separatedDivisor F G) := by
      simpa using Polynomial.sub_modByMonic (P.map C : k[X][X]) (C Q) (separatedDivisor F G)
    have hCQ : (C Q : k[X][X]) %ₘ separatedDivisor F G = C Q := by
      rw [Polynomial.modByMonic_eq_self_iff hDsep]
      calc
        degree (C Q : k[X][X]) ≤ (0 : WithBot ℕ) := degree_C_le
        _ < degree (separatedDivisor F G) := by
          unfold separatedDivisor
          rw [degree_sub_eq_left_of_degree_lt]
          · rw [hF.degree_map C, degree_eq_natDegree hF.ne_zero]
            exact WithBot.coe_lt_coe.mpr hFpos
          · calc
              degree (C G : k[X][X]) ≤ (0 : WithBot ℕ) := degree_C_le
              _ < degree (F.map C : k[X][X]) := by
                rw [hF.degree_map C, degree_eq_natDegree hF.ne_zero]
                exact WithBot.coe_lt_coe.mpr hFpos
    rw [hsub, hCQ] at hsubzero
    exact sub_eq_zero.mp hsubzero
  have hRmapC : R.map (subst G) = C Q := by
    rw [hmapR, hmapP, hmapD, hrem_eq]
  have hRconst : R = C (R.coeff 0) := eq_C_of_map_aeval_eq_C hG hRmapC
  refine ⟨R.coeff 0, ?_, ?_⟩
  · have hdivision := Polynomial.modByMonic_add_div (P.map C : k[X][X]) Dgen
    have hdivision' : R + Dgen * ((P.map C : k[X][X]) /ₘ Dgen) = P.map C := by
      simpa [R] using hdivision
    have heval := congrArg
      (fun A : k[X][X] => eval₂ (subst F) (X : k[X]) A) hdivision'
    have hDzero :
        eval₂ (subst F) (X : k[X]) Dgen = 0 := by
      simp [Dgen, genericDivisor, eval₂_map_C]
    rw [hRconst] at heval
    change
      eval₂ (subst F) (X : k[X]) (C (R.coeff 0) + Dgen * ((P.map C : k[X][X]) /ₘ Dgen)) =
        eval₂ (subst F) (X : k[X]) (P.map C : k[X][X]) at heval
    rw [eval₂_add, eval₂_mul, hDzero, zero_mul, add_zero] at heval
    rw [eval₂_C_subst, eval₂_map_C] at heval
    exact heval.symm
  · have hcoeff0 := congrArg (fun A : k[X][X] => A.coeff 0) hRmapC
    simpa [coeff_map] using hcoeff0.symm

theorem separated_composition_criterion
    {F G P Q : k[X]} (hF : 0 < F.natDegree) (hG : 0 < G.natDegree)
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q) :
    ∃ S : k[X], P = S.comp F ∧ Q = S.comp G := by
  let a : k := F.leadingCoeff
  have ha : a ≠ 0 := by
    exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hF)
  let F₀ : k[X] := C a⁻¹ * F
  let G₀ : k[X] := C a⁻¹ * G
  have hF₀monic : F₀.Monic := by
    unfold F₀ a
    rw [Monic, leadingCoeff_mul]
    simpa using inv_mul_cancel₀ ha
  have hF₀pos : 0 < F₀.natDegree := by
    unfold F₀ a
    rwa [natDegree_C_mul (inv_ne_zero ha)]
  have hG₀pos : 0 < G₀.natDegree := by
    unfold G₀ a
    rwa [natDegree_C_mul (inv_ne_zero ha)]
  have hDscale :
      separatedDivisor F G = C (C a) * separatedDivisor F₀ G₀ := by
    unfold separatedDivisor F₀ G₀
    simp [Polynomial.map_mul, a]
    ring_nf
    have hscalar :
        (C (C a) : k[X][X]) * C (C a⁻¹) = 1 := by
      rw [← C_mul, ← C_mul]
      simp [ha]
    rw [mul_assoc, hscalar, mul_one, mul_assoc, hscalar, mul_one]
  have hunit : IsUnit (C (C a) : k[X][X]) := by
    exact isUnit_C.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha))
  have hdiv₀ : separatedDivisor F₀ G₀ ∣ (P.map C : k[X][X]) - C Q := by
    rw [hDscale] at hdiv
    exact (hunit.mul_left_dvd).mp hdiv
  obtain ⟨T, hP, hQ⟩ := monic_case hF₀monic hF₀pos hG₀pos hdiv₀
  refine ⟨T.comp (C a⁻¹ * X), ?_, ?_⟩
  · rw [comp_assoc, hP]
    congr 1
    simp [F₀, comp_eq_aeval, a]
  · rw [comp_assoc, hQ]
    congr 1
    simp [G₀, comp_eq_aeval, a]

theorem separated_composition_converse (F G S : k[X]) :
    separatedDivisor F G ∣ (S.comp F).map C - C (S.comp G) := by
  classical
  induction S using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa [add_comp, Polynomial.map_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using dvd_add hp hq
  | monomial n c =>
      have hpow :
          separatedDivisor F G ∣
            (F.map C) ^ n - C (G ^ n) := by
        induction n with
        | zero =>
            simp [separatedDivisor]
        | succ n ih =>
            have hstep :
                (F.map C) ^ (n + 1) - C (G ^ (n + 1)) =
                  (F.map C) ^ n * (F.map C - C G) +
                    ((F.map C) ^ n - C (G ^ n)) * C G := by
              simp [pow_succ, map_mul]
              ring
            rw [hstep]
            exact dvd_add (dvd_mul_of_dvd_right dvd_rfl _) (dvd_mul_of_dvd_left ih _)
      have hmonoF :
          (monomial n c).comp F = C c * F ^ n := by
        rw [← C_mul_X_pow_eq_monomial]
        simp [mul_comp, pow_comp]
      have hmonoG :
          (monomial n c).comp G = C c * G ^ n := by
        rw [← C_mul_X_pow_eq_monomial]
        simp [mul_comp, pow_comp]
      have htarget :
          (C c * F ^ n).map C - C (C c * G ^ n) =
            C (C c) * ((F.map C) ^ n - C (G ^ n)) := by
        simp [Polynomial.map_mul, Polynomial.map_pow, mul_sub]
      rw [hmonoF, hmonoG, htarget]
      exact dvd_mul_of_dvd_right hpow _

theorem separated_composition_criterion_iff
    {F G P Q : k[X]} (hF : 0 < F.natDegree) (hG : 0 < G.natDegree) :
    separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q ↔
      ∃ S : k[X], P = S.comp F ∧ Q = S.comp G := by
  constructor
  · exact separated_composition_criterion hF hG
  · rintro ⟨S, rfl, rfl⟩
    exact separated_composition_converse F G S

theorem separable_case
    {F G P Q : k[X]} (hF : 0 < F.natDegree) (hG : 0 < G.natDegree)
    (hFsep : derivative F ≠ 0) (hGsep : derivative G ≠ 0)
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q) :
    ∃ S : k[X], P = S.comp F ∧ Q = S.comp G :=
  separable_case_via_common_splitting_field hF hG hFsep hGsep hdiv

theorem frobenius_reduction_step_left
    {p : Nat} [CharP k p] (hp : Ne p 0)
    {F G P Q : k[X]} (hF : 0 < F.natDegree) (hG : 0 < G.natDegree)
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q)
    (hFderiv : derivative F = 0) :
    derivative P = 0 ∧
      ∃ F1 P1 : k[X],
        F = F1.comp ((X : k[X]) ^ p) ∧
        P = P1.comp ((X : k[X]) ^ p) ∧
        separatedDivisor F1 G ∣ (P1.map C : k[X][X]) - C Q := by
  obtain ⟨S, hP, hQ⟩ := separated_composition_criterion hF hG hdiv
  have hPderiv : derivative P = 0 := by
    rw [hP, Polynomial.derivative_comp, hFderiv]
    simp
  obtain ⟨F1, hF1⟩ := (zero_derivative_iff_expand (k := k) hp F).mp hFderiv
  let P1 : k[X] := S.comp F1
  refine ⟨hPderiv, F1, P1, hF1, ?_, ?_⟩
  · symm
    change (S.comp F1).comp ((X : k[X]) ^ p) = P
    rw [comp_assoc, ← hF1, ← hP]
  · simpa [P1, hQ] using separated_composition_converse F1 G S

theorem frobenius_reduction_step_right
    {p : Nat} [CharP k p] (hp : Ne p 0)
    {F G P Q : k[X]} (hF : 0 < F.natDegree) (hG : 0 < G.natDegree)
    (hdiv : separatedDivisor F G ∣ (P.map C : k[X][X]) - C Q)
    (hGderiv : derivative G = 0) :
    derivative Q = 0 ∧
      ∃ G1 Q1 : k[X],
        G = G1.comp ((X : k[X]) ^ p) ∧
        Q = Q1.comp ((X : k[X]) ^ p) ∧
        separatedDivisor F G1 ∣ (P.map C : k[X][X]) - C Q1 := by
  obtain ⟨S, hP, hQ⟩ := separated_composition_criterion hF hG hdiv
  have hQderiv : derivative Q = 0 := by
    rw [hQ, Polynomial.derivative_comp, hGderiv]
    simp
  obtain ⟨G1, hG1⟩ := (zero_derivative_iff_expand (k := k) hp G).mp hGderiv
  let Q1 : k[X] := S.comp G1
  refine ⟨hQderiv, G1, Q1, hG1, ?_, ?_⟩
  · symm
    change (S.comp G1).comp ((X : k[X]) ^ p) = Q
    rw [comp_assoc, ← hG1, ← hQ]
  · simpa [Q1, hP] using separated_composition_converse F G1 S

lemma monic_dvd_of_map_dvd
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {D T : K[X]} (hD : D.Monic)
    (hdiv : D.map (algebraMap K L) ∣ T.map (algebraMap K L)) :
    D ∣ T := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hD]
  have hzeroL :
      T.map (algebraMap K L) %ₘ D.map (algebraMap K L) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (hD.map (algebraMap K L))).mpr hdiv
  have hmap :
      (T %ₘ D).map (algebraMap K L) =
        T.map (algebraMap K L) %ₘ D.map (algebraMap K L) :=
    Polynomial.map_modByMonic (algebraMap K L) hD
  exact (Polynomial.map_eq_zero_iff (FaithfulSMul.algebraMap_injective K L)).mp
    (hmap.trans hzeroL)

lemma monic_dvd_of_fraction_map_dvd
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {D T : R[X]} (hD : D.Monic)
    (hdiv : D.map (algebraMap R K) ∣ T.map (algebraMap R K)) :
    D ∣ T := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hD]
  have hzeroK :
      T.map (algebraMap R K) %ₘ D.map (algebraMap R K) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (hD.map (algebraMap R K))).mpr hdiv
  have hmap :
      (T %ₘ D).map (algebraMap R K) =
        T.map (algebraMap R K) %ₘ D.map (algebraMap R K) :=
    Polynomial.map_modByMonic (algebraMap R K) hD
  exact (Polynomial.map_eq_zero_iff (IsFractionRing.injective R K)).mp
    (hmap.trans hzeroK)

lemma three_linear_factors_dvd_of_eval_eq_zero
    {K : Type*} [Field K] {P : K[X]} {a b c : K}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : P.eval a = 0) (hb : P.eval b = 0) (hc : P.eval c = 0) :
    (X - C a) * (X - C b) * (X - C c) ∣ P := by
  have hAdiv : X - C a ∣ P :=
    Polynomial.dvd_iff_isRoot.mpr (by simpa [Polynomial.IsRoot] using ha)
  rcases hAdiv with ⟨Q, hQ⟩
  have hQb : Q.eval b = 0 := by
    have hb' : ((X - C a) * Q).eval b = 0 := by simpa [hQ] using hb
    rw [Polynomial.eval_mul] at hb'
    have hlin : (X - C a).eval b ≠ 0 := by
      simpa using sub_ne_zero.mpr (Ne.symm hab)
    exact (mul_eq_zero.mp hb').resolve_left hlin
  have hBdiv : X - C b ∣ Q :=
    Polynomial.dvd_iff_isRoot.mpr (by simpa [Polynomial.IsRoot] using hQb)
  rcases hBdiv with ⟨R, hR⟩
  have hRc : R.eval c = 0 := by
    have hc' : ((X - C a) * ((X - C b) * R)).eval c = 0 := by
      simpa [hQ, hR] using hc
    rw [Polynomial.eval_mul, Polynomial.eval_mul] at hc'
    have ha' : (X - C a).eval c ≠ 0 := by
      simpa using sub_ne_zero.mpr (Ne.symm hac)
    have hb' : (X - C b).eval c ≠ 0 := by
      simpa using sub_ne_zero.mpr (Ne.symm hbc)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hc').resolve_left ha')).resolve_left hb'
  have hCdiv : X - C c ∣ R :=
    Polynomial.dvd_iff_isRoot.mpr (by simpa [Polynomial.IsRoot] using hRc)
  rcases hCdiv with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  rw [hQ, hR, hS]
  ring

theorem symmetric_composition_criterion
    {g f : k[X]} (hg : 0 < g.natDegree) :
    separatedDivisor g g ∣ (f.map C : k[X][X]) - C f ↔
      ∃ h : k[X], f = h.comp g := by
  constructor
  · intro hdiv
    obtain ⟨S, hP, _hQ⟩ := separated_composition_criterion hg hg hdiv
    exact ⟨S, hP⟩
  · rintro ⟨h, rfl⟩
    exact separated_composition_converse g g h

theorem cubic_functional_equation_divisibility_form {f : k[X]} :
    separatedDivisor (cubicPlusLinear : k[X]) (cubicPlusLinear : k[X]) ∣
        (f.map C : k[X][X]) - C f ↔
      ∃ h : k[X], f = h.comp (cubicPlusLinear : k[X]) :=
  symmetric_composition_criterion cubicPlusLinear_natDegree_pos

section CubicSquareRootFunctionalEquation

variable {L : Type*} [Field L]
  [Algebra k L] [Algebra k[X] L] [Algebra (RatFunc k) L]
  [IsScalarTower k k[X] L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L]

omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [IsScalarTower k[X] (RatFunc k) L] in
lemma eval_map_separatedTarget_eq
    (f : k[X]) (x z : L)
    (hx : x = algebraMap k[X] L (X : k[X])) :
    Polynomial.eval z (((f.map C : k[X][X]) - C f).map (algebraMap k[X] L)) =
      Polynomial.aeval z f - Polynomial.aeval x f := by
  subst x
  have hφ :
      (algebraMap k[X] L) =
        (Polynomial.aeval (algebraMap k[X] L (X : k[X])) : k[X] →ₐ[k] L).toRingHom := by
    have hAlg :
        (IsScalarTower.toAlgHom k k[X] L) =
          (Polynomial.aeval (algebraMap k[X] L (X : k[X])) : k[X] →ₐ[k] L) := by
      apply Polynomial.algHom_ext
      simp
    exact congrArg AlgHom.toRingHom hAlg
  rw [Polynomial.eval_map]
  rw [hφ]
  simpa using eval₂_separatedTarget (k := k) (L := L) f f
    (algebraMap k[X] L (X : k[X])) z

omit [Algebra k L] [Algebra (RatFunc k) L] [IsScalarTower k k[X] L]
  [IsScalarTower k (RatFunc k) L] [IsScalarTower k[X] (RatFunc k) L] in
lemma eval_map_cubicQuadraticFactor
    (x z : L) (hx : x = algebraMap k[X] L (X : k[X])) :
    Polynomial.eval z ((cubicQuadraticFactor : k[X][X]).map (algebraMap k[X] L)) =
      z ^ 2 + x * z + (x ^ 2 + 1) := by
  subst x
  simp [cubicQuadraticFactor, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

lemma square_root_branch_quadratic_plus
    {x s : L} (h2 : (2 : L) ≠ 0)
    (hs : s ^ 2 = -3 * x ^ 2 - 4) :
    ((-x + s) / 2) ^ 2 + x * ((-x + s) / 2) + (x ^ 2 + 1) = 0 := by
  field_simp [h2]
  ring_nf
  rw [hs]
  ring

lemma square_root_branch_quadratic_minus
    {x s : L} (h2 : (2 : L) ≠ 0)
    (hs : s ^ 2 = -3 * x ^ 2 - 4) :
    ((-x - s) / 2) ^ 2 + x * ((-x - s) / 2) + (x ^ 2 + 1) = 0 := by
  field_simp [h2]
  ring_nf
  rw [hs]
  ring

lemma polynomial_quadratic_ne_zero :
    (C (3 : k) * (X : k[X]) ^ 2 + C (1 : k)) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun P : k[X] => P.coeff 0) h
  simp at hcoeff

lemma polynomial_discriminant_ne_zero (h2 : (2 : k) ≠ 0) :
    (-C (3 : k) * (X : k[X]) ^ 2 - C (4 : k)) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun P : k[X] => P.coeff 0) h
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = (2 : k) ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  simp at hcoeff
  exact h4 hcoeff

omit [Algebra k L] [IsScalarTower k k[X] L] [IsScalarTower k (RatFunc k) L] in
lemma generic_quadratic_value_ne_zero (_h2 : (2 : k) ≠ 0) :
    (3 : L) * (algebraMap k[X] L (X : k[X])) ^ 2 + 1 ≠ 0 := by
  intro h
  exact polynomial_quadratic_ne_zero (k := k)
    (algebraMap_polynomial_to_ratFunc_extension_injective (k := k) (L := L) (by
      rw [map_add, map_mul, map_pow, map_zero]
      have hC3 : algebraMap k[X] L (C (3 : k)) = (3 : L) := by
        rw [show C (3 : k) = (3 : k[X]) by
          exact map_natCast (C : k →+* k[X]) 3]
        exact map_natCast (algebraMap k[X] L) 3
      have hC1 : algebraMap k[X] L (C (1 : k)) = (1 : L) := by
        rw [show C (1 : k) = (1 : k[X]) by
          exact map_one (C : k →+* k[X])]
        exact map_one (algebraMap k[X] L)
      rw [hC3, hC1]
      simpa using h))

omit [Algebra k L] [IsScalarTower k k[X] L] [IsScalarTower k (RatFunc k) L] in
lemma generic_discriminant_value_ne_zero (h2 : (2 : k) ≠ 0) :
    -(3 : L) * (algebraMap k[X] L (X : k[X])) ^ 2 - 4 ≠ 0 := by
  intro h
  exact polynomial_discriminant_ne_zero (k := k) h2
    (algebraMap_polynomial_to_ratFunc_extension_injective (k := k) (L := L) (by
      rw [map_sub, map_mul, map_neg, map_pow, map_zero]
      have hC3 : algebraMap k[X] L (C (3 : k)) = (3 : L) := by
        rw [show C (3 : k) = (3 : k[X]) by
          exact map_natCast (C : k →+* k[X]) 3]
        exact map_natCast (algebraMap k[X] L) 3
      have hC4 : algebraMap k[X] L (C (4 : k)) = (4 : L) := by
        rw [show C (4 : k) = (4 : k[X]) by
          exact map_natCast (C : k →+* k[X]) 4]
        exact map_natCast (algebraMap k[X] L) 4
      rw [hC3, hC4]
      simpa using h))

omit [IsScalarTower k (RatFunc k) L] in
theorem cubic_functional_equation_square_root
    (h2 : (2 : k) ≠ 0) {f : k[X]} {s : L}
    (hs : s ^ 2 =
      -(3 : L) * (algebraMap k[X] L (X : k[X])) ^ 2 - 4)
    (hplus :
      Polynomial.aeval (algebraMap k[X] L (X : k[X])) f =
        Polynomial.aeval ((-(algebraMap k[X] L (X : k[X])) + s) / 2) f)
    (hminus :
      Polynomial.aeval (algebraMap k[X] L (X : k[X])) f =
        Polynomial.aeval ((-(algebraMap k[X] L (X : k[X])) - s) / 2) f) :
    ∃ h : k[X], f = h.comp (cubicPlusLinear : k[X]) := by
  classical
  let x : L := algebraMap k[X] L (X : k[X])
  let uPlus : L := (-x + s) / 2
  let uMinus : L := (-x - s) / 2
  let D : k[X][X] := separatedDivisor (cubicPlusLinear : k[X]) (cubicPlusLinear : k[X])
  let T : k[X][X] := (f.map C : k[X][X]) - C f
  let Q : L[X] := (cubicQuadraticFactor : k[X][X]).map (algebraMap k[X] L)
  let TL : L[X] := T.map (algebraMap k[X] L)
  have h2L : (2 : L) ≠ 0 := by
    have h2map : algebraMap k L (2 : k) ≠ 0 :=
      (_root_.map_ne_zero (algebraMap k L)).mpr h2
    have hcast : algebraMap k L (2 : k) = (2 : L) :=
      map_natCast (algebraMap k L) 2
    intro h
    exact h2map (hcast.trans h)
  have hsx : s ^ 2 = -(3 : L) * x ^ 2 - 4 := by
    simpa [x] using hs
  have hsne : s ≠ 0 := by
    intro hs0
    have hdisc : -(3 : L) * x ^ 2 - 4 = 0 := by
      simpa [hs0] using hsx.symm
    exact generic_discriminant_value_ne_zero (k := k) (L := L) h2 (by simpa [x] using hdisc)
  have hbranches_ne : uPlus ≠ uMinus := by
    intro h
    apply hsne
    have hdiff : uPlus - uMinus = s := by
      simp [uPlus, uMinus]
      field_simp [h2L]
      ring
    simpa [h] using hdiff.symm
  have hQplus : Q.eval uPlus = 0 := by
    rw [eval_map_cubicQuadraticFactor (k := k) (L := L) x uPlus rfl]
    exact square_root_branch_quadratic_plus (L := L) h2L hsx
  have hQminus : Q.eval uMinus = 0 := by
    rw [eval_map_cubicQuadraticFactor (k := k) (L := L) x uMinus rfl]
    exact square_root_branch_quadratic_minus (L := L) h2L hsx
  have hTplus : TL.eval uPlus = 0 := by
    rw [eval_map_separatedTarget_eq (k := k) (L := L) f x uPlus rfl]
    rw [show Polynomial.aeval x f = Polynomial.aeval uPlus f by simpa [x, uPlus] using hplus]
    simp
  have hTminus : TL.eval uMinus = 0 := by
    rw [eval_map_separatedTarget_eq (k := k) (L := L) f x uMinus rfl]
    rw [show Polynomial.aeval x f = Polynomial.aeval uMinus f by simpa [x, uMinus] using hminus]
    simp
  have hTx : TL.eval x = 0 := by
    rw [eval_map_separatedTarget_eq (k := k) (L := L) f x x rfl]
    simp
  have hQeq : Q = X ^ 2 + C x * X + C (x ^ 2 + 1) := by
    simp [Q, cubicQuadraticFactor, map_add, map_pow, x]
  have hQmonic : Q.Monic := by
    rw [hQeq]
    rw [show (X ^ 2 + C x * X + C (x ^ 2 + 1) : L[X]) =
      C (1 : L) * X ^ 2 + C x * X + C (x ^ 2 + 1) by simp]
    rw [Polynomial.Monic, Polynomial.leadingCoeff_quadratic]
    exact one_ne_zero
  have hQnat : Q.natDegree = 2 := by
    rw [hQeq]
    rw [show (X ^ 2 + C x * X + C (x ^ 2 + 1) : L[X]) =
      C (1 : L) * X ^ 2 + C x * X + C (x ^ 2 + 1) by simp]
    exact Polynomial.natDegree_quadratic one_ne_zero
  have hQne1 : Q ≠ 1 := by
    intro h
    have hnat := congrArg Polynomial.natDegree h
    rw [hQnat] at hnat
    simp at hnat
  have hQdvdT : Q ∣ TL := by
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hQmonic]
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (TL %ₘ Q) ({uPlus, uMinus} : Finset L)
    · intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · have hrem := Polynomial.aeval_modByMonic_eq_self_of_root
          (p := TL) (q := Q) (x := uPlus) (by simpa [Polynomial.aeval_def] using hQplus)
        simpa [Polynomial.aeval_def, hTplus] using hrem
      · have hrem := Polynomial.aeval_modByMonic_eq_self_of_root
          (p := TL) (q := Q) (x := uMinus) (by simpa [Polynomial.aeval_def] using hQminus)
        simpa [Polynomial.aeval_def, hTminus] using hrem
    · have hcard : ({uPlus, uMinus} : Finset L).card = 2 := by
        simp [hbranches_ne]
      rw [hcard]
      rw [← hQnat]
      exact Polynomial.natDegree_modByMonic_lt TL hQmonic hQne1
  rcases hQdvdT with ⟨A, hA⟩
  have hQx : Q.eval x ≠ 0 := by
    rw [eval_map_cubicQuadraticFactor (k := k) (L := L) x x rfl]
    have hval : x ^ 2 + x * x + (x ^ 2 + 1) = (3 : L) * x ^ 2 + 1 := by
      ring
    rw [hval]
    simpa [x] using generic_quadratic_value_ne_zero (k := k) (L := L) h2
  have hAx : A.eval x = 0 := by
    have hx' : (Q * A).eval x = 0 := by simpa [hA] using hTx
    rw [Polynomial.eval_mul] at hx'
    exact (mul_eq_zero.mp hx').resolve_left hQx
  have hlinA : X - C x ∣ A :=
    Polynomial.dvd_iff_isRoot.mpr (by simpa [Polynomial.IsRoot] using hAx)
  rcases hlinA with ⟨B, hB⟩
  have hDLdivTL :
      D.map (algebraMap k[X] L) ∣ TL := by
    refine ⟨B, ?_⟩
    have hDfac :
        D.map (algebraMap k[X] L) = (X - C x) * Q := by
      have h := congrArg (fun P : k[X][X] => P.map (algebraMap k[X] L))
        (cubic_separated_factorization (k := k))
      simpa [D, Q, x, map_mul, map_sub] using h
    rw [hDfac, hA, hB]
    ring
  have hDKdivTK :
      D.map (algebraMap k[X] (RatFunc k)) ∣
        T.map (algebraMap k[X] (RatFunc k)) := by
    apply monic_dvd_of_map_dvd (K := RatFunc k) (L := L)
    · exact (separatedDivisor_monic (k := k)
        cubicPlusLinear_monic
        cubicPlusLinear_natDegree_pos).map (algebraMap k[X] (RatFunc k))
    · simpa [D, T, TL, Polynomial.map_map, IsScalarTower.algebraMap_eq k[X] (RatFunc k) L]
        using hDLdivTL
  have hDmonic : D.Monic :=
    separatedDivisor_monic (k := k)
      cubicPlusLinear_monic
      cubicPlusLinear_natDegree_pos
  have hdiv : D ∣ T :=
    monic_dvd_of_fraction_map_dvd (K := RatFunc k) hDmonic hDKdivTK
  exact (cubic_functional_equation_divisibility_form (k := k) (f := f)).mp
    (by simpa [D, T] using hdiv)

end CubicSquareRootFunctionalEquation

theorem division_algorithm_extraction_monic
    {g f : k[X]} (hg : g.Monic) (hgpos : 0 < g.natDegree) :
    (∃ h : k[X], f = h.comp g) ↔
      ∃ h : k[X], outerRemainder g f = C h := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h, ?_⟩
    let D := genericDivisor g
    have hD : D.Monic := genericDivisor_monic hg hgpos
    have hdiv : D ∣ ((h.comp g).map C : k[X][X]) - C h := by
      simpa [D, genericDivisor, separatedDivisor] using
        (separated_composition_converse g (X : k[X]) h)
    have hzero :
        (((h.comp g).map C : k[X][X]) - C h) %ₘ D = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hD).mpr hdiv
    have hsub :
        (((h.comp g).map C : k[X][X]) - C h) %ₘ D =
          (((h.comp g).map C : k[X][X]) %ₘ D) - ((C h : k[X][X]) %ₘ D) := by
      simpa using Polynomial.sub_modByMonic ((h.comp g).map C : k[X][X]) (C h) D
    have hCh : (C h : k[X][X]) %ₘ D = C h := by
      rw [Polynomial.modByMonic_eq_self_iff hD]
      simpa [D] using degree_C_lt_genericDivisor hg hgpos
    rw [hsub, hCh] at hzero
    simpa [outerRemainder, D] using sub_eq_zero.mp hzero
  · rintro ⟨h, hrem⟩
    refine ⟨h, ?_⟩
    let D := genericDivisor g
    have hdivision := Polynomial.modByMonic_add_div (f.map C : k[X][X]) D
    have hremD : ((f.map C : k[X][X]) %ₘ D) = C h := by
      simpa [outerRemainder, D] using hrem
    rw [hremD] at hdivision
    have hdivision' : C h + D * ((f.map C : k[X][X]) /ₘ D) = f.map C := hdivision
    have heval := congrArg
      (fun A : k[X][X] => eval₂ (subst g) (X : k[X]) A) hdivision'
    have hDzero : eval₂ (subst g) (X : k[X]) D = 0 := by
      simpa [D] using eval₂_genericDivisor g
    change
      eval₂ (subst g) (X : k[X]) (C h + D * ((f.map C : k[X][X]) /ₘ D)) =
        eval₂ (subst g) (X : k[X]) (f.map C : k[X][X]) at heval
    rw [eval₂_add, eval₂_mul, hDzero, zero_mul, add_zero] at heval
    rw [eval₂_C_subst, eval₂_map_C] at heval
    exact heval.symm

theorem division_algorithm_extraction
    {g f : k[X]} (hgpos : 0 < g.natDegree) :
    (∃ h : k[X], f = h.comp g) ↔
      ∃ h : k[X], normalizedOuterRemainder g f = C h := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h, ?_⟩
    let D := normalizedGenericDivisor g
    have hD : D.Monic := normalizedGenericDivisor_monic hgpos
    have hdivGeneric : genericDivisor g ∣ ((h.comp g).map C : k[X][X]) - C h := by
      simpa [genericDivisor, separatedDivisor] using
        (separated_composition_converse g (X : k[X]) h)
    have hglc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hgpos)
    have hunit : IsUnit (C (C g.leadingCoeff⁻¹) : k[X][X]) := by
      exact isUnit_C.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hglc)))
    have hdivD : D ∣ ((h.comp g).map C : k[X][X]) - C h := by
      unfold D normalizedGenericDivisor
      exact (hunit.mul_left_dvd).mpr hdivGeneric
    have hzero :
        (((h.comp g).map C : k[X][X]) - C h) %ₘ D = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hD).mpr hdivD
    have hsub :
        (((h.comp g).map C : k[X][X]) - C h) %ₘ D =
          (((h.comp g).map C : k[X][X]) %ₘ D) - ((C h : k[X][X]) %ₘ D) := by
      simpa using Polynomial.sub_modByMonic ((h.comp g).map C : k[X][X]) (C h) D
    have hCh : (C h : k[X][X]) %ₘ D = C h := by
      rw [Polynomial.modByMonic_eq_self_iff hD]
      simpa [D] using degree_C_lt_normalizedGenericDivisor (g := g) (h := h) hgpos
    rw [hsub, hCh] at hzero
    simpa [normalizedOuterRemainder, D] using sub_eq_zero.mp hzero
  · rintro ⟨h, hrem⟩
    refine ⟨h, ?_⟩
    let D := normalizedGenericDivisor g
    have hdivision := Polynomial.modByMonic_add_div (f.map C : k[X][X]) D
    have hremD : ((f.map C : k[X][X]) %ₘ D) = C h := by
      simpa [normalizedOuterRemainder, D] using hrem
    rw [hremD] at hdivision
    have hdivision' : C h + D * ((f.map C : k[X][X]) /ₘ D) = f.map C := hdivision
    have heval := congrArg
      (fun A : k[X][X] => eval₂ (subst g) (X : k[X]) A) hdivision'
    have hDzero : eval₂ (subst g) (X : k[X]) D = 0 := by
      simp [D, normalizedGenericDivisor, eval₂_genericDivisor]
    change
      eval₂ (subst g) (X : k[X]) (C h + D * ((f.map C : k[X][X]) /ₘ D)) =
        eval₂ (subst g) (X : k[X]) (f.map C : k[X][X]) at heval
    rw [eval₂_add, eval₂_mul, hDzero, zero_mul, add_zero] at heval
    rw [eval₂_C_subst, eval₂_map_C] at heval
    exact heval.symm

end SeparatedComposition
