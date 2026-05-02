import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace SeparatedPolynomialDifferences

variable {K : Type*} [Field K]

/-- `p(X)` as a polynomial in the first variable over `K[Y]`. -/
def liftX (p : Polynomial K) : Polynomial (Polynomial K) :=
  p.map Polynomial.C

/-- `q(Y)` as a polynomial in the first variable over `K[Y]`. -/
def liftY (q : Polynomial K) : Polynomial (Polynomial K) :=
  Polynomial.C q

/-- The generic divisor `f(X) - Z`, used for the remainder extraction proof. -/
def genericDivisor (f : Polynomial K) : Polynomial (Polynomial K) :=
  liftX f - Polynomial.C Polynomial.X

/-- The separated polynomial `f(X) - g(Y)`. -/
def sep (f g : Polynomial K) : Polynomial (Polynomial K) :=
  liftX f - liftY g

/-- Embed constants from `K` into the two-variable ring `K[Y][X]`. -/
def bivarC : K →+* Polynomial (Polynomial K) :=
  (Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp
    (Polynomial.C : K →+* Polynomial K)

/-- View a one-variable polynomial as a polynomial with coefficients in `K[Y][X]`. -/
def liftCoeff (s : Polynomial K) : Polynomial (Polynomial (Polynomial K)) :=
  s.map bivarC

lemma map_liftX_aeval (g p : Polynomial K) :
    (liftX p).map (Polynomial.aeval g).toRingHom = liftX p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show liftX (p + q) = liftX p + liftX q by simp [liftX]]
      simp only [Polynomial.map_add]
      rw [hp, hq]
  | monomial n a =>
      simp [liftX, Polynomial.map_monomial]

lemma map_genericDivisor_aeval (f g : Polynomial K) :
    (genericDivisor f).map (Polynomial.aeval g).toRingHom = sep f g := by
  rw [genericDivisor, sep, Polynomial.map_sub, map_liftX_aeval]
  simp [liftY]

lemma diag_liftX (f p : Polynomial K) :
    ((liftX p).map (Polynomial.aeval f).toRingHom).eval Polynomial.X = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show liftX (p + q) = liftX p + liftX q by simp [liftX]]
      simp only [Polynomial.map_add, Polynomial.eval_add]
      rw [hp, hq]
  | monomial n a =>
      simp [liftX, Polynomial.map_monomial, Polynomial.eval_monomial,
        Polynomial.C_mul_X_pow_eq_monomial]

lemma diag_genericDivisor (f : Polynomial K) :
    ((genericDivisor f).map (Polynomial.aeval f).toRingHom).eval Polynomial.X = 0 := by
  rw [genericDivisor, Polynomial.map_sub, Polynomial.eval_sub, diag_liftX]
  simp

lemma diag_C (f s : Polynomial K) :
    ((Polynomial.C s : Polynomial (Polynomial K)).map
      (Polynomial.aeval f).toRingHom).eval Polynomial.X = s.comp f := by
  simp [Polynomial.comp_eq_aeval]

lemma eval_liftCoeff_liftX (s f : Polynomial K) :
    (liftCoeff s).eval (liftX f) = liftX (s.comp f) := by
  induction s using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show liftCoeff (p + q) = liftCoeff p + liftCoeff q by simp [liftCoeff]]
      rw [Polynomial.eval_add, Polynomial.add_comp]
      rw [show liftX (p.comp f + q.comp f) = liftX (p.comp f) + liftX (q.comp f) by
        simp [liftX]]
      rw [hp, hq]
  | monomial n a =>
      simp [liftCoeff, liftX, bivarC, Polynomial.map_monomial, Polynomial.eval_monomial,
        Polynomial.monomial_comp, Polynomial.map_mul, Polynomial.map_pow]

lemma eval_liftCoeff_liftY (s g : Polynomial K) :
    (liftCoeff s).eval (liftY g) = liftY (s.comp g) := by
  induction s using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show liftCoeff (p + q) = liftCoeff p + liftCoeff q by simp [liftCoeff]]
      rw [Polynomial.eval_add, Polynomial.add_comp]
      rw [show liftY (p.comp g + q.comp g) = liftY (p.comp g) + liftY (q.comp g) by
        simp [liftY]]
      rw [hp, hq]
  | monomial n a =>
      simp [liftCoeff, liftY, bivarC, Polynomial.map_monomial, Polynomial.eval_monomial,
        Polynomial.monomial_comp]

lemma one_le_degree_liftX_of_monic {f : Polynomial K} (hf : f.Monic)
    (hfpos : 0 < f.natDegree) :
    (1 : WithBot Nat) <= (liftX f).degree := by
  unfold liftX
  rw [Polynomial.degree_eq_natDegree (hf.map Polynomial.C).ne_zero, hf.natDegree_map Polynomial.C]
  exact_mod_cast (Nat.succ_le_iff.mpr hfpos)

lemma degree_liftY_lt_liftX_of_monic {f g : Polynomial K} (hf : f.Monic)
    (hfpos : 0 < f.natDegree) :
    (liftY g).degree < (liftX f).degree := by
  exact lt_of_lt_of_le Polynomial.degree_C_lt
    (one_le_degree_liftX_of_monic (f := f) hf hfpos)

lemma degree_CX_lt_liftX_of_monic {f : Polynomial K} (hf : f.Monic)
    (hfpos : 0 < f.natDegree) :
    (Polynomial.C Polynomial.X : Polynomial (Polynomial K)).degree < (liftX f).degree := by
  exact lt_of_lt_of_le Polynomial.degree_C_lt
    (one_le_degree_liftX_of_monic (f := f) hf hfpos)

lemma genericDivisor_monic {f : Polynomial K} (hf : f.Monic)
    (hfpos : 0 < f.natDegree) :
    (genericDivisor f).Monic := by
  unfold genericDivisor
  exact (hf.map Polynomial.C).sub_of_left
    (degree_CX_lt_liftX_of_monic (f := f) hf hfpos)

lemma sep_monic {f g : Polynomial K} (hf : f.Monic) (hfpos : 0 < f.natDegree) :
    (sep f g).Monic := by
  unfold sep
  exact (hf.map Polynomial.C).sub_of_left
    (degree_liftY_lt_liftX_of_monic (f := f) (g := g) hf hfpos)

lemma one_le_degree_sep_of_monic {f g : Polynomial K} (hf : f.Monic)
    (hfpos : 0 < f.natDegree) :
    (1 : WithBot Nat) <= (sep f g).degree := by
  rw [sep, Polynomial.degree_sub_eq_left_of_degree_lt
    (degree_liftY_lt_liftX_of_monic (f := f) (g := g) hf hfpos)]
  exact one_le_degree_liftX_of_monic (f := f) hf hfpos

lemma liftY_degree_lt_sep_of_monic {f g q : Polynomial K} (hf : f.Monic)
    (hfpos : 0 < f.natDegree) :
    (liftY q).degree < (sep f g).degree := by
  exact lt_of_lt_of_le Polynomial.degree_C_lt
    (one_le_degree_sep_of_monic (f := f) (g := g) hf hfpos)

lemma sep_mul_C (f g : Polynomial K) (a : K) :
    sep (f * Polynomial.C a) (g * Polynomial.C a) =
      sep f g * Polynomial.C (Polynomial.C a) := by
  simp [sep, liftX, liftY, Polynomial.map_mul]
  ring

lemma aeval_injective_of_natDegree_pos {g : Polynomial K} (hgpos : 0 < g.natDegree) :
    Function.Injective (Polynomial.aeval g : Polynomial K -> Polynomial K) := by
  intro a b h
  have hsubeq : a - b = 0 := by
    have hzero : (Polynomial.aeval g) (a - b) = 0 := by
      simp [h]
    have hzeroComp : (a - b).comp g = 0 := by
      simpa [Polynomial.comp_eq_aeval] using hzero
    rw [Polynomial.comp_eq_zero_iff] at hzeroComp
    cases hzeroComp with
    | inl hsub => exact hsub
    | inr hconst =>
        exact False.elim ((Nat.ne_of_gt hgpos) (by
          rw [hconst.2, Polynomial.natDegree_C]))
  exact sub_eq_zero.mp hsubeq

lemma eq_C_coeff_zero_of_coeff_eq_zero {R : Type*} [Semiring R] {P : Polynomial R}
    (h : forall n : Nat, Not (n = 0) -> P.coeff n = 0) :
    P = Polynomial.C (P.coeff 0) := by
  ext n
  if hn : n = 0 then
    subst n
    simp
  else
    simp [Polynomial.coeff_C, hn, h n hn]

/-- Forward direction of the separated divisibility criterion, after making `f` monic.

The proof follows the remainder-extraction argument: divide `p(X)` by the generic
divisor `f(X) - Z`, specialize `Z = g(Y)`, and use injectivity of composition by
the nonconstant polynomial `g` to show that the generic remainder is constant in
`X`.
-/
theorem exists_common_outer_of_sep_dvd_monic {f g p q : Polynomial K}
    (hf : f.Monic) (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree)
    (hdiv : Dvd.dvd (sep f g) (sep p q)) :
    Exists (fun s : Polynomial K => And (p = s.comp f) (q = s.comp g)) := by
  let d := genericDivisor f
  let r := (liftX p) %ₘ d
  have hd : d.Monic := genericDivisor_monic (f := f) hf hfpos
  have hmapR : r.map (Polynomial.aeval g).toRingHom = liftY q := by
    have hmapmod := Polynomial.map_modByMonic ((Polynomial.aeval g).toRingHom)
      (p := liftX p) (q := d) hd
    have hDg : d.map (Polynomial.aeval g).toRingHom = sep f g := by
      simpa [d] using map_genericDivisor_aeval f g
    have hpmap : (liftX p).map (Polynomial.aeval g).toRingHom = liftX p :=
      map_liftX_aeval g p
    have hSep : (sep f g).Monic := sep_monic (f := f) (g := g) hf hfpos
    have hrem : (liftX p) %ₘ (sep f g) = (liftY q) %ₘ (sep f g) := by
      exact Polynomial.modByMonic_eq_of_dvd_sub hSep hdiv
    have hconstRem : (liftY q) %ₘ (sep f g) = liftY q := by
      exact (Polynomial.modByMonic_eq_self_iff hSep).mpr
        (liftY_degree_lt_sep_of_monic (f := f) (g := g) (q := q) hf hfpos)
    calc
      r.map (Polynomial.aeval g).toRingHom
          = (liftX p).map (Polynomial.aeval g).toRingHom %ₘ
              d.map (Polynomial.aeval g).toRingHom := by
              simpa [r] using hmapmod
      _ = (liftX p) %ₘ (sep f g) := by rw [hpmap, hDg]
      _ = (liftY q) %ₘ (sep f g) := hrem
      _ = liftY q := hconstRem
  have hcoeff_zero : forall n : Nat, Not (n = 0) -> r.coeff n = 0 := by
    intro n hn
    apply aeval_injective_of_natDegree_pos (g := g) hgpos
    have hc := congrArg (fun P : Polynomial (Polynomial K) => P.coeff n) hmapR
    have hc' : (Polynomial.aeval g) (r.coeff n) = (liftY q).coeff n := by
      simpa [Polynomial.coeff_map] using hc
    have hqn : (liftY q).coeff n = 0 := by
      simp [liftY, Polynomial.coeff_C, hn]
    simpa [hqn] using hc'
  have hRconst : r = Polynomial.C (r.coeff 0) :=
    eq_C_coeff_zero_of_coeff_eq_zero hcoeff_zero
  let s : Polynomial K := r.coeff 0
  have hq_eval : (Polynomial.aeval g) s = q := by
    have hc := congrArg (fun P : Polynomial (Polynomial K) => P.coeff 0) hmapR
    calc
      (Polynomial.aeval g) s = (r.map (Polynomial.aeval g).toRingHom).coeff 0 := by
        simp [s, Polynomial.coeff_map]
      _ = (liftY q).coeff 0 := hc
      _ = q := by simp [liftY]
  have hp_eval : p = s.comp f := by
    have hdivision := Polynomial.modByMonic_add_div (liftX p) d
    have hdivision' : r + d * ((liftX p) /ₘ d) = liftX p := by
      simpa [r] using hdivision
    let diag : Polynomial (Polynomial K) -> Polynomial K :=
      fun P => (P.map (Polynomial.aeval f).toRingHom).eval Polynomial.X
    have hdiag := congrArg diag hdivision'
    have hdiag_r : diag r = s.comp f := by
      rw [hRconst]
      exact diag_C f (r.coeff 0)
    have hdiag_d : diag d = 0 := by
      simpa [diag, d] using diag_genericDivisor f
    have hdiag_lift : diag (liftX p) = p := by
      simpa [diag] using diag_liftX f p
    have hdiag_r' :
        (r.map (Polynomial.aeval f).toRingHom).eval Polynomial.X = s.comp f := by
      simpa [diag] using hdiag_r
    have hdiag_d' :
        (d.map (Polynomial.aeval f).toRingHom).eval Polynomial.X = 0 := by
      simpa [diag] using hdiag_d
    have hdiag_lift' :
        ((liftX p).map (Polynomial.aeval f).toRingHom).eval Polynomial.X = p := by
      simpa [diag] using hdiag_lift
    simp only [diag, Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
      Polynomial.eval_mul] at hdiag
    rw [hdiag_r', hdiag_d', zero_mul, add_zero, hdiag_lift'] at hdiag
    exact hdiag.symm
  exact Exists.intro s (And.intro hp_eval (by
    simpa [Polynomial.comp_eq_aeval] using hq_eval.symm))

/-- If `p` and `q` are obtained by composing with a common outer polynomial, then
`f(X)-g(Y)` divides `p(X)-q(Y)`. This direction does not need monicity or
nonconstancy assumptions. -/
theorem sep_dvd_of_common_outer (s f g : Polynomial K) :
    Dvd.dvd (sep f g) (sep (s.comp f) (s.comp g)) := by
  have h :=
    Polynomial.sub_dvd_eval_sub (liftX f) (liftY g) (liftCoeff s)
  simpa [sep, eval_liftCoeff_liftX, eval_liftCoeff_liftY] using h

/-- The separated divisibility criterion in the monic-`f` normalization used by
the formal proof. -/
theorem sep_dvd_iff_exists_common_outer_monic {f g p q : Polynomial K}
    (hf : f.Monic) (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree) :
    Dvd.dvd (sep f g) (sep p q) ↔
      Exists (fun s : Polynomial K => And (p = s.comp f) (q = s.comp g)) := by
  constructor
  · exact exists_common_outer_of_sep_dvd_monic hf hfpos hgpos
  · rintro ⟨s, hp, hq⟩
    rw [hp, hq]
    exact sep_dvd_of_common_outer s f g

/-- The separated divisibility criterion over a field, in the same nested-polynomial
model of `K[X,Y]` used throughout this file. -/
theorem sep_dvd_iff_exists_common_outer {f g p q : Polynomial K}
    (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree) :
    Dvd.dvd (sep f g) (sep p q) ↔
      Exists (fun s : Polynomial K => And (p = s.comp f) (q = s.comp g)) := by
  constructor
  · intro hdiv
    have hfne : f ≠ 0 := by
      intro hf0
      rw [hf0, Polynomial.natDegree_zero] at hfpos
      exact (Nat.lt_irrefl 0) hfpos
    have hflc : f.leadingCoeff ≠ 0 := by
      rwa [Polynomial.leadingCoeff_ne_zero]
    let c : K := f.leadingCoeff⁻¹
    let F : Polynomial K := f * Polynomial.C c
    let G : Polynomial K := g * Polynomial.C c
    have hFmonic : F.Monic := by
      simpa [F, c] using Polynomial.monic_mul_leadingCoeff_inv hfne
    have hFpos : 0 < F.natDegree := by
      simpa [F, c] using
        (Polynomial.natDegree_mul_leadingCoeff_inv f (q := f) hfne).symm ▸ hfpos
    have hGpos : 0 < G.natDegree := by
      simpa [G, c] using
        (Polynomial.natDegree_mul_leadingCoeff_inv g (q := f) hfne).symm ▸ hgpos
    let u : Polynomial (Polynomial K) := Polynomial.C (Polynomial.C c)
    let v : Polynomial (Polynomial K) := Polynomial.C (Polynomial.C f.leadingCoeff)
    have huv : u * v = 1 := by
      change Polynomial.C (Polynomial.C f.leadingCoeff⁻¹) *
          Polynomial.C (Polynomial.C f.leadingCoeff) = 1
      rw [← Polynomial.C_mul, ← Polynomial.C_mul,
        inv_mul_cancel₀ hflc, Polynomial.C_1, Polynomial.C_1]
    have hsepFG : sep F G = sep f g * u := by
      simpa [F, G, u, c] using sep_mul_C f g c
    have hdivNorm : Dvd.dvd (sep F G) (sep p q) := by
      rcases hdiv with ⟨H, hH⟩
      refine ⟨v * H, ?_⟩
      calc
        sep p q = sep f g * H := hH
        _ = (sep f g * u) * (v * H) := by
          rw [mul_assoc, ← mul_assoc u v H, huv, one_mul]
        _ = sep F G * (v * H) := by rw [hsepFG]
    rcases exists_common_outer_of_sep_dvd_monic hFmonic hFpos hGpos hdivNorm with
      ⟨s, hpF, hqG⟩
    let lin : Polynomial K := Polynomial.C c * Polynomial.X
    let t : Polynomial K := s.comp lin
    have hlin_f : lin.comp f = F := by
      change (Polynomial.C c * Polynomial.X).comp f = f * Polynomial.C c
      rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
      ring
    have hlin_g : lin.comp g = G := by
      change (Polynomial.C c * Polynomial.X).comp g = g * Polynomial.C c
      rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
      ring
    have ht_f : t.comp f = s.comp F := by
      change (s.comp lin).comp f = s.comp F
      rw [Polynomial.comp_assoc, hlin_f]
    have ht_g : t.comp g = s.comp G := by
      change (s.comp lin).comp g = s.comp G
      rw [Polynomial.comp_assoc, hlin_g]
    exact ⟨t, hpF.trans ht_f.symm, hqG.trans ht_g.symm⟩
  · rintro ⟨s, hp, hq⟩
    rw [hp, hq]
    exact sep_dvd_of_common_outer s f g

end SeparatedPolynomialDifferences
