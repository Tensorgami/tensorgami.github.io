import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# A weighting argument for convergence in measure

This file formalizes the main weighting mechanisms from the note
`A Weighting Argument for Pointwise Convergence to Convergence in Measure`.

The main theorem is
`exists_conull_pos_measurable_weight_uniformOn_tendstoInMeasure_of_ae_tendsto`:
on a sigma-finite measure space, a sequence of real-valued measurable functions
which tends to `0` almost everywhere can be multiplied by a strictly positive
measurable finite-valued weight so that it tends uniformly to `0` on a conull
set and therefore tends to `0` in measure.  The file also includes the shorter
dominated-convergence route to convergence in measure.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace PointwiseWeighting

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The pointwise envelope `sup_n ||f_n x||`, valued in `ℝ≥0∞`. -/
noncomputable def envelope (f : ℕ → α → ℝ) (x : α) : ℝ≥0∞ :=
  ⨆ n : ℕ, (‖f n x‖₊ : ℝ≥0∞)

lemma measurable_envelope {f : ℕ → α → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (envelope f) := by
  unfold envelope
  exact Measurable.iSup fun n => (hf n).nnnorm.coe_nnreal_ennreal

omit [MeasurableSpace α] in
lemma envelope_ne_top_of_tendsto {f : ℕ → α → ℝ} {x : α}
    (hx : Tendsto (fun n => f n x) atTop (nhds 0)) :
    envelope f x ≠ ∞ := by
  unfold envelope
  rw [← lt_top_iff_ne_top, ENNReal.iSup_coe_lt_top]
  exact (hx.nnnorm.isBoundedUnder_le).bddAbove_range

omit [MeasurableSpace α] in
lemma nnnorm_le_envelope_toReal {f : ℕ → α → ℝ} {x : α}
    (hx : envelope f x ≠ ∞) (n : ℕ) :
    ‖f n x‖ ≤ (envelope f x).toReal := by
  have hle : (‖f n x‖₊ : ℝ≥0∞) ≤ envelope f x := by
    simpa [envelope] using (le_iSup (fun k : ℕ => (‖f k x‖₊ : ℝ≥0∞)) n)
  simpa using ENNReal.toReal_mono hx hle

/--
The envelope sublevel sets are measurable.  These are the Lean counterpart of
the measurable boundedness pieces `B_j = {x : M(x) ≤ j}` in the note.
-/
lemma measurableSet_envelope_le_nat {f : ℕ → α → ℝ} (hf : ∀ n, Measurable (f n))
    (j : ℕ) : MeasurableSet {x | envelope f x ≤ (j : ℝ≥0∞)} := by
  exact measurableSet_le (measurable_envelope hf) measurable_const

omit [MeasurableSpace α] in
lemma iUnion_envelope_le_nat_of_finite {f : ℕ → α → ℝ}
    (hfinite : ∀ x, envelope f x ≠ ∞) :
    (⋃ j : ℕ, {x | envelope f x ≤ (j : ℝ≥0∞)}) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hxmem : envelope f x ∈ (⋃ j : ℕ, Set.Iic (j : ℝ≥0∞)) := by
    rw [ENNReal.iUnion_Iic_coe_nat]
    simpa using hfinite x
  rcases Set.mem_iUnion.mp hxmem with ⟨j, hj⟩
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

omit [MeasurableSpace α] in
lemma norm_le_of_envelope_le_nat {f : ℕ → α → ℝ} {x : α} {j n : ℕ}
    (hx : envelope f x ≤ (j : ℝ≥0∞)) :
    ‖f n x‖ ≤ (j : ℝ) := by
  have hle_env : (‖f n x‖₊ : ℝ≥0∞) ≤ envelope f x := by
    simpa [envelope] using (le_iSup (fun k : ℕ => (‖f k x‖₊ : ℝ≥0∞)) n)
  have hle : (‖f n x‖₊ : ℝ≥0∞) ≤ (j : ℝ≥0∞) := hle_env.trans hx
  have htop : (j : ℝ≥0∞) ≠ ∞ := by simp
  have hreal := ENNReal.toReal_mono htop hle
  simpa using hreal

omit [MeasurableSpace α] in
lemma norm_mul_envelope_div_le {f : ℕ → α → ℝ} {x : α} {c : ℝ}
    (hc : 0 ≤ c) (hx : envelope f x ≠ ∞) (n : ℕ) :
    ‖f n x * (c / (1 + (envelope f x).toReal))‖ ≤ c := by
  have hnorm_le : ‖f n x‖ ≤ (envelope f x).toReal :=
    nnnorm_le_envelope_toReal hx n
  have hM_nonneg : 0 ≤ (envelope f x).toReal := ENNReal.toReal_nonneg
  have hden_pos : 0 < 1 + (envelope f x).toReal := by positivity
  have hquot_nonneg : 0 ≤ c / (1 + (envelope f x).toReal) := by positivity
  calc
    ‖f n x * (c / (1 + (envelope f x).toReal))‖
        = ‖f n x‖ * (c / (1 + (envelope f x).toReal)) := by
          rw [norm_mul]
          congr 1
          exact Real.norm_of_nonneg hquot_nonneg
    _ ≤ (envelope f x).toReal * (c / (1 + (envelope f x).toReal)) := by
          exact mul_le_mul_of_nonneg_right hnorm_le hquot_nonneg
    _ ≤ c := by
          have hfrac : (envelope f x).toReal / (1 + (envelope f x).toReal) ≤ 1 := by
            rw [div_le_one hden_pos]
            linarith
          calc
            (envelope f x).toReal * (c / (1 + (envelope f x).toReal))
                = c * ((envelope f x).toReal / (1 + (envelope f x).toReal)) := by
                  ring
            _ ≤ c * 1 := by
                  exact mul_le_mul_of_nonneg_left hfrac hc
            _ = c := by ring

/-- Pointwise boundedness stratification for everywhere convergence. -/
theorem pointwise_boundedness_stratification
    {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∃ B : ℕ → Set α,
      (∀ j, MeasurableSet (B j)) ∧
      (⋃ j, B j) = Set.univ ∧
      ∀ j n x, x ∈ B j → ‖f n x‖ ≤ (j : ℝ) := by
  refine ⟨fun j => {x | envelope f x ≤ (j : ℝ≥0∞)}, ?_, ?_, ?_⟩
  · exact measurableSet_envelope_le_nat hf
  · exact iUnion_envelope_le_nat_of_finite
      (fun x => envelope_ne_top_of_tendsto (f := f) (hlim x))
  · intro j n x hx
    exact norm_le_of_envelope_le_nat hx

/--
Almost-everywhere version of the boundedness stratification: the same
measurable sublevel pieces cover a conull set under a.e. convergence.
-/
theorem ae_pointwise_boundedness_stratification
    {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∃ B : ℕ → Set α,
      (∀ j, MeasurableSet (B j)) ∧
      μ ((⋃ j, B j)ᶜ) = 0 ∧
      ∀ j n x, x ∈ B j → ‖f n x‖ ≤ (j : ℝ) := by
  let B : ℕ → Set α := fun j => {x | envelope f x ≤ (j : ℝ≥0∞)}
  have hcover_ae : ∀ᵐ x ∂μ, x ∈ ⋃ j, B j := by
    filter_upwards [hlim] with x hx
    have hxmem : envelope f x ∈ (⋃ j : ℕ, Set.Iic (j : ℝ≥0∞)) := by
      rw [ENNReal.iUnion_Iic_coe_nat]
      simpa using envelope_ne_top_of_tendsto (f := f) hx
    rcases Set.mem_iUnion.mp hxmem with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  refine ⟨B, ?_, ?_, ?_⟩
  · intro j
    exact measurableSet_envelope_le_nat hf j
  · exact mem_ae_iff.mp hcover_ae
  · intro j n x hx
    exact norm_le_of_envelope_le_nat hx

lemma ennreal_eq_zero_of_forall_le_inv_nat_succ {a : ℝ≥0∞}
    (hle : ∀ k : ℕ, a ≤ ENNReal.ofReal (((k + 1 : ℕ) : ℝ)⁻¹)) :
    a = 0 := by
  have hlim_real : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ)⁻¹)) atTop (nhds 0) := by
    simpa [one_div, Nat.cast_add] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim :
      Tendsto (fun k : ℕ => ENNReal.ofReal (((k + 1 : ℕ) : ℝ)⁻¹)) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hlim_real
  exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hle)) bot_le

/-- The dominated-convergence weight associated to a positive integrable `g`. -/
noncomputable def dominatedWeight (f : ℕ → α → ℝ) (g : α → ℝ≥0) (x : α) : ℝ :=
  (g x : ℝ) / (1 + (envelope f x).toReal)

lemma measurable_dominatedWeight {f : ℕ → α → ℝ} {g : α → ℝ≥0}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) :
    Measurable (dominatedWeight f g) := by
  unfold dominatedWeight
  exact hg.coe_nnreal_real.div
    (measurable_const.add ((measurable_envelope hf).ennreal_toReal))

omit [MeasurableSpace α] in
lemma dominatedWeight_pos {f : ℕ → α → ℝ} {g : α → ℝ≥0}
    (hgpos : ∀ x, 0 < g x) (x : α) :
    0 < dominatedWeight f g x := by
  unfold dominatedWeight
  exact div_pos (by exact_mod_cast hgpos x) (by positivity)

omit [MeasurableSpace α] in
lemma norm_mul_dominatedWeight_le {f : ℕ → α → ℝ} {g : α → ℝ≥0} {x : α}
    (hx : Tendsto (fun n => f n x) atTop (nhds 0)) (n : ℕ) :
    ‖f n x * dominatedWeight f g x‖ ≤ (g x : ℝ) := by
  have hM_ne_top : envelope f x ≠ ∞ := envelope_ne_top_of_tendsto hx
  have hnorm_le : ‖f n x‖ ≤ (envelope f x).toReal :=
    nnnorm_le_envelope_toReal hM_ne_top n
  have hM_nonneg : 0 ≤ (envelope f x).toReal := ENNReal.toReal_nonneg
  have hden_pos : 0 < 1 + (envelope f x).toReal := by positivity
  have hg_nonneg : 0 ≤ (g x : ℝ) := by positivity
  have hquot_nonneg : 0 ≤ (g x : ℝ) / (1 + (envelope f x).toReal) := by positivity
  calc
    ‖f n x * dominatedWeight f g x‖
        = ‖f n x‖ * ‖dominatedWeight f g x‖ := by
          rw [norm_mul]
    _ = ‖f n x‖ * ((g x : ℝ) / (1 + (envelope f x).toReal)) := by
          congr 1
          unfold dominatedWeight
          exact Real.norm_of_nonneg hquot_nonneg
    _ ≤ (envelope f x).toReal * ((g x : ℝ) / (1 + (envelope f x).toReal)) := by
          exact mul_le_mul_of_nonneg_right hnorm_le hquot_nonneg
    _ ≤ (g x : ℝ) := by
          have hfrac : (envelope f x).toReal / (1 + (envelope f x).toReal) ≤ 1 := by
            rw [div_le_one hden_pos]
            linarith
          calc
            (envelope f x).toReal * ((g x : ℝ) / (1 + (envelope f x).toReal))
                = (g x : ℝ) * ((envelope f x).toReal / (1 + (envelope f x).toReal)) := by
                  ring
            _ ≤ (g x : ℝ) * 1 := by
                  exact mul_le_mul_of_nonneg_left hfrac hg_nonneg
            _ = (g x : ℝ) := by ring

/--
Finite-measure Egorov form used in the note: on a measurable set of finite
measure, almost-everywhere convergence to `0` is uniform on a measurable subset
whose complement has arbitrarily small measure.
-/
theorem egorov_uniformOn_large_subset
    {s : Set α} {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n)) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hlim : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set α,
      A ⊆ s ∧
      MeasurableSet A ∧
      μ (s \ A) ≤ ENNReal.ofReal ε ∧
      TendstoUniformlyOn f (fun _ => (0 : ℝ)) atTop A := by
  obtain ⟨t, htsub, htmeas, htmeasure, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto
      (fun n => (hf n).stronglyMeasurable) stronglyMeasurable_const hsm hs hlim hε
  refine ⟨s \ t, Set.diff_subset, hsm.diff htmeas, ?_, hunif⟩
  exact (measure_mono (by
    intro x hx
    rcases hx with ⟨hxs, hxnot⟩
    by_contra hxt
    exact hxnot ⟨hxs, hxt⟩)).trans htmeasure

/--
Sigma-finite Egorov bookkeeping: a.e. convergence is uniform on countably many
measurable pieces whose union is conull.
-/
theorem exists_countable_measurable_uniformOn_cover_ae
    [SigmaFinite μ] {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∃ A : ℕ × ℕ → Set α,
      (∀ p, MeasurableSet (A p)) ∧
      μ ((⋃ p : ℕ × ℕ, A p)ᶜ) = 0 ∧
      ∀ p, TendstoUniformlyOn f (fun _ => (0 : ℝ)) atTop (A p) := by
  classical
  let S : ℕ → Set α := spanningSets μ
  have hpiece_exists : ∀ p : ℕ × ℕ,
      ∃ A : Set α,
        A ⊆ S p.1 ∧
        MeasurableSet A ∧
        μ (S p.1 \ A) ≤ ENNReal.ofReal (((p.2 + 1 : ℕ) : ℝ)⁻¹) ∧
        TendstoUniformlyOn f (fun _ => (0 : ℝ)) atTop A := by
    intro p
    have hlimS : ∀ᵐ x ∂μ, x ∈ S p.1 → Tendsto (fun n => f n x) atTop (nhds 0) := by
      filter_upwards [hlim] with x hx _hxs
      exact hx
    have hε : 0 < (((p.2 + 1 : ℕ) : ℝ)⁻¹) := by
      exact inv_pos.mpr (by exact_mod_cast Nat.succ_pos p.2)
    exact egorov_uniformOn_large_subset (μ := μ) hf (measurableSet_spanningSets μ p.1)
      (measure_spanningSets_lt_top μ p.1).ne hlimS hε
  let A : ℕ × ℕ → Set α := fun p => Classical.choose (hpiece_exists p)
  have hA_meas : ∀ p, MeasurableSet (A p) :=
    fun p => (Classical.choose_spec (hpiece_exists p)).2.1
  have hA_measure : ∀ p, μ (S p.1 \ A p) ≤ ENNReal.ofReal (((p.2 + 1 : ℕ) : ℝ)⁻¹) :=
    fun p => (Classical.choose_spec (hpiece_exists p)).2.2.1
  have hA_unif : ∀ p, TendstoUniformlyOn f (fun _ => (0 : ℝ)) atTop (A p) :=
    fun p => (Classical.choose_spec (hpiece_exists p)).2.2.2
  refine ⟨A, hA_meas, ?_, hA_unif⟩
  have hlocal_null : ∀ r : ℕ, μ (S r \ ⋃ k : ℕ, A (r, k)) = 0 := by
    intro r
    apply ennreal_eq_zero_of_forall_le_inv_nat_succ
    intro k
    have hsubset : S r \ (⋃ k : ℕ, A (r, k)) ⊆ S r \ A (r, k) := by
      intro x hx
      exact ⟨hx.1, fun hxA => hx.2 (Set.mem_iUnion.mpr ⟨k, hxA⟩)⟩
    exact (measure_mono hsubset).trans (hA_measure (r, k))
  let G : Set α := (⋃ p : ℕ × ℕ, A p)ᶜ
  have hG_eq : G = ⋃ r : ℕ, G ∩ S r := by
    rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  change μ G = 0
  rw [hG_eq]
  apply measure_iUnion_null
  intro r
  apply measure_mono_null ?_ (hlocal_null r)
  intro x hx
  refine ⟨hx.2, ?_⟩
  intro hxU
  rcases Set.mem_iUnion.mp hxU with ⟨k, hxAk⟩
  exact hx.1 (Set.mem_iUnion.mpr ⟨(r, k), hxAk⟩)

/--
Uniformization from a countable measurable cover.  If `f_n` is uniformly
convergent on each member of a conull countable cover, then a positive
measurable envelope weight makes `f_n h` converge uniformly on a conull set.
-/
theorem exists_conull_measurable_pos_weight_tendstoUniformlyOn_of_countable_cover
    {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n))
    {C : ℕ → Set α}
    (hCmeas : ∀ q, MeasurableSet (C q))
    (hUnull : μ ((⋃ q : ℕ, C q)ᶜ) = 0)
    (hunif : ∀ q, TendstoUniformlyOn f (fun _ => (0 : ℝ)) atTop (C q))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∃ A : Set α, ∃ h : α → ℝ,
      MeasurableSet A ∧
      μ Aᶜ = 0 ∧
      Measurable h ∧
      (∀ x, 0 < h x) ∧
      TendstoUniformlyOn (fun n x => f n x * h x) (fun _ => (0 : ℝ)) atTop A := by
  classical
  let U : Set α := ⋃ q : ℕ, C q
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion hCmeas
  let finiteSet : Set α := {x | envelope f x ≠ ∞}
  have hfinite_meas : MeasurableSet finiteSet := by
    have htop_meas : MeasurableSet ((envelope f) ⁻¹' ({∞} : Set ℝ≥0∞)) :=
      (measurable_envelope hf) (measurableSet_singleton ∞)
    convert htop_meas.compl using 1
  have hfinite_ae : ∀ᵐ x ∂μ, x ∈ finiteSet := by
    filter_upwards [hlim] with x hx
    exact envelope_ne_top_of_tendsto (f := f) hx
  have hfinite_null : μ finiteSetᶜ = 0 := mem_ae_iff.mp hfinite_ae
  let A : Set α := U ∩ finiteSet
  let cover : ℕ → Set α
    | 0 => Uᶜ
    | q + 1 => C q
  have hcover_all : ∀ x : α, ∃ n, x ∈ cover n := by
    intro x
    by_cases hx : x ∈ U
    · rcases Set.mem_iUnion.mp hx with ⟨q, hq⟩
      exact ⟨q + 1, hq⟩
    · exact ⟨0, hx⟩
  have hcover_meas : ∀ n, MeasurableSet (cover n) := by
    intro n
    cases n with
    | zero => simpa [cover] using hUmeas.compl
    | succ q => simpa [cover] using hCmeas q
  letI : ∀ x : α, DecidablePred (fun n => x ∈ cover n) := fun _ => Classical.decPred _
  let idx : α → ℕ := fun x => Nat.find (hcover_all x)
  have hidx_meas : Measurable idx := by
    exact measurable_find (p := fun x n => x ∈ cover n) hcover_all hcover_meas
  let w : α → ℝ := fun x => if idx x = 0 then (1 : ℝ) else ((idx x : ℕ) : ℝ)⁻¹
  let h : α → ℝ := fun x => w x / (1 + (envelope f x).toReal)
  have hidx_mem : ∀ x, x ∈ cover (idx x) := by
    intro x
    exact Nat.find_spec (hcover_all x)
  have hidx_ne_zero_of_mem_U : ∀ {x}, x ∈ U → idx x ≠ 0 := by
    intro x hxU hzero
    have hxcover := hidx_mem x
    have hxUc : x ∈ Uᶜ := by
      simpa [idx, cover, hzero] using hxcover
    exact hxUc hxU
  have hw_pos : ∀ x, 0 < w x := by
    intro x
    by_cases hzero : idx x = 0
    · simp [w, hzero]
    · have hidx_pos_nat : 0 < idx x := Nat.pos_of_ne_zero hzero
      have hidx_pos_real : 0 < ((idx x : ℕ) : ℝ) := by exact_mod_cast hidx_pos_nat
      simp [w, hzero, inv_pos.mpr hidx_pos_real]
  have hw_le_one : ∀ x, w x ≤ 1 := by
    intro x
    by_cases hzero : idx x = 0
    · simp [w, hzero]
    · have hidx_pos_nat : 0 < idx x := Nat.pos_of_ne_zero hzero
      have hidx_ge_one_real : (1 : ℝ) ≤ ((idx x : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hidx_pos_nat
      have hinv : (((idx x : ℕ) : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hidx_ge_one_real
      simpa [w, hzero] using hinv
  have hh_pos : ∀ x, 0 < h x := by
    intro x
    dsimp [h]
    exact div_pos (hw_pos x) (by positivity)
  have hh_le_one : ∀ x, h x ≤ 1 := by
    intro x
    dsimp [h]
    have hden_pos : 0 < 1 + (envelope f x).toReal := by positivity
    have hden_ge_one : (1 : ℝ) ≤ 1 + (envelope f x).toReal := by
      nlinarith [ENNReal.toReal_nonneg (a := envelope f x)]
    have hdiv_le_w : w x / (1 + (envelope f x).toReal) ≤ w x := by
      rw [div_le_iff₀ hden_pos]
      nlinarith [mul_le_mul_of_nonneg_left hden_ge_one (le_of_lt (hw_pos x))]
    exact hdiv_le_w.trans (hw_le_one x)
  have hw_meas : Measurable w := by
    have hset : MeasurableSet (idx ⁻¹' ({0} : Set ℕ)) :=
      hidx_meas (measurableSet_singleton 0)
    have hset' : MeasurableSet {x | idx x = 0} := by
      simpa [Set.preimage, Set.mem_singleton_iff] using hset
    exact measurable_const.ite hset'
      (((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp hidx_meas).inv)
  have hh_meas : Measurable h := by
    dsimp [h]
    exact hw_meas.div (measurable_const.add ((measurable_envelope hf).ennreal_toReal))
  refine ⟨A, h, hUmeas.inter hfinite_meas, ?_, hh_meas, hh_pos, ?_⟩
  · dsimp [A]
    rw [Set.compl_inter]
    exact measure_union_null hUnull hfinite_null
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htail_event : ∀ᶠ m : ℕ in atTop, (((m : ℕ) : ℝ)⁻¹) < ε :=
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (isOpen_Iio.mem_nhds hε)
    rcases eventually_atTop.1 htail_event with ⟨N, hNtail⟩
    have hfinite_event : ∀ᶠ n in atTop, ∀ q ∈ Finset.range N, ∀ x ∈ C q,
        dist (0 : ℝ) (f n x) < ε := by
      rw [Filter.eventually_all_finset]
      intro q _hq
      exact (Metric.tendstoUniformlyOn_iff.mp (hunif q)) ε hε
    filter_upwards [hfinite_event] with n hn x hxA
    have hxU : x ∈ U := hxA.1
    have hxfinite : x ∈ finiteSet := hxA.2
    have hidx_ne0 : idx x ≠ 0 := hidx_ne_zero_of_mem_U hxU
    by_cases hlt : idx x < N
    · rcases Nat.exists_eq_succ_of_ne_zero hidx_ne0 with ⟨q, hqeq⟩
      have hq_lt : q < N := by omega
      have hxC : x ∈ C q := by
        have hxcover := hidx_mem x
        simpa [cover, hqeq] using hxcover
      have hfsmall : dist (0 : ℝ) (f n x) < ε := hn q (Finset.mem_range.mpr hq_lt) x hxC
      have hnorm_f_small : ‖f n x‖ < ε := by
        simpa [dist_eq_norm] using hfsmall
      have hnorm_le : ‖f n x * h x‖ ≤ ‖f n x‖ := by
        rw [norm_mul]
        have hh_nonneg : 0 ≤ h x := (hh_pos x).le
        have hhnorm : ‖h x‖ = h x := Real.norm_of_nonneg hh_nonneg
        rw [hhnorm]
        exact mul_le_of_le_one_right (norm_nonneg _) (hh_le_one x)
      simpa [dist_eq_norm] using lt_of_le_of_lt hnorm_le hnorm_f_small
    · have hidx_ge : N ≤ idx x := le_of_not_gt hlt
      have hw_lt : w x < ε := by
        have htail := hNtail (idx x) hidx_ge
        simpa [w, hidx_ne0] using htail
      have hprod_le : ‖f n x * h x‖ ≤ w x := by
        have hle := norm_mul_envelope_div_le (f := f) (x := x) (c := w x)
          (le_of_lt (hw_pos x)) hxfinite n
        simpa [h] using hle
      simpa [dist_eq_norm] using lt_of_le_of_lt hprod_le hw_lt

/-- Sigma-finite conull uniformization by a positive measurable weight. -/
theorem exists_conull_pos_measurable_weight_tendstoUniformlyOn_of_ae_tendsto
    [SigmaFinite μ] {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∃ A : Set α, ∃ h : α → ℝ,
      MeasurableSet A ∧
      μ Aᶜ = 0 ∧
      Measurable h ∧
      (∀ x, 0 < h x) ∧
      TendstoUniformlyOn (fun n x => f n x * h x) (fun _ => (0 : ℝ)) atTop A := by
  obtain ⟨P, hPmeas, hPnull, hPunif⟩ :=
    exists_countable_measurable_uniformOn_cover_ae (μ := μ) hf hlim
  let C : ℕ → Set α := fun n => P (Nat.unpair n)
  have hCmeas : ∀ q, MeasurableSet (C q) := fun q => hPmeas (Nat.unpair q)
  have hUeq : (⋃ q : ℕ, C q) = (⋃ p : ℕ × ℕ, P p) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨q, hq⟩
      exact Set.mem_iUnion.mpr ⟨Nat.unpair q, hq⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨p, hp⟩
      refine Set.mem_iUnion.mpr ⟨Nat.pair p.1 p.2, ?_⟩
      simpa [C, Nat.unpair_pair] using hp
  have hUnull : μ ((⋃ q : ℕ, C q)ᶜ) = 0 := by
    simpa [hUeq] using hPnull
  have hCunif : ∀ q, TendstoUniformlyOn f (fun _ => (0 : ℝ)) atTop (C q) :=
    fun q => hPunif (Nat.unpair q)
  exact exists_conull_measurable_pos_weight_tendstoUniformlyOn_of_countable_cover
    (μ := μ) hf hCmeas hUnull hCunif hlim

theorem tendstoInMeasure_of_tendstoUniformlyOn_conull
    {E : Type*} [PseudoMetricSpace E] {F : ℕ → α → E} {g : α → E}
    {A : Set α} (hA0 : μ Aᶜ = 0)
    (hunif : TendstoUniformlyOn F g atTop A) :
    TendstoInMeasure μ F atTop g := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hev := (Metric.tendstoUniformlyOn_iff.mp hunif) ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with n hn
  apply Eq.symm
  apply le_antisymm ?_ bot_le
  refine le_of_eq (measure_mono_null (μ := μ) ?_ hA0)
  intro x hxBad hxA
  have hlt : dist (F n x) (g x) < ε := by simpa [dist_comm] using hn x hxA
  exact not_le_of_gt hlt hxBad

/--
Sigma-finite version matching the main uniformization statement, including the
same weight's convergence in measure.
-/
theorem exists_conull_pos_measurable_weight_uniformOn_tendstoInMeasure_of_ae_tendsto
    [SigmaFinite μ] {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∃ A : Set α, ∃ h : α → ℝ,
      MeasurableSet A ∧
      μ Aᶜ = 0 ∧
      Measurable h ∧
      (∀ x, 0 < h x) ∧
      TendstoUniformlyOn (fun n x => f n x * h x) (fun _ => (0 : ℝ)) atTop A ∧
      TendstoInMeasure μ (fun n x => f n x * h x) atTop (fun _ => (0 : ℝ)) := by
  obtain ⟨A, h, hA_meas, hA_null, hh_meas, hh_pos, hunif⟩ :=
    exists_conull_pos_measurable_weight_tendstoUniformlyOn_of_ae_tendsto (μ := μ) hf hlim
  exact ⟨A, h, hA_meas, hA_null, hh_meas, hh_pos, hunif,
    tendstoInMeasure_of_tendstoUniformlyOn_conull (μ := μ) hA_null hunif⟩

/--
Sigma-finite dominated-convergence form of the weighting argument.

If `f_n → 0` almost everywhere and all `f_n` are measurable, then there is a
strictly positive measurable real-valued weight `h` such that `f_n * h → 0` in
measure.  The proof also gives `L¹` convergence, expressed as convergence of the
`eLpNorm` with exponent `1`.
-/
theorem exists_pos_measurable_weight_tendstoInMeasure_of_ae_tendsto
    [SigmaFinite μ] {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∃ h : α → ℝ,
      Measurable h ∧
      (∀ x, 0 < h x) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x * h x) 1 μ) atTop (nhds 0) ∧
      TendstoInMeasure μ (fun n x => f n x * h x) atTop (fun _ => 0) := by
  obtain ⟨g, hgpos, hg_meas, hg_lintegral_lt⟩ :=
    exists_pos_lintegral_lt_of_sigmaFinite μ (ε := (1 : ℝ≥0∞)) (by simp)
  let h : α → ℝ := dominatedWeight f g
  have h_meas : Measurable h := measurable_dominatedWeight hf hg_meas
  have h_pos : ∀ x, 0 < h x := dominatedWeight_pos hgpos
  have hg_int_toReal :
      Integrable (fun x => ((g x : ℝ≥0∞).toReal)) μ :=
    integrable_toReal_of_lintegral_ne_top
      hg_meas.coe_nnreal_ennreal.aemeasurable
      (ne_top_of_lt hg_lintegral_lt)
  have hg_int : Integrable (fun x => (g x : ℝ)) μ := by
    simpa using hg_int_toReal
  have hF_meas : ∀ n, AEStronglyMeasurable (fun x => f n x * h x) μ := by
    intro n
    exact ((hf n).mul h_meas).aestronglyMeasurable
  have h_bound : ∀ n, ∀ᵐ x ∂μ, ‖f n x * h x‖ ≤ (g x : ℝ) := by
    intro n
    filter_upwards [hlim] with x hx
    exact norm_mul_dominatedWeight_le (f := f) (g := g) hx n
  have h_pointwise : ∀ᵐ x ∂μ,
      Tendsto (fun n => f n x * h x) atTop (nhds (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa using hx.mul tendsto_const_nhds
  have h_lintegral :
      Tendsto
        (fun n => ∫⁻ x, ENNReal.ofReal ‖f n x * h x - (0 : ℝ)‖ ∂μ)
        atTop (nhds 0) :=
    tendsto_lintegral_norm_of_dominated_convergence
      hF_meas hg_int.hasFiniteIntegral h_bound h_pointwise
  have h_eLp :
      Tendsto (fun n => eLpNorm (fun x => f n x * h x) 1 μ) atTop (nhds 0) := by
    simpa [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply, Real.norm_eq_abs,
      ← ofReal_norm_eq_enorm] using h_lintegral
  refine ⟨h, h_meas, h_pos, h_eLp, ?_⟩
  have h_eLp_sub :
      Tendsto
        (fun n => eLpNorm ((fun x => f n x * h x) - (fun _ => (0 : ℝ))) 1 μ)
        atTop (nhds 0) := by
    have h_eq :
        (fun n => eLpNorm ((fun x => f n x * h x) - (fun _ => (0 : ℝ))) 1 μ)
          = fun n => eLpNorm (fun x => f n x * h x) 1 μ := by
      funext n
      congr 1
      funext x
      simp [Pi.sub_apply]
    simpa [h_eq] using h_eLp
  exact tendstoInMeasure_of_tendsto_eLpNorm
    (p := (1 : ℝ≥0∞)) (by simp)
    hF_meas aestronglyMeasurable_const h_eLp_sub

/-- The real-line conull uniformization theorem from the note. -/
theorem real_exists_conull_pos_measurable_weight_uniformOn_tendstoInMeasure
    {f : ℕ → ℝ → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∃ A : Set ℝ, ∃ h : ℝ → ℝ,
      MeasurableSet A ∧
      (volume : Measure ℝ) Aᶜ = 0 ∧
      Measurable h ∧
      (∀ x, 0 < h x) ∧
      TendstoUniformlyOn (fun n x => f n x * h x) (fun _ => (0 : ℝ)) atTop A ∧
      TendstoInMeasure (volume : Measure ℝ) (fun n x => f n x * h x)
        atTop (fun _ => (0 : ℝ)) := by
  exact exists_conull_pos_measurable_weight_uniformOn_tendstoInMeasure_of_ae_tendsto
    (μ := (volume : Measure ℝ)) hf (ae_of_all _ hlim)

/-- The real-line dominated-convergence version used in the note. -/
theorem real_exists_pos_measurable_weight_tendstoInMeasure
    {f : ℕ → ℝ → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∃ h : ℝ → ℝ,
      Measurable h ∧
      (∀ x, 0 < h x) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x * h x) 1 (volume : Measure ℝ))
        atTop (nhds 0) ∧
      TendstoInMeasure (volume : Measure ℝ) (fun n x => f n x * h x)
        atTop (fun _ => 0) := by
  exact exists_pos_measurable_weight_tendstoInMeasure_of_ae_tendsto
    (μ := (volume : Measure ℝ)) hf (ae_of_all _ hlim)

end PointwiseWeighting
