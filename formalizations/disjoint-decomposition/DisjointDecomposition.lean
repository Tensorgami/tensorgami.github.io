import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Filter Set Topology

private theorem isPreconnected_ball_IccSubtype
    (p : Icc (0 : ℝ) 1) (r : ℝ) :
    IsPreconnected (Metric.ball p r) := by
  rw [isPreconnected_iff_ordConnected]
  have hreal : OrdConnected (Metric.ball (p : ℝ) r) := by
    rw [Real.ball_eq_Ioo]
    infer_instance
  simpa [Subtype.dist_eq] using
    hreal.preimage_mono (Subtype.mono_coe fun x : ℝ => x ∈ Icc (0 : ℝ) 1)

private theorem no_closed_partition_Icc_with_singleton_one
    (F : ℕ → Set (Icc (0 : ℝ) 1))
    (hclosed : ∀ n, IsClosed (F n))
    (hdisj : (univ : Set ℕ).PairwiseDisjoint F)
    (hcover : (⋃ n, F n) = univ)
    (hF0 : F 0 = ({⟨1, by norm_num⟩} : Set (Icc (0 : ℝ) 1))) :
    False := by
  let X := Icc (0 : ℝ) 1
  let oneX : X := ⟨1, by
    change (1 : ℝ) ∈ Icc (0 : ℝ) 1
    norm_num⟩
  let zeroX : X := ⟨0, by
    change (0 : ℝ) ∈ Icc (0 : ℝ) 1
    norm_num⟩
  haveI : ConnectedSpace X :=
    Subtype.connectedSpace (isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num))
  haveI : Nontrivial X := ⟨⟨zeroX, oneX, by
    intro h
    have := congrArg Subtype.val h
    norm_num at this⟩⟩
  have hone_not_int0 : oneX ∉ interior (F 0) := by
    rw [hF0]
    simp [oneX, interior_singleton]
  have hone_mem_F0 : oneX ∈ F 0 := by
    simp [hF0, oneX]
  let P : Set X := (⋃ n, interior (F n))ᶜ
  have hP_closed : IsClosed P := by
    dsimp [P]
    exact (isOpen_iUnion fun n => isOpen_interior).isClosed_compl
  have hone_mem_P : oneX ∈ P := by
    intro hone
    rcases mem_iUnion.mp hone with ⟨n, hn⟩
    by_cases hn0 : n = 0
    · subst n
      exact hone_not_int0 hn
    · have hone_mem_Fn : oneX ∈ F n := interior_subset hn
      have h01 : Disjoint (F 0) (F n) :=
        hdisj (mem_univ 0) (mem_univ n) (Ne.symm hn0)
      exact (disjoint_left.mp h01) hone_mem_F0 hone_mem_Fn
  have hP_nonempty : P.Nonempty := ⟨oneX, hone_mem_P⟩
  haveI : Nonempty P := hP_nonempty.to_subtype
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace P :=
    hP_closed.isCompletelyPseudoMetrizableSpace
  haveI : BaireSpace P := inferInstance
  let B : ℕ → Set P := fun n => {x | (x : X) ∈ F n}
  have hB_closed : ∀ n, IsClosed (B n) := by
    intro n
    exact (hclosed n).preimage continuous_subtype_val
  have hB_cover : (⋃ n, B n) = univ := by
    ext x
    constructor
    · intro hx
      trivial
    · intro _hx
      have hxF : (x : X) ∈ ⋃ n, F n := by
        rw [hcover]
        trivial
      rcases mem_iUnion.mp hxF with ⟨n, hn⟩
      exact mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨k, hk_nonempty⟩ := nonempty_interior_of_iUnion_of_closed hB_closed hB_cover
  rcases hk_nonempty with ⟨p, hp_int_Bk⟩
  have hp_Bk : p ∈ B k := interior_subset hp_int_Bk
  have hp_Fk : (p : X) ∈ F k := hp_Bk
  have hp_nhds : B k ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hp_int_Bk
  rcases Metric.mem_nhds_iff.mp hp_nhds with ⟨ε, hε_pos, hε_sub⟩
  let J : Set X := Metric.ball (p : X) (ε / 2)
  have hε_half_pos : 0 < ε / 2 := by positivity
  have hp_mem_J : (p : X) ∈ J := by
    exact Metric.mem_ball_self hε_half_pos
  have hJ_open : IsOpen J := Metric.isOpen_ball
  have hJ_preconnected : IsPreconnected J :=
    isPreconnected_ball_IccSubtype (p : X) (ε / 2)
  have hJP_subset_Fk : ∀ ⦃y : X⦄, y ∈ J → y ∈ P → y ∈ F k := by
    intro y hyJ hyP
    have hy_ball_P : (⟨y, hyP⟩ : P) ∈ Metric.ball p ε := by
      change dist (⟨y, hyP⟩ : P) p < ε
      rw [Subtype.dist_eq]
      have hy_half : dist y (p : X) < ε / 2 := by
        simpa [J] using hyJ
      linarith
    exact hε_sub hy_ball_P
  have hJ_subset_union :
      ∀ m, m ≠ k → J ⊆ (F m)ᶜ ∪ interior (F m) := by
    intro m hmk y hyJ
    by_cases hyFm : y ∈ F m
    · right
      by_cases hyP : y ∈ P
      · have hyFk : y ∈ F k := hJP_subset_Fk hyJ hyP
        have hmk_disj : Disjoint (F m) (F k) :=
          hdisj (mem_univ m) (mem_univ k) hmk
        exact False.elim ((disjoint_left.mp hmk_disj) hyFm hyFk)
      · have hyU : y ∈ ⋃ n, interior (F n) := by
          simpa [P] using hyP
        rcases mem_iUnion.mp hyU with ⟨n, hyn⟩
        have hynF : y ∈ F n := interior_subset hyn
        have hnm : n = m := by
          by_contra hne
          have hnm_disj : Disjoint (F n) (F m) :=
            hdisj (mem_univ n) (mem_univ m) hne
          exact (disjoint_left.mp hnm_disj) hynF hyFm
        subst n
        exact hyn
    · left
      exact hyFm
  have hJ_subset_compl :
      ∀ m, m ≠ k → J ⊆ (F m)ᶜ := by
    intro m hmk
    have hcases : J ⊆ (F m)ᶜ ∨ J ⊆ interior (F m) :=
      hJ_preconnected.subset_or_subset
        (hclosed m).isOpen_compl
        isOpen_interior
        (disjoint_compl_left.mono_right interior_subset)
        (hJ_subset_union m hmk)
    exact hcases.resolve_right (by
      intro hJ_sub_int
      have hpFm : (p : X) ∈ F m := interior_subset (hJ_sub_int hp_mem_J)
      have hmk_disj : Disjoint (F m) (F k) :=
        hdisj (mem_univ m) (mem_univ k) hmk
      exact (disjoint_left.mp hmk_disj) hpFm hp_Fk)
  have hJ_subset_Fk : J ⊆ F k := by
    intro y hyJ
    have hy_cover : y ∈ ⋃ n, F n := by
      rw [hcover]
      trivial
    rcases mem_iUnion.mp hy_cover with ⟨n, hyn⟩
    by_cases hnk : n = k
    · simpa [hnk] using hyn
    · exact False.elim ((hJ_subset_compl n hnk hyJ) hyn)
  have hp_int_Fk : (p : X) ∈ interior (F k) := by
    exact mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (hJ_open.mem_nhds hp_mem_J) hJ_subset_Fk)
  exact p.2 (mem_iUnion.mpr ⟨k, hp_int_Fk⟩)

theorem no_pairwiseDisjoint_closed_iUnion_eq_Ico
    (E : ℕ → Set ℝ)
    (hclosed : ∀ n, IsClosed (E n))
    (hdisj : (univ : Set ℕ).PairwiseDisjoint E)
    (hcover : (⋃ n, E n) = Ico (0 : ℝ) 1) :
    False := by
  let X := Icc (0 : ℝ) 1
  let oneX : X := ⟨1, by
    change (1 : ℝ) ∈ Icc (0 : ℝ) 1
    norm_num⟩
  have hE_subset_Ico : ∀ n, E n ⊆ Ico (0 : ℝ) 1 := by
    intro n x hx
    have hxU : x ∈ ⋃ n, E n := mem_iUnion.mpr ⟨n, hx⟩
    simpa [hcover] using hxU
  let F : ℕ → Set X := fun n =>
    match n with
    | 0 => {oneX}
    | m + 1 => {x : X | (x : ℝ) ∈ E m}
  have hFclosed : ∀ n, IsClosed (F n) := by
    intro n
    cases n with
    | zero =>
        simp [F]
    | succ n =>
        exact (hclosed n).preimage continuous_subtype_val
  have hFcover : (⋃ n, F n) = univ := by
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      by_cases hx1 : (x : ℝ) = 1
      · exact mem_iUnion.mpr ⟨0, by
          simp [F, oneX, Subtype.ext_iff, hx1]⟩
      · have hxlt1 : (x : ℝ) < 1 := lt_of_le_of_ne x.2.2 hx1
        have hxIco : (x : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨x.2.1, hxlt1⟩
        have hxU : (x : ℝ) ∈ ⋃ n, E n := by
          rw [hcover]
          exact hxIco
        rcases mem_iUnion.mp hxU with ⟨n, hn⟩
        exact mem_iUnion.mpr ⟨n + 1, by
          simpa [F] using hn⟩
  have hFdisj : (univ : Set ℕ).PairwiseDisjoint F := by
    intro i _hi j _hj hij
    cases i with
    | zero =>
        cases j with
        | zero =>
            exact False.elim (hij rfl)
        | succ j =>
            refine disjoint_left.mpr ?_
            intro x hx0 hxj
            have hx_eq : x = oneX := by
              simpa [F] using hx0
            have hxE : (x : ℝ) ∈ E j := by
              simpa [F] using hxj
            have hxlt : (x : ℝ) < 1 := (hE_subset_Ico j hxE).2
            have hxeq1 : (x : ℝ) = 1 := by
              simp [hx_eq, oneX]
            linarith
    | succ i =>
        cases j with
        | zero =>
            refine disjoint_left.mpr ?_
            intro x hxi hx0
            have hx_eq : x = oneX := by
              simpa [F] using hx0
            have hxE : (x : ℝ) ∈ E i := by
              simpa [F] using hxi
            have hxlt : (x : ℝ) < 1 := (hE_subset_Ico i hxE).2
            have hxeq1 : (x : ℝ) = 1 := by
              simp [hx_eq, oneX]
            linarith
        | succ j =>
            have hij' : i ≠ j := by
              intro h
              exact hij (by simp [h])
            have hEij : Disjoint (E i) (E j) :=
              hdisj (mem_univ i) (mem_univ j) hij'
            refine disjoint_left.mpr ?_
            intro x hxi hxj
            have hxiE : (x : ℝ) ∈ E i := by
              simpa [F] using hxi
            have hxjE : (x : ℝ) ∈ E j := by
              simpa [F] using hxj
            exact (disjoint_left.mp hEij) hxiE hxjE
  have hF0 : F 0 = ({⟨1, by
      change (1 : ℝ) ∈ Icc (0 : ℝ) 1
      norm_num⟩} : Set X) := by
    simp [F, oneX]
  exact no_closed_partition_Icc_with_singleton_one F hFclosed hFdisj hFcover hF0
