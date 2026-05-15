import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

noncomputable section

namespace IBMPonderThisBridge

open Real

def alpha : ℝ := 1 + 2 * Real.cos (Real.pi / 9)
def beta : ℝ := 1 + 2 * Real.cos (5 * Real.pi / 9)
def gamma : ℝ := 1 + 2 * Real.cos (7 * Real.pi / 9)

def cubic (x : ℝ) : ℝ := x ^ 3 - 3 * x ^ 2 + 1

lemma two_cos_cubic_eq_one (theta : ℝ) (h : Real.cos (3 * theta) = 1 / 2) :
    (2 * Real.cos theta) ^ 3 - 3 * (2 * Real.cos theta) = 1 := by
  have h3 := Real.cos_three_mul theta
  rw [h] at h3
  nlinarith

lemma cos_three_pi_div_nine : Real.cos (3 * (Real.pi / 9)) = 1 / 2 := by
  have harg : 3 * (Real.pi / 9) = Real.pi / 3 := by ring
  rw [harg, Real.cos_pi_div_three]

lemma cos_three_five_pi_div_nine : Real.cos (3 * (5 * Real.pi / 9)) = 1 / 2 := by
  have harg : 3 * (5 * Real.pi / 9) = (2 : ℝ) * Real.pi - Real.pi / 3 := by ring
  rw [harg, Real.cos_two_pi_sub, Real.cos_pi_div_three]

lemma cos_three_seven_pi_div_nine : Real.cos (3 * (7 * Real.pi / 9)) = 1 / 2 := by
  have harg : 3 * (7 * Real.pi / 9) = Real.pi / 3 + (2 : ℝ) * Real.pi := by ring
  rw [harg, Real.cos_add_two_pi, Real.cos_pi_div_three]

lemma cubic_one_add_of_two_cos {theta : ℝ}
    (h : (2 * Real.cos theta) ^ 3 - 3 * (2 * Real.cos theta) = 1) :
    cubic (1 + 2 * Real.cos theta) = 0 := by
  unfold cubic
  nlinarith

theorem cubic_alpha : cubic alpha = 0 := by
  unfold alpha
  exact cubic_one_add_of_two_cos
    (two_cos_cubic_eq_one (Real.pi / 9) cos_three_pi_div_nine)

theorem cubic_beta : cubic beta = 0 := by
  unfold beta
  exact cubic_one_add_of_two_cos
    (two_cos_cubic_eq_one (5 * Real.pi / 9) cos_three_five_pi_div_nine)

theorem cubic_gamma : cubic gamma = 0 := by
  unfold gamma
  exact cubic_one_add_of_two_cos
    (two_cos_cubic_eq_one (7 * Real.pi / 9) cos_three_seven_pi_div_nine)

lemma cos_two_pi_div_three : Real.cos ((2 : ℝ) * Real.pi / 3) = -1 / 2 := by
  have harg : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [harg, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma alpha_gt_two : 2 < alpha := by
  unfold alpha
  have hcos : (1 / 2 : ℝ) < Real.cos (Real.pi / 9) := by
    have h :=
      Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := Real.pi / 9) (y := Real.pi / 3) (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    rw [Real.cos_pi_div_three] at h
    exact h
  nlinarith

lemma alpha_lt_three : alpha < 3 := by
  unfold alpha
  have hcos : Real.cos (Real.pi / 9) < 1 := by
    have h :=
      Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := 0) (y := Real.pi / 9) (by norm_num)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simpa using h
  nlinarith

lemma beta_pos : 0 < beta := by
  unfold beta
  have hcos : (-1 / 2 : ℝ) < Real.cos (5 * Real.pi / 9) := by
    have h :=
      Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := 5 * Real.pi / 9) (y := (2 : ℝ) * Real.pi / 3)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])
    rw [cos_two_pi_div_three] at h
    exact h
  nlinarith

lemma beta_lt_one : beta < 1 := by
  unfold beta
  have hcos : Real.cos (5 * Real.pi / 9) < 0 := by
    have h :=
      Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := Real.pi / 2) (y := 5 * Real.pi / 9)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])
    rw [Real.cos_pi_div_two] at h
    exact h
  nlinarith

lemma gamma_gt_neg_one : -1 < gamma := by
  unfold gamma
  have hcos : (-1 : ℝ) < Real.cos (7 * Real.pi / 9) := by
    have h :=
      Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := 7 * Real.pi / 9) (y := Real.pi)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])
    rw [Real.cos_pi] at h
    exact h
  nlinarith

lemma gamma_neg : gamma < 0 := by
  unfold gamma
  have hcos : Real.cos (7 * Real.pi / 9) < -1 / 2 := by
    have h :=
      Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := (2 : ℝ) * Real.pi / 3) (y := 7 * Real.pi / 9)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])
    rw [cos_two_pi_div_three] at h
    exact h
  nlinarith

lemma cubic_neg_of_two_thirds_le_of_lt_one {x : ℝ}
    (hlo : (2 / 3 : ℝ) ≤ x) (hhi : x < 1) : cubic x < 0 := by
  unfold cubic
  nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (x - 1)]

lemma cubic_neg_of_gt_neg_one_of_le_neg_two_thirds {x : ℝ}
    (hlo : -1 < x) (hhi : x ≤ (-2 / 3 : ℝ)) : cubic x < 0 := by
  unfold cubic
  nlinarith [sq_nonneg (x + 2 / 3), sq_nonneg (x + 1)]

theorem abs_beta_lt_two_thirds : |beta| < 2 / 3 := by
  have hlt : beta < 2 / 3 := by
    by_contra h
    have hge : (2 / 3 : ℝ) ≤ beta := le_of_not_gt h
    have hneg := cubic_neg_of_two_thirds_le_of_lt_one hge beta_lt_one
    rw [cubic_beta] at hneg
    norm_num at hneg
  have hpos := beta_pos
  rw [abs_of_pos hpos]
  exact hlt

theorem abs_gamma_lt_two_thirds : |gamma| < 2 / 3 := by
  have hgt : (-2 / 3 : ℝ) < gamma := by
    by_contra h
    have hle : gamma ≤ (-2 / 3 : ℝ) := le_of_not_gt h
    have hneg := cubic_neg_of_gt_neg_one_of_le_neg_two_thirds gamma_gt_neg_one hle
    rw [cubic_gamma] at hneg
    norm_num at hneg
  have hneg := gamma_neg
  rw [abs_of_neg hneg]
  nlinarith

def realTrace (n : ℕ) : ℝ := alpha ^ n + beta ^ n + gamma ^ n

def traceInt : ℕ → ℤ
  | 0 => 3
  | 1 => 3
  | 2 => 9
  | n + 3 => 3 * traceInt (n + 2) - traceInt n

lemma pow_recurrence_of_cubic {x : ℝ} (hx : cubic x = 0) (n : ℕ) :
    x ^ (n + 3) = 3 * x ^ (n + 2) - x ^ n := by
  have hx3 : x ^ 3 = 3 * x ^ 2 - 1 := by
    unfold cubic at hx
    nlinarith
  calc
    x ^ (n + 3) = x ^ n * x ^ 3 := by
      rw [pow_add]
    _ = x ^ n * (3 * x ^ 2 - 1) := by rw [hx3]
    _ = 3 * x ^ (n + 2) - x ^ n := by
      rw [pow_add]
      ring

lemma realTrace_recurrence (n : ℕ) :
    realTrace (n + 3) = 3 * realTrace (n + 2) - realTrace n := by
  unfold realTrace
  rw [pow_recurrence_of_cubic cubic_alpha n,
    pow_recurrence_of_cubic cubic_beta n,
    pow_recurrence_of_cubic cubic_gamma n]
  ring

lemma cos_sum_zero :
    Real.cos (Real.pi / 9) + Real.cos (5 * Real.pi / 9) +
      Real.cos (7 * Real.pi / 9) = 0 := by
  have h :=
    Real.cos_add_cos (5 * Real.pi / 9) (7 * Real.pi / 9)
  have hsum : (5 * Real.pi / 9 + 7 * Real.pi / 9) / 2 = (2 : ℝ) * Real.pi / 3 := by
    ring
  have hdiff : (5 * Real.pi / 9 - 7 * Real.pi / 9) / 2 = -(Real.pi / 9) := by
    ring
  have hneg : Real.cos (-(Real.pi / 9)) = Real.cos (Real.pi / 9) := by
    rw [Real.cos_neg]
  rw [hsum, hdiff, hneg, cos_two_pi_div_three] at h
  nlinarith

lemma cos_four_pi_div_three : Real.cos ((4 : ℝ) * Real.pi / 3) = -1 / 2 := by
  have harg : (4 : ℝ) * Real.pi / 3 = (2 : ℝ) * Real.pi - (2 : ℝ) * Real.pi / 3 := by
    ring
  rw [harg, Real.cos_two_pi_sub, cos_two_pi_div_three]

lemma cos_double_sum_zero :
    Real.cos (2 * (Real.pi / 9)) + Real.cos (2 * (5 * Real.pi / 9)) +
      Real.cos (2 * (7 * Real.pi / 9)) = 0 := by
  have h :=
    Real.cos_add_cos (2 * (5 * Real.pi / 9)) (2 * (7 * Real.pi / 9))
  have hsum :
      (2 * (5 * Real.pi / 9) + 2 * (7 * Real.pi / 9)) / 2 =
        (4 : ℝ) * Real.pi / 3 := by
    ring
  have hdiff :
      (2 * (5 * Real.pi / 9) - 2 * (7 * Real.pi / 9)) / 2 =
        -(2 * (Real.pi / 9)) := by
    ring
  have hneg : Real.cos (-(2 * (Real.pi / 9))) = Real.cos (2 * (Real.pi / 9)) := by
    rw [Real.cos_neg]
  rw [hsum, hdiff, hneg, cos_four_pi_div_three] at h
  nlinarith

lemma cos_sq_sum :
    Real.cos (Real.pi / 9) ^ 2 + Real.cos (5 * Real.pi / 9) ^ 2 +
      Real.cos (7 * Real.pi / 9) ^ 2 = 3 / 2 := by
  rw [Real.cos_sq, Real.cos_sq, Real.cos_sq]
  nlinarith [cos_double_sum_zero]

lemma realTrace_zero : realTrace 0 = 3 := by
  unfold realTrace
  norm_num

lemma realTrace_one : realTrace 1 = 3 := by
  unfold realTrace alpha beta gamma
  nlinarith [cos_sum_zero]

lemma realTrace_two : realTrace 2 = 9 := by
  unfold realTrace alpha beta gamma
  nlinarith [cos_sum_zero, cos_sq_sum]

theorem traceInt_cast_eq_realTrace (n : ℕ) : (traceInt n : ℝ) = realTrace n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          simp [traceInt, realTrace_zero]
      | 1 =>
          simp [traceInt, realTrace_one]
      | 2 =>
          simp [traceInt, realTrace_two]
      | k + 3 =>
          rw [traceInt, realTrace_recurrence]
          have h2 : (traceInt (k + 2) : ℝ) = realTrace (k + 2) :=
            ih (k + 2) (by omega)
          have h0 : (traceInt k : ℝ) = realTrace k :=
            ih k (by omega)
          norm_num [h2, h0]

lemma beta_gamma_error_lt_half {n : ℕ} (hn : 4 ≤ n) :
    |beta ^ n + gamma ^ n| < 1 / 2 := by
  have htri : |beta ^ n + gamma ^ n| ≤ |beta| ^ n + |gamma| ^ n := by
    calc
      |beta ^ n + gamma ^ n| ≤ |beta ^ n| + |gamma ^ n| := abs_add_le _ _
      _ = |beta| ^ n + |gamma| ^ n := by rw [abs_pow, abs_pow]
  have hn0 : n ≠ 0 := by omega
  have hb : |beta| ^ n < (2 / 3 : ℝ) ^ n :=
    pow_lt_pow_left₀ abs_beta_lt_two_thirds (abs_nonneg beta) hn0
  have hg : |gamma| ^ n < (2 / 3 : ℝ) ^ n :=
    pow_lt_pow_left₀ abs_gamma_lt_two_thirds (abs_nonneg gamma) hn0
  have hsum : |beta| ^ n + |gamma| ^ n < (2 / 3 : ℝ) ^ n + (2 / 3 : ℝ) ^ n :=
    add_lt_add hb hg
  have hmono : (2 / 3 : ℝ) ^ n ≤ (2 / 3 : ℝ) ^ 4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  nlinarith

theorem round_alpha_pow_eq_traceInt {n : ℕ} (hn : 4 ≤ n) :
    round (alpha ^ n) = traceInt n := by
  rw [round_eq_iff]
  have htrace := traceInt_cast_eq_realTrace n
  have herr : |alpha ^ n - (traceInt n : ℝ)| < 1 / 2 := by
    calc
      |alpha ^ n - (traceInt n : ℝ)| = |beta ^ n + gamma ^ n| := by
        rw [htrace]
        unfold realTrace
        have h :
            alpha ^ n - (alpha ^ n + beta ^ n + gamma ^ n) =
              -(beta ^ n + gamma ^ n) := by
          ring
        rw [h, abs_neg]
      _ < 1 / 2 := beta_gamma_error_lt_half hn
  rcases abs_lt.mp herr with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem round_alpha_sharpN_eq_traceInt :
    round (alpha ^ 21699999999) = traceInt 21699999999 := by
  exact round_alpha_pow_eq_traceInt (by norm_num)

end IBMPonderThisBridge
