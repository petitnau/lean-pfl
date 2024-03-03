import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

def maxc (a b: ℝ): ℝ :=
  (a + b)*0.5 + (|a - b|)*0.5

@[simp]
theorem max_correct (a b: ℝ): maxc a b = max a b := by
  unfold maxc
  have : (0.5:ℝ) = 1/2 := by norm_num
  have H : ∀x:ℝ, x*0.5 = x/2 := by aesop
  suffices (a + b)/2 + |a - b|/2 = max a b
    by simp [H (a+b), H |a-b|]; assumption
  by_cases (a ≤ b)
  case pos h =>
    have : |a - b| = b - a := by unfold abs; simp; linarith
    simp [this, h]
    linarith
  case neg h =>
    have : max a b = a := by aesop; apply le_of_lt; assumption
    have : |a - b| = a - b := by aesop
    simp [this, h]
    linarith


def minc (a b: ℝ): ℝ :=
  (a + b)*0.5 - (|a - b|)*0.5

@[simp]
theorem min_correct (a b: ℝ): minc a b = min a b := by
  unfold minc
  have : (0.5:ℝ) = 1/2 := by norm_num
  have H : ∀x:ℝ, x*0.5 = x/2 := by aesop
  suffices  (a + b)/2 - |a - b|/2 = min a b
    by simp [H (a+b), H |a-b|]; assumption
  by_cases (a ≤ b)
  case pos h =>
    have : |a - b| = b - a := by unfold abs; simp; linarith
    simp [this, h]
    linarith
  case neg h =>
    have : min a b = b := by aesop; apply le_of_lt; assumption
    have : |a - b| = a - b := by aesop
    simp [this, h]
    linarith
