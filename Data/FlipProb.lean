import Data.Prob

inductive FlipProb where
  | zero : FlipProb
  | one : FlipProb
  | rest : {x : Probability // 0 < x ∧ x < 1} -> FlipProb

namespace FlipProb

def prob : FlipProb -> Probability
  | zero => 0
  | one => 1
  | rest a => a.val

def invProb : FlipProb -> Probability
  | zero => 1
  | one => 0
  | rest a => Probability.add_inv a.val a.prop.right

def fromRat (q: ℚ) (h: 0 ≤ q ∧ q ≤ 1): FlipProb :=
  if h1 : q = 0 then zero
  else if h2 : q = 1 then one
  else
    have : (0: ℝ) < q := by rw [← ne_eq] at h1; simp [lt_iff_le_and_ne.mpr ⟨h.left, h1.symm⟩]
    have : q < (1: ℝ) := by rw [← ne_eq] at h2; norm_cast; simp [lt_iff_le_and_ne.mpr ⟨h.right, h2⟩]
    rest ⟨⟨DReal.fromRealPos (q: ℝ) (by aesop), by simp; rw [← DReal.one_ext]; simp [LT.lt.le this]⟩, by aesop⟩

end FlipProb
