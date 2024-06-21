import Data.Probability

inductive FlipProb' where
  | zero : FlipProb'
  | one : FlipProb'
  | rest : {x : Probability // 0 < x ∧ x < 1} -> FlipProb'

def FlipProb: Type := {r : ℚ // 0 ≤ r ∧ r ≤ 1}

namespace FlipProb'

def prob' : FlipProb' -> Probability
  | zero => 0
  | one => 1
  | rest a => a.val

def invProb : FlipProb' -> Probability
  | zero => 1
  | one => 0
  | rest a => Probability.add_inv a.val a.prop.right

def fromRat (q: ℚ) (h: 0 ≤ q ∧ q ≤ 1): FlipProb' :=
  if h1 : q = 0 then zero
  else if h2 : q = 1 then one
  else
    have : (0: ℝ) < q := by rw [← ne_eq] at h1; simp [lt_iff_le_and_ne.mpr ⟨h.left, h1.symm⟩]
    have : q < (1: ℝ) := by rw [← ne_eq] at h2; norm_cast; simp [lt_iff_le_and_ne.mpr ⟨h.right, h2⟩]
    rest ⟨⟨DReal.fromRealPos (q: ℝ) (by aesop), by rw [DReal.le_ext, DReal.one_ext]; simp [LT.lt.le this]⟩, by aesop⟩

@[simp] theorem PSum.cast_inl
  (x: α) (h1: (α ⊕' β) = (α' ⊕' β)) (h2: α = α')
  : cast h1 (@PSum.inl α β x)
    = @PSum.inl α' β (cast h2 x) := by aesop

@[simp] theorem PSum.cast_inr
  (h1: (α ⊕' β) = (α ⊕' β')) (h2: β = β')
  : cast h1 (@PSum.inr α β x)
    = @PSum.inr α β' (cast h2 x) := by aesop

@[simp]
theorem prob_fromRat_zero : prob' (fromRat 0 h) = 0 := by aesop

@[simp]
theorem prob_fromRat_one : prob' (fromRat 1 h) = 1 := by aesop

@[simp]
theorem prob_fromRat_rest (h1: 0 < q) (h2: q < 1) :
  prob' (fromRat q h) = ⟨⟨q, by aesop⟩, by
    have : (q:ℝ) < 1 := by norm_cast
    rw [DReal.le_ext]; simp_all;
    exact LT.lt.le this⟩ := by
      have : ¬ q = 0 := by aesop
      have : ¬ q = 1 := by aesop
      unfold prob' fromRat DReal.fromRealPos;
      aesop;

end FlipProb'

namespace FlipProb

def prob (x : FlipProb) : Probability :=
  if h: x.val = 0 then 0
  else Probability.fromRealPos x.val (by
    constructor; rw [← ne_eq] at h;
    norm_cast; exact h.symm.lt_of_le x.prop.left;
    norm_cast; exact x.prop.right)

def invProb (x : FlipProb) : Probability :=
  prob ⟨1 - x.val, by simp [x.prop]⟩

def fromRat (q: ℚ) (h: 0 ≤ q ∧ q ≤ 1): FlipProb :=
  ⟨q, h⟩

end FlipProb
