import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.CompleteLattice
import Data.DReal

@[simp]
theorem min_three_sum (a b c l: ℝ) (c0: 0 ≤ c)
  : min l ((min l (a + b)) + c) = min l (a + b + c) := by
  by_cases (a + b) ≤ l
  case pos _ => aesop
  case neg h =>
    have h : l < a + b := by aesop
    have : min l ((min l (a + b)) + c) = min l (l + c) := by simp [LT.lt.le h]
    rw [this]
    have : l ≤ l + c := by aesop
    rw [min_eq_left this]
    simp [le_add_of_nonneg_of_le c0 (LT.lt.le h), add_comm]


def Probability : Type := {r : DReal // r ≤ 1}
  deriving LE, LT

namespace Probability

def fromRealPos (x: ℝ) (h: 0 < x ∧ x ≤ 1): Probability :=
  ⟨DReal.fromRealPos x h.left, by simp [h.right]⟩

def fromRealZero (x: ℝ) (h: 0 = x) : Probability :=
  ⟨DReal.fromRealZero x h, by simp; rw [←h]; simp⟩

theorem double_bound : Probability = {r : DReal // 0 ≤ r ∧ r ≤ 1} := by
  unfold Probability; simp

@[coe] def toDReal : Probability → DReal := Subtype.val
instance : Coe Probability DReal := ⟨toDReal⟩

@[simp]
theorem eq_ext : ∀(a b: Probability), a = b ↔ a.toDReal = b.toDReal := by
  intro a b; unfold toDReal;
  apply Iff.intro
  . intro h; rw [h]
  . exact Subtype.eq

--------------------
-- SIMPLE NUMBERS --
--------------------

instance : Zero (Probability) := ⟨⟨0, DReal.zero_le_one'⟩⟩

@[simp]
theorem zero_ext : (0 : Probability).toDReal = 0 := by rfl

instance : One (Probability) := ⟨⟨1, by simp⟩⟩

@[simp]
theorem one_ext : (1 : Probability).toDReal = 1 := by rfl

----------------
-- INEQUALITY --
----------------

@[simp]
theorem le_ext : ∀(a b: Probability), a ≤ b ↔ a.toDReal ≤ b.toDReal := by
  intro a b; conv => lhs; unfold_projs; unfold DReal.le;

theorem zero_le : ∀(a: Probability), 0 ≤ a := by
  intro a; rw [le_ext]; simp;

@[simp]
theorem zero_le_real : ∀(a: Probability), 0 ≤ a.toDReal := by
  intro a; rw [←zero_ext, ←le_ext]; exact zero_le a

theorem zero_le_one' : (0 : Probability) ≤ 1 := by
  rw [le_ext]; simp

theorem le_total' : ∀ (a b: Probability), a ≤ b ∨ b ≤ a := by
  intro a b; rw [le_ext, le_ext]; simp  [@LinearOrder.le_total ℝ _ _ _]

-----------------------
-- STRICT INEQUALITY --
-----------------------

@[simp]
theorem lt_ext : ∀(a b: Probability), a < b ↔ a.toDReal < b.toDReal := by
  intro a b; conv => lhs; unfold_projs;

theorem zero_lt_one'' : (0: Probability) < 1 := by
  rw [lt_ext]; simp

--------------
-- ADDITION --
--------------

@[simp]
theorem todo1 : ∀(a: Probability), a.toDReal ≤ 1 := Subtype.prop

@[simp]
theorem todo2 : ∀(a: Probability), a.toDReal.toReal ≤ 1 := by
  intro a; rw [←DReal.one_ext, ←DReal.le_ext]; exact todo1 a

def add (a b: Probability): Probability := ⟨DReal.minc' 1 (a.val + b.val), by simp⟩
instance : Add (Probability) := ⟨add⟩

@[simp]
theorem add_ext : ∀(a b: Probability), (a + b).toDReal = DReal.minc' 1 (a.toDReal + b.toDReal) := by
  intro a b; (conv => lhs; unfold HAdd.hAdd instHAdd Add.add instAddProbability add);

lemma zero_add' : ∀(a: Probability), 0 + a = a := by
  intro a; rw [eq_ext, add_ext]; simp

lemma add_zero' : ∀(a: Probability), a + 0 = a := by
  intro a; rw [eq_ext, add_ext]; simp

lemma add_comm' : ∀(a b: Probability), a + b = b + a := by
  intro a b; rw [eq_ext]; simp [add_comm]

lemma add_assoc' : ∀(a b c: Probability), (a + b) + c = a + (b + c) := by
  intro a b c; rw [eq_ext]; simp [add_assoc];
  conv => rhs; rhs; rw [add_comm]
  simp; simp [add_comm, add_assoc]

def add_inv (a: Probability) (h: a < 1): Probability :=
  match a with
  | ⟨DReal.zero, _⟩ => ⟨DReal.fromRealPos 1 (by simp), by unfold DReal.fromRealPos; simp⟩
  | ⟨DReal.pos a', h'⟩ => ⟨DReal.fromRealPos (1 - a') (by simp; exact h), by unfold DReal.fromRealPos; simp; exact LT.lt.le a'.prop;⟩

--------------------
-- MULTIPLICATION --
--------------------

def mul (a b: Probability): Probability :=
  ⟨(a.val * b.val), by
    rw [DReal.le_ext];
    have h1 : a.val.toReal ≤ 1 := by rw [←DReal.one_ext, ←DReal.le_ext]; exact a.prop
    have h2 : 0 ≤ b.val.toReal := by rw [←DReal.zero_ext, ←DReal.zero_ext', ←DReal.le_ext]; exact DReal.zero_le _
    have h3 : b.val.toReal ≤ 1 := by rw [←DReal.one_ext, ←DReal.le_ext]; exact b.prop
    simp; exact mul_le_one h1 h2 h3⟩
instance : Mul (Probability) := ⟨mul⟩

@[simp]
theorem mul_ext : ∀(a b: Probability), (a * b).toDReal = a.toDReal * b.toDReal := by
  intro a b; (conv => lhs; unfold HMul.hMul instHMul Mul.mul instMulProbability mul);

@[simp]
lemma mul_zero' : ∀(a: Probability), a * 0 = 0 := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma zero_mul' : ∀(a: Probability), 0 * a = 0 := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma mul_one' : ∀(a: Probability), a * 1 = a := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma one_mul' : ∀(a: Probability), 1 * a = a := by
  intro a; rw [eq_ext]; simp

lemma mul_comm' : ∀(a b: Probability), a * b = b * a := by
  intro a b; rw [eq_ext]; simp [mul_comm]

lemma mul_assoc' : ∀(a b c: Probability), (a * b) * c = a * (b * c) := by
  intro a b c; rw [eq_ext]; simp [mul_assoc]

/-
lemma left_distrib' : ∀(a b c: Probability), a * (b + c) = a * b + a * c := by
  intro a b c; rw [eq_ext]; simp [left_distrib]; simp [DReal.eq_ext]
  have a0 : (0: ℝ) ≤ a := by simp
  have a1 : a ≤ (1: ℝ) := by rw [← DReal.one_ext, ←DReal.le_ext]; simp
  have b0 : (0: ℝ) ≤ b := by simp
  have c0 : (0: ℝ) ≤ c := by simp
  have bc0 : (0: ℝ) ≤ b + c := add_nonneg b0 c0
  by_cases b + c ≤ (1: ℝ)
  case pos =>
    have : min (1: ℝ) (b + c) = b + c := by simpa
    rw [this]
    have : a * b + a * c ≤ (1: ℝ) := by
      calc a * b + a * (c: ℝ)
      _  = a * (b + c: ℝ) := by simp [left_distrib]
      _  ≤ (b + c: ℝ) := mul_le_of_le_one_left bc0 a1
      _  ≤ 1 := by assumption
    simp [this, left_distrib]
  case neg h =>
-/

lemma not_left_distrib': ∃(a b c: Probability), a * (b + c) ≠ a * b + a * c := by
  existsi ⟨DReal.pos ⟨0.5, by norm_num⟩, by rw [DReal.le_ext]; norm_num⟩
  existsi ⟨DReal.pos ⟨1, by norm_num⟩, by rw [DReal.le_ext]; norm_num⟩
  existsi ⟨DReal.pos ⟨1, by norm_num⟩, by rw [DReal.le_ext]; norm_num⟩
  simp; unfold toDReal; simp; ring_nf; simp

--------------
-- DIVISION --
--------------

def div (a: Probability) (b: DReal): Probability :=
  ⟨DReal.minc' 1 (a.val * b⁻¹), by simp⟩

---------------
-- MIN & MAX --
---------------

def minc' : Probability -> Probability -> Probability
  | x, y => ⟨DReal.minc' x.val y.val, by simp; left; rw [←DReal.one_ext, ←DReal.le_ext]; exact x.prop⟩
instance : Min Probability := ⟨ minc' ⟩

@[simp]
theorem min_ext : ∀(a b: Probability), (min a b).toDReal = Min.min a.toDReal b.toDReal := by
  intro a b; (conv => lhs; unfold min instMinProbability minc'); simp; rw [←DReal.min_ext]; norm_cast

def maxc' : Probability -> Probability -> Probability
  | x, y => ⟨DReal.maxc' x.val y.val, by simp; (conv => congr; repeat (rw [←DReal.one_ext, ←DReal.le_ext]; rfl)); constructor; exact x.prop; exact y.prop⟩
instance : Max Probability := ⟨ maxc' ⟩

@[simp]
theorem max_ext : ∀(a b: Probability), (max a b).toDReal = Max.max a.toDReal b.toDReal := by
  intro a b; (conv => lhs; unfold min instMaxProbability maxc'); simp; rw [←DReal.max_ext]; norm_cast

---------------------
-- SUPSET & INFSET --
---------------------

noncomputable instance supset {τ: Ty}: SupSet Probability :=
  ⟨ fun s => ⟨DReal.sSup {toDReal x | x ∈ s}, by sorry⟩⟩

noncomputable instance infset {τ: Ty}: InfSet Probability :=
  ⟨ fun s => ⟨DReal.sInf {toDReal x | x ∈ s}, by sorry⟩⟩

-----------------------------------
-- SEMIFIELD AND OTHER INSTANCES --
-----------------------------------

instance addcommmonoid : AddCommMonoid  (Probability) :=
  { add := add
  , add_assoc := add_assoc'
  , zero_add := zero_add'
  , add_zero := add_zero'
  , add_comm := add_comm'
  }
instance mulcommmonoid : CommMonoid  (Probability) :=
  { mul := mul
  , mul_assoc := mul_assoc'
  , one_mul := one_mul'
  , mul_one := mul_one'
  , mul_comm := mul_comm'
  }

instance partialOrder : PartialOrder Probability where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le a b := by
    apply Iff.intro; intro h; simp_all; exact LT.lt.le h; intro h; simp_all
  le_refl a := by simp
  le_trans a b c := by
    intro h1 h2; simp_all; exact LE.le.trans h1 h2
  le_antisymm a b := by
    intro h1 h2; simp_all; exact LE.le.antisymm h1 h2

instance : Preorder Probability := inferInstance

instance : OrderedAddCommMonoid Probability :=
  { addcommmonoid, partialOrder with
    add_le_add_left := by simp_all }

noncomputable instance : CompleteLattice Probability := by
  have y := Set.Icc.completeLattice DReal.zero_le_one'
  have : Probability = ↑(Set.Icc (0: DReal) 1) := by unfold Set.Icc; rw [double_bound, Set.coe_setOf]
  simpa [this]


-----------
-- OTHER --
-----------

theorem mul_le_mul {a b c d: Probability} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := by
  simp_all
  sorry

end Probability
