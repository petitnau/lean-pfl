import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.CauSeq.Completion
import Mathlib.Order.CompleteLatticeIntervals

-------------------------
-- EXTRA QUOTIENT DEFS --
-------------------------

def Quotient.toTrunc {α : Sort*} [s : Setoid α] (q : Quotient s) : Trunc { a // ⟦a⟧ = q } :=
  q.recOn (fun a ↦ Trunc.mk ⟨a, rfl⟩) (fun _ _ _ ↦ Trunc.eq ..)

def Quotient.elim {α β : Sort*} [s : Setoid α] (q : Quotient s)
    (f : (a : α) → ⟦a⟧ = q → β) (h : ∀ a b ha hb, f a ha = f b hb)
    : β :=
  q.toTrunc.lift (fun x ↦ f x.val x.prop) (fun _ _ ↦ h ..)

def generalize {α β : Sort*} [s : Setoid α] (q : Quotient s)
    (f : α → β) : (a : α) → ⟦a⟧ = q → β :=
    fun a _ => f a

def generalize_h {α β : Sort*} [s : Setoid α] (q : Quotient s)
    (f : α → β) (c : (a b : α) → a ≈ b → f a = f b)
    : ∀ a b ha hb, (generalize q f) a ha = (generalize q f) b hb := by
    intro a b h1 h2; unfold generalize
    simp [c, ←h2, Quotient.eq] at *
    exact c a b h1

lemma eq_elim_lifton {α β : Sort*} [s: Setoid α] (q : Quotient s)
    (f : α → β) (c : (a b : α) → a ≈ b → f a = f b)
    : Quotient.liftOn q f c = Quotient.elim q (generalize q f) (generalize_h q f c) := by
    unfold Quotient.liftOn; unfold Quot.liftOn; unfold Quotient.elim;
    have ⟨a, ha⟩ : ∃a, ⟦a⟧ = q := Quotient.exists_rep q
    have ha : q = ⟦a⟧ := ha.symm
    have elem : { a_1 // ⟦a_1⟧ = q} := ⟨a, by aesop⟩
    have elem' : { a_1 // (⟦a_1⟧: Quotient s) = ⟦a⟧} := by rwa [ha] at elem
    let elemt' : Trunc { a_1 // ⟦a_1⟧ = ⟦a⟧} := Trunc.mk elem'
    have elemt'_def : elemt' = Trunc.mk elem' := by rfl
    have : Quotient.toTrunc ⟦a⟧ = elemt' := by apply Trunc.eq
    rw [ha]
    rw [this]
    simp [Quot.lift_mk f c a]
    rw [Trunc.lift_mk (fun (x: { a_1 // ⟦a_1⟧ = ⟦a⟧ }) => (generalize ⟦a⟧ f) x.val x.prop) _ elem'];
    unfold generalize;
    let ⟨v, h⟩ := elem'
    simp
    apply c
    have : ⟦a⟧ = ⟦v⟧ := Eq.symm h
    rwa [Quotient.eq] at this

def generalize_aux {α: Type} {s: Setoid α} {x: Quotient s} {f: α -> β} (h2 : ∀ (a b : α), a ≈ b → f a = f b):
  ∀ (a b : α) (ha : ⟦a⟧ = x) (hb : ⟦b⟧ = x), (fun x _ => f x) a ha = (fun x _ => f x) b hb := by
  intro a b ha hb
  simp
  rw [← hb] at ha
  clear hb
  simp_all only [Quotient.eq]
  apply h2; apply ha

--------------------------------
-- CONDITIONAL REAL INVERSION --
--------------------------------

section CauSeq.Inversion

open Classical
variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

def conditional_inv (x: CauSeq.Completion.Cauchy abv) (h: ¬ Quotient.liftOn x CauSeq.LimZero limZero_congr) : CauSeq.Completion.Cauchy abv :=
  (Quotient.elim x (fun f _ => CauSeq.Completion.mk <| CauSeq.inv f (by aesop))) fun f g fxh gxh => by
    have hf : ¬ CauSeq.LimZero f := by
      rw [← fxh, CauSeq.Completion.mk_eq_mk] at h
      exact h
    have hg : ¬ CauSeq.LimZero g := by
      rw [← gxh, CauSeq.Completion.mk_eq_mk] at h
      exact h
    have If  : CauSeq.Completion.mk (CauSeq.inv f hf) * CauSeq.Completion.mk f = 1 := CauSeq.Completion.mk_eq.2 (CauSeq.inv_mul_cancel hf)
    have Ig  : CauSeq.Completion.mk (CauSeq.inv g hg) * CauSeq.Completion.mk g = 1 := CauSeq.Completion.mk_eq.2 (CauSeq.inv_mul_cancel hg)
    have Ig' : CauSeq.Completion.mk g * CauSeq.Completion.mk (CauSeq.inv g hg) = 1 := CauSeq.Completion.mk_eq.2 (CauSeq.mul_inv_cancel hg)
    rw [← gxh] at fxh
    rw [CauSeq.Completion.mk_eq_mk] at fxh
    rw [CauSeq.Completion.mk_eq_mk] at fxh
    rw [CauSeq.Completion.mk_eq] at fxh
    rw [CauSeq.Completion.mk_eq.2 fxh, ← Ig] at If
    rw [← MulOneClass.mul_one (CauSeq.Completion.mk (CauSeq.inv f hf)), ← Ig', ← Semigroup.mul_assoc, If, Semigroup.mul_assoc, Ig', MulOneClass.mul_one]

@[simp]
theorem conditional_inv_correct {x: CauSeq.Completion.Cauchy abv} {h: ¬ Quotient.liftOn x CauSeq.LimZero limZero_congr}: conditional_inv x h = x⁻¹ := by
  unfold_projs; unfold conditional_inv; rw [eq_elim_lifton]; congr;
  unfold generalize; simp; funext f h''; rw [← CauSeq.Completion.mk_eq_mk] at h''; congr;
  by_cases h' : CauSeq.LimZero f;
  . exfalso; apply h; rwa [← h'', Quotient.liftOn_mk CauSeq.LimZero limZero_congr f]
  . simp [h']

theorem pos_not_limzero (x: ℝ) (h: 0 < x): ¬ Quotient.liftOn x.cauchy CauSeq.LimZero limZero_congr :=
  by
    have ⟨a, ha⟩: ∃a, ⟦a⟧ = x.cauchy := Quotient.exists_rep x.cauchy
    have : x ≠ 0 := by aesop
    have : ¬ CauSeq.LimZero a := by
      apply CauSeq.not_limZero_of_not_congr_zero;
      rw [CauSeq.Completion.mk_eq_mk] at ha
      have : x = Real.mk a := by unfold Real.mk; aesop
      rw [← Real.mk_zero] at h
      rw [this] at h
      rw [Real.mk_lt] at h
      by_contra h1
      have := CauSeq.lt_of_lt_of_eq h h1
      apply CauSeq.lt_irrefl this
    rw [← ha]
    rw [Quotient.liftOn_mk CauSeq.LimZero limZero_congr a]
    assumption

end CauSeq.Inversion

-----------------------------
-- COMPUTABLE REAL MIN/MAX --
-----------------------------

def Real.maxc (a b: ℝ): ℝ :=
  (a + b)*0.5 + (|a - b|)*0.5

@[simp]
theorem Real.maxc_correct (a b: ℝ): maxc a b = max a b := by
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
    have : max a b = a := by simp [max_eq_right]; apply le_of_lt; aesop
    have : |a - b| = a - b := by aesop
    simp [this, h]
    linarith

def Real.minc (a b: ℝ): ℝ :=
  (a + b)*0.5 - (|a - b|)*0.5

@[simp]
theorem Real.min_correct (a b: ℝ): minc a b = min a b := by
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
    have : min a b = b := by simp [min_eq_right]; apply le_of_lt; aesop
    have : |a - b| = a - b := by aesop
    simp [this, h]
    linarith

---------------------
-- DECIDABLE REALS --
---------------------

structure DReal :=
  val : ℝ
  pos  : (0 = val) ⊕' (0 < val)

namespace DReal

----------------
-- CONVERSION --
----------------

@[coe] abbrev toReal : DReal → ℝ := DReal.val
instance : Coe DReal ℝ := ⟨toReal⟩

@[simp]
theorem val_ext : (⟨v, h⟩: DReal).toReal = v := by aesop

def fromRealPos (x: ℝ) (h: 0 < x) : DReal := ⟨x, .inr h⟩

noncomputable def fromReal (x: ℝ) (h: 0 ≤ x) : DReal :=
  if h': 0 = x then ⟨0, .inl rfl⟩
  else fromRealPos x (by rw [← ne_eq] at h'; simp [lt_of_le_of_ne h h'])

@[simp]
theorem fromReal_ext : (fromReal a h).toReal = a := by
  unfold fromReal; aesop

@[simp]
theorem fromReal_if_pos : ∀(h: 0 < a), fromReal a h' = fromRealPos a h := by
  unfold fromReal; aesop (add safe forward lt_irrefl 0)

@[simp]
theorem fromRealPos_ext : (fromRealPos a h).toReal = a := by aesop

theorem eq_ext : ∀(a b: DReal), a = b ↔ a.toReal = b.toReal := by
  intro a b; unfold toReal; cases a; cases b; aesop

theorem ne_ext : ∀(a b: DReal), a ≠ b ↔ a.toReal ≠ b.toReal := by
  intro a b; unfold toReal; cases a; cases b; aesop

--------------------
-- SIMPLE NUMBERS --
--------------------

instance instZero : Zero (DReal) :=
  ⟨ ⟨0, .inl rfl⟩ ⟩

@[simp]
theorem zero_ext : (0: DReal).toReal = 0 := by aesop

instance instOne : One (DReal) :=
  ⟨ ⟨1, .inr <| by simp⟩ ⟩

@[simp]
theorem one_ext : (1: DReal).toReal = 1 := by aesop

instance instInhabited : Inhabited DReal :=
  ⟨ 0 ⟩

----------------
-- INEQUALITY --
----------------

instance instLE : LE (DReal) := ⟨fun x y => x.toReal <= y.toReal⟩

theorem le_ext : ∀(a b: DReal), a ≤ b ↔ a.toReal ≤ b.toReal := by
  intro a b; (conv => lhs; unfold_projs; unfold toReal); rfl

theorem zero_le : ∀(a: DReal), 0 ≤ a := by
  intro a; rw [le_ext]; cases a.pos
  . apply Eq.le; assumption
  . apply LT.lt.le; assumption

@[simp]
theorem zero_le_real : ∀(a: DReal), 0 ≤ a.toReal := by
  intro a; rw [←zero_ext, ←le_ext]; exact zero_le a

theorem zero_le_one : (0 : DReal) ≤ 1 := by
  rw [le_ext]; simp

theorem le_total : ∀ (a b: DReal), a ≤ b ∨ b ≤ a := by
  intro a b; rw [le_ext, le_ext]; simp  [@LinearOrder.le_total ℝ _ _ _]

-----------------------
-- STRICT INEQUALITY --
-----------------------

instance instLT : LT (DReal) := ⟨fun x y => x.toReal < y.toReal⟩

theorem lt_ext : ∀(a b: DReal), a < b ↔ a.toReal < b.toReal := by
  intro a b; (conv => lhs; unfold_projs); rfl

theorem zero_lt_pos : ∀(a b:ℝ) (ha:0=a) (hb:0<b), (⟨a, .inl ha⟩: DReal) < ⟨b, .inr hb⟩ := by
  intro a b ha hb; rw [lt_ext]; rwa [ha] at hb;

theorem zero_lt_one : (0:DReal) < 1 := by
  rw [lt_ext]; simp

--------------
-- ADDITION --
--------------

instance instAdd : Add DReal := ⟨ fun
  | ⟨_, .inl _⟩,  y            => y
  | x,            ⟨_, .inl _⟩  => x
  | ⟨x, .inr hx⟩, ⟨y, .inr hy⟩ => ⟨x+y, .inr <| add_pos hx hy⟩⟩

@[simp]
theorem add_ext : ∀(a b: DReal), (a + b).toReal = a.toReal + b.toReal := by
  intro a b; (conv => lhs; unfold HAdd.hAdd instHAdd Add.add instAdd);
  simp; (cases' a with va pa; cases pa) <;> (cases' b with vb pb; cases pb) <;> aesop

@[simp]
lemma zero_add : ∀(a: DReal), 0 + a = a := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma add_zero : ∀(a: DReal), a + 0 = a := by
  intro a; rw [eq_ext]; simp

lemma add_comm : ∀(a b: DReal), a + b = b + a := by
  intro a b; rw [eq_ext]; simp [AddCommMagma.add_comm]

lemma add_assoc : ∀(a b c: DReal), (a + b) + c = a + (b + c) := by
  intro a b c; rw [eq_ext]; simp [AddSemigroup.add_assoc]

theorem le_of_add_le_add_left : ∀ (a b c: DReal), a + b ≤ a + c → b ≤ c := by
  intro a b c h; rw [le_ext] at *; simp_all [add_le_add_iff_left]

theorem add_le_add_left : ∀ (a b : DReal), a ≤ b → ∀ (c : DReal), c + a ≤ c + b := by
  intro a b h c; rw [le_ext] at *; simp_all

noncomputable
instance instSub : Sub (DReal) := ⟨ fun a b => ⟨max 0 (a.val - b.val),
  have : 0 ≤ a.val := by aesop
  have : 0 ≤ b.val := by aesop
  if h: b.val < a.val then .inr (by aesop)
  else .inl (by aesop)⟩ ⟩

@[simp]
theorem sub_ext : ∀(a b: DReal), (a - b).toReal = max 0 (a.toReal - b.toReal ):= by
  intro a b; (conv => lhs; unfold HSub.hSub instHSub Sub.sub instSub);

@[simp]
theorem sub_self : ∀(a: DReal), a - a = 0 := by
  intro a; rw [eq_ext]; simp_all

@[simp]
theorem sub_zero : ∀(a: DReal), a - 0 = a := by
  intro a; rw [eq_ext]; simp_all

--------------------
-- MULTIPLICATION --
--------------------

instance instMul : Mul DReal := ⟨ fun
  | ⟨x, .inr hx⟩, ⟨y, .inr hy⟩ => ⟨x*y, .inr <| mul_pos hx hy⟩
  | _,            _            => 0⟩

@[simp]
theorem mul_ext : ∀(a b: DReal), (a * b).toReal = a.toReal * b.toReal := by
  intro a b; (conv => lhs; unfold HMul.hMul instHMul Mul.mul instMul);
  simp; (cases' a with va pa; cases pa) <;> (cases' b with vb pb; cases pb) <;> aesop

@[simp]
lemma mul_zero : ∀(a: DReal), a * 0 = 0 := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma zero_mul : ∀(a: DReal), 0 * a = 0 := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma mul_one : ∀(a: DReal), a * 1 = a := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma one_mul : ∀(a: DReal), 1 * a = a := by
  intro a; rw [eq_ext]; simp

lemma mul_comm : ∀(a b: DReal), a * b = b * a := by
  intro a b; rw [eq_ext]; simp [CommMagma.mul_comm]

lemma mul_assoc : ∀(a b c: DReal), (a * b) * c = a * (b * c) := by
  intro a b c; rw [eq_ext]; simp [Semigroup.mul_assoc]

lemma left_distrib : ∀(a b c: DReal), a * (b + c) = a * b + a * c := by
  intro a b c; rw [eq_ext]; simp [Distrib.left_distrib]

lemma right_distrib : ∀(a b c: DReal), (a + b) * c = a * c + b * c := by
  intro a b c; rw [eq_ext]; simp [Distrib.right_distrib]

theorem mul_pos {a b : DReal} : 0 < a → 0 < b → 0 < a * b := by
  intro a b; rw [lt_ext] at *; simp [Real.mul_pos a b]

theorem mul_lt_mul_of_pos_left : ∀ (a b c : DReal), a < b → 0 < c → c * a < c * b := by
  intro a b c h1 h2; rw [lt_ext] at *; simp_all [mul_lt_mul_iff_left]

theorem mul_lt_mul_of_pos_right  : ∀ (a b c : DReal), a < b → 0 < c → a * c < b * c := by
  intro a b c h1 h2; rw [lt_ext] at *; simp_all [mul_lt_mul_iff_right]

---------------
-- INVERSION --
---------------


instance instInv : Inv DReal := ⟨ fun
  | ⟨x, .inr h⟩ =>
    { val := ⟨conditional_inv x.cauchy (@pos_not_limzero (by simp; exact @CauSeq.limZero_congr _  ℚ _ _ abs _) x h)⟩
    , pos := .inr <| by simpa [Real.ofCauchy_inv, inv_pos] using h }
  | _           => 0⟩

instance instDiv : Div DReal := ⟨ fun x y => x * y⁻¹ ⟩

@[simp]
theorem inv_ext : ∀(a : DReal), (a⁻¹).toReal = a.toReal⁻¹ := by
  intro a; (conv => lhs; unfold Inv.inv instInv);
  cases' a with va ha; cases ha <;> simp [Real.ofCauchy_inv]; assumption

@[simp]
lemma inv_zero : (0: DReal)⁻¹ = 0 := by
  rw [eq_ext, inv_ext]; simp

@[simp]
lemma mul_inv_cancel : ∀ (a : DReal), a ≠ 0 → a * a⁻¹ = 1 := by
  intro a h; rw [eq_ext, ne_ext] at *; simp;
  exact GroupWithZero.mul_inv_cancel a.toReal h

---------------
-- MIN & MAX --
---------------

def minc' : DReal -> DReal -> DReal
  | ⟨x, .inr hx⟩, ⟨y, .inr hy⟩ => ⟨Real.minc x y, .inr <| by simp_all⟩
  | _,            _            => 0

def maxc' : DReal -> DReal -> DReal
  | ⟨_, .inl _⟩, y            => y
  | x,            ⟨_, .inl _⟩ => x
  | ⟨x, .inr hx⟩, ⟨y, .inr hy⟩ => ⟨Real.maxc x y, .inr <| by simp_all⟩

-----------------------------------
-- SEMIFIELD AND OTHER INSTANCES --
-----------------------------------

def nsmul : ℕ -> DReal -> DReal
  | 0, _           => ⟨0, .inl rfl⟩
  | _, ⟨x, .inl h⟩ => ⟨x, .inl h⟩
  | .succ a, ⟨x, .inr h⟩ => ⟨a.succ * x, .inr (by rw [← Nat.add_one, Nat.cast_add, Nat.cast_one]; nlinarith)⟩

@[simp]
theorem nsmul_ext : ∀(x: DReal), (nsmul n x).toReal = Real.field.nsmul n (x.toReal) := by
  induction n with
  | zero => unfold nsmul; simp
  | succ n _ =>
    intro x; unfold nsmul; cases' x with v p
    cases' p with p p;
    . simp; rw [← p]; simp
    . simp

/-
instance instNNRatCast : NNRatCast DReal :=
  ⟨ fun q =>
    have : (q.val: ℝ) ≥ 0 := by aesop
    if hq: q = 0 then ⟨0, .inl rfl⟩
    else ⟨q, .inr (by
      have qge : q ≥ 0 := q.prop
      have : q ≥ (0: ℚ) := by norm_cast
      have : (q: ℚ) ≥ (0: ℝ) := by norm_cast
      have : q ≥ (0: ℝ) := by norm_cast
      have a : (0: ℚ) ≤ q := by aesop
      have b : ↑q ≠ (0: ℚ) := by aesop
      have : ↑q > (0: ℚ) := lt_of_le_of_ne a b.symm
      have : (0: ℝ) < ↑(↑q: ℚ) := by aesop
      have : (0: ℝ) < ↑q := by norm_cast
      nlinarith)⟩⟩
-/

instance instSemifield : Semifield (DReal) :=
  { nsmul := nsmul
  , nsmul_zero := by intro x; rw [eq_ext]; simp
  , nsmul_succ := by intro n x; rw [eq_ext]; simp; ring
  , nnqsmul := _
  , add_assoc := add_assoc
  , zero_add := zero_add
  , add_zero := add_zero
  , add_comm := add_comm
  , left_distrib := left_distrib
  , right_distrib := right_distrib
  , zero_mul := zero_mul
  , mul_zero := mul_zero
  , mul_assoc := mul_assoc
  , one_mul := one_mul
  , mul_one := mul_one
  , mul_comm := mul_comm
  , inv_zero := inv_zero
  , mul_inv_cancel := mul_inv_cancel
  , exists_pair_ne := by existsi 0; existsi 1; simp [eq_ext]
  }

instance : Semiring DReal := by infer_instance

instance : CommSemiring DReal := by infer_instance

instance semiring : Semiring DReal := by infer_instance

instance : CommMonoidWithZero DReal := by infer_instance

instance : MonoidWithZero DReal := by infer_instance

instance : AddCommMonoid DReal := by infer_instance

instance : AddMonoid DReal := by infer_instance

instance : AddCommSemigroup DReal := by infer_instance

instance : AddSemigroup DReal := by infer_instance

instance : CommMonoid DReal := by infer_instance

instance : Monoid DReal := by infer_instance

instance : CommSemigroup DReal := by infer_instance

instance : Semigroup DReal := by infer_instance

instance : Inhabited DReal :=
  ⟨0⟩

instance instPartialOrder : PartialOrder DReal where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le a b := by
    rw [lt_ext, le_ext, le_ext]; exact lt_iff_le_not_le
  le_refl a := by
    rw [le_ext]
  le_trans a b c := by
    rw [le_ext, le_ext, le_ext]; exact le_trans
  le_antisymm a b := by
    rw [le_ext, le_ext, eq_ext]; exact le_antisymm

noncomputable
instance instLinearOrderedCommSemiring : LinearOrderedCommSemiring DReal :=
  { le_of_add_le_add_left := le_of_add_le_add_left,
    exists_pair_ne := ⟨0, 1, zero_lt_one.ne⟩
    mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left
    mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right
    le_total := le_total
    mul_comm := instSemifield.mul_comm
    decidableLE := open Classical in inferInstance
    add_le_add_left := add_le_add_left
    zero_le_one := LT.lt.le zero_lt_one }

open Classical in noncomputable
instance instSupSet : SupSet DReal := ⟨ fun S => fromReal (sSup {toReal x | x ∈ S}) (by
  have : ∀x ∈ {toReal x | x ∈ S}, 0 ≤ x := by aesop
  exact Real.sSup_nonneg {toReal x | x ∈ S} this)⟩

@[simp]
lemma supSet_ext : ∀(s: Set DReal), (sSup s).toReal = sSup {DReal.toReal x | x ∈ s} := by
  intro s; unfold sSup instSupSet Real.instSupSet; simp

lemma sSup_empty : sSup (∅: Set DReal) = 0 := by
  unfold sSup instSupSet; rw [eq_ext]; simp

open Classical in noncomputable
instance instInfSet : InfSet DReal := ⟨ fun S => fromReal (sInf {toReal x | x ∈ S}) (by
  have : ∀x ∈ {toReal x | x ∈ S}, 0 ≤ x := by aesop
  exact Real.sInf_nonneg {toReal x | x ∈ S} this)⟩

@[simp]
lemma infSet_ext : ∀(s: Set DReal), (sInf s).toReal = sInf {DReal.toReal x | x ∈ s} := by
  intro s; unfold sInf instInfSet Real.instInfSet; simp

lemma sInf_empty : sInf (∅: Set DReal) = 0 := by
  unfold sInf instInfSet; rw [eq_ext]; simp

noncomputable
instance instConditionallyCompleteLattice : ConditionallyCompleteLattice DReal :=
  { le_csSup := by
      intro s a hs ha;
      have uhs : toReal a ∈ {DReal.toReal x | x ∈ s} := by aesop
      have uha : BddAbove {DReal.toReal x | x ∈ s} := by
        unfold BddAbove upperBounds Set.Nonempty at *; simp_all
        have ⟨x,p⟩ := hs
        existsi x; intro a as
        have p := p as;
        rw [← le_ext]; assumption
      rw [le_ext, supSet_ext]; exact le_csSup uha uhs
  , csSup_le := by
      intro s a hs ha;
      have uhs : Set.Nonempty {DReal.toReal x | x ∈ s} := by
        unfold Set.Nonempty at *; simp_all
        have ⟨x,p⟩ := hs
        existsi x; existsi x; simp_all
      have uha : toReal a ∈ upperBounds {DReal.toReal x | x ∈ s} := by
        unfold upperBounds at *; simp_all
        intro a as; have ha := ha as
        rw [← le_ext]; assumption
      rw [le_ext, supSet_ext]; exact csSup_le uhs uha
  , csInf_le := by
      intro s a hs ha;
      have uhs : toReal a ∈ {DReal.toReal x | x ∈ s} := by aesop
      have uha : BddBelow {DReal.toReal x | x ∈ s} := by
        unfold BddBelow lowerBounds Set.Nonempty at *; simp_all
        have ⟨x,p⟩ := hs
        existsi x; intro a as
        have p := p as;
        rw [← le_ext]; assumption
      rw [le_ext, infSet_ext]; exact csInf_le uha uhs
  , le_csInf := by
      intro s a hs ha;
      have uhs : Set.Nonempty {DReal.toReal x | x ∈ s} := by
        unfold Set.Nonempty at *; simp_all
        have ⟨x,p⟩ := hs
        existsi x; existsi x; simp_all
      have uha : toReal a ∈ lowerBounds {DReal.toReal x | x ∈ s} := by
        unfold lowerBounds at *; simp_all
        intro a as; have ha := ha as
        rw [← le_ext]; assumption
      rw [le_ext, infSet_ext]; exact le_csInf uhs uha }

@[simp]
theorem max_ext : ∀(a b: DReal), (max a b).toReal = max a.toReal b.toReal := by
  intro a b; (conv => lhs; unfold_projs);
  (cases' a with va ha; cases' ha with za pa) <;> (cases' b with vb hb; cases' hb with zb pb) <;> simp
  . aesop
  . rw [za] at pb; simp [max_eq_right (LT.lt.le pb)];
    have : va ≤ vb := (LT.lt.le pb); unfold_projs at this; aesop
  . rw [zb] at pa; simp [max_eq_left (LT.lt.le pa)];
    have := (le_not_le_of_lt pa).right; unfold_projs at this; aesop
  . by_cases h : va ≤ vb;
    . have h' := h; unfold_projs at h'; aesop
    . have h' := h; unfold_projs at h'; simp_all [↓reduceIte]; rw [max_eq_left (LT.lt.le h)]

@[simp]
theorem min_ext : ∀(a b: DReal), (min a b).toReal = min a.toReal b.toReal := by
  intro a b; (conv => lhs; unfold_projs);
  (cases' a with va ha; cases' ha with za pa) <;> (cases' b with vb hb; cases' hb with zb pb) <;> simp
  . aesop
  . rw [za] at pb; simp [min_eq_left (LT.lt.le pb)];
    have : va ≤ vb := (LT.lt.le pb); unfold_projs at this; aesop
  . rw [zb] at pa; simp [min_eq_right (LT.lt.le pa)];
    have := (le_not_le_of_lt pa).right; unfold_projs at this; aesop
  . by_cases h : va ≤ vb;
    . have h' := h; unfold_projs at h'; aesop
    . have h' := h; unfold_projs at h'; simp_all [↓reduceIte]; rw [min_eq_right (LT.lt.le h)]

@[simp]
theorem maxc_ext' : ∀(a b: DReal), (maxc' a b) = max a b := by
  intro a b; rw [eq_ext]; unfold maxc';
  (cases' a with va ha; cases' ha with za pa) <;> (cases' b with vb hb; cases' hb with zb pb) <;> simp
  . aesop
  . rw[za] at pb; simp [max_eq_right (LT.lt.le pb)]
  . rw[zb] at pa; simp [max_eq_left (LT.lt.le pa)]

@[simp]
theorem minc_ext' : ∀(a b: DReal), (minc' a b) = min a b := by
  intro a b; rw [eq_ext]; unfold minc';
  (cases' a with va ha; cases' ha with za pa) <;> (cases' b with vb hb; cases' hb with zb pb) <;> simp
  . aesop
  . rw[za] at pb ⊢; simp [min_eq_left (LT.lt.le pb)]
  . rw[zb] at pa ⊢; simp [min_eq_right (LT.lt.le pa)]

/-
noncomputable def sub (a: DReal) (b: DReal) (h: b ≤ a): DReal :=
  if h': b = a then ⟨0, .inl rfl⟩
  else ⟨a.val - b.val, .inr (by ?)⟩

noncomputable def div (a: DReal) (b: DReal) (h: 0 ≠ b): DReal :=
  match a, b with
  | ⟨_, .inl _⟩,  _            => ⟨0, .inl rfl⟩
  | _,            ⟨y, .inl hy⟩  => by exfalso; unfold_projs at *; aesop
  | ⟨x, .inr hx⟩, ⟨y, .inr hy⟩ => ⟨x * b.val, .inr (by ?)⟩
-/


--------------------------
-- RANDOM USEFUL THINGS --
--------------------------

@[simp]
lemma nat_dreal_real (n: ℕ) : ↑(↑n: DReal) = (↑n: ℝ) := by
  induction n <;> simp_all

end DReal
