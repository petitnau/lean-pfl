import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.CauSeq.Completion
import Data.Min
import Mathlib.Order.CompleteLatticeIntervals

/-
section

variable [LinearOrderedField α] [Ring β] [Min β] (abv : β → α) [IsAbsoluteValue abv]

instance [Min β]: Min (ℕ -> β) :=
  ⟨fun f g => fun x => min (f x) (g x)⟩

lemma min_lemma : ∀(x y z w: β), abv (min x y - min z w) <= abv (x - z) + abv (y - w) := by


theorem rat_max_continuous_lemma {ε : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ →
      abv (min a₁ a₂ - min b₁ b₂) < ε :=
  ⟨ε / 2, half_pos ε0, fun {a₁ a₂ b₁ b₂} h₁ h₂ => by
    calc abv (min a₁ a₂ - min b₁ b₂)
    _ ≤ abv (a₁ - b₁) + abv (a₂ - b₂) := by simp [min_lemma]
    _ < ε / 2 + abv (a₂ - b₂) := by simp_all only [add_lt_add_iff_right]
    _ < ε / 2 + ε / 2 := by simp_all only [add_lt_add_iff_left]
    _ = ε := by simp [add_halves]⟩

theorem max {α : Type u_2} {β : Type u_1} [LinearOrderedField α] [Ring β] [Min β] {abv : β → α}
  [IsAbsoluteValue abv] {f g : ℕ → β} (hf : IsCauSeq abv f) (hg : IsCauSeq abv g)
  : IsCauSeq abv (min f g) := fun _ ε0 =>
  let ⟨_, δ0, Hδ⟩ := rat_max_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun _ ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl;
    Hδ (H₁ _ ij) (H₂ _ ij)⟩

instance : Min (CauSeq β abv) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

theorem min_equiv_min {α : Type u_2} {β : Type u_1} [LinearOrderedField α] [Ring β] [Min β]
  {abv : β → α} [IsAbsoluteValue abv] {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    min f1 g1 ≈ min f2 g2 := by simpa only [← add_sub_add_comm] using CauSeq.add_limZero hf hg

instance : Min (CauSeq.Completion.Cauchy abv) :=
  ⟨(Quotient.map₂ min) fun _ _ hf _ _ hg => min_equiv_min hf hg⟩

end
-/

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

lemma eq_elim_lifton {α β : Sort*} [s : Setoid α] (q : Quotient s)
    (f : α → β) (c : (a b : α) → a ≈ b → f a = f b)
    : Quotient.liftOn q f c = Quotient.elim q (generalize q f) (generalize_h q f c) := by
    unfold Quotient.liftOn; unfold Quot.liftOn; unfold Quotient.elim;
    have ⟨a, ha⟩ : ∃a, ⟦a⟧ = q := Quotient.exists_rep q
    have ha : q = ⟦a⟧ := ha.symm
    have elem : { a_1 // ⟦a_1⟧ = q} := ⟨a, by aesop⟩
    have elem' : { a_1 // ⟦a_1⟧ = ⟦a⟧} := by rwa [ha] at elem
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


inductive DReal where
  | zero : DReal
  | pos  : { r: ℝ // 0 < r } -> DReal

namespace DReal

----------------
-- CONVERSION --
----------------

@[coe] def toReal : DReal → ℝ
  | DReal.zero => 0
  | DReal.pos x => x.val
instance : Coe DReal ℝ := ⟨toReal⟩

@[simp]
theorem zero_ext : (zero: DReal).toReal = 0 := by aesop

@[simp]
theorem pos_ext : (pos x: DReal).toReal = x := by aesop

def fromRealZero (x: ℝ) (_: 0 = x) : DReal :=
  zero

def fromRealPos (x: ℝ) (h: 0 < x) : DReal :=
  DReal.pos ⟨x, h⟩

noncomputable def fromReal (x: ℝ) (h: 0 ≤ x) : DReal :=
  if h': 0 = x then fromRealZero x h'
  else fromRealPos x (by rw [← ne_eq] at h'; simp [lt_of_le_of_ne h h'])

@[simp]
theorem fromRealId : fromReal a h = a := by
  unfold fromReal; by_cases (a = zero); all_goals aesop

@[simp]
theorem fromReal_ext : (fromReal a h).toReal = a := by
  unfold fromReal; by_cases (a = zero); all_goals aesop

@[simp]
theorem fromRealZeroId : fromRealZero (zero) h = zero := by unfold fromRealZero; aesop

@[simp]
theorem fromRealZero_ext : (fromRealZero a h).toReal = a := by aesop

@[simp]
theorem fromRealPosId : fromRealPos (pos a) h = pos a := by aesop

@[simp]
theorem fromRealPos_ext : (fromRealPos a h).toReal = a := by aesop

@[simp]
theorem eq_ext : ∀(a b: DReal), a = b ↔ a.toReal = b.toReal := by
  intro a b; unfold toReal; cases a <;> cases b <;> (simp; try aesop)

--------------------
-- SIMPLE NUMBERS --
--------------------

instance : Zero (DReal) :=
  ⟨ zero ⟩

@[simp]
theorem zero_ext' : (0: DReal) = zero := by rfl

instance : One (DReal) :=
  ⟨ pos ⟨1, by simp⟩ ⟩

@[simp]
theorem one_ext : (1: DReal).toReal = 1 := by aesop

----------------
-- INEQUALITY --
----------------

def le : DReal -> DReal -> Prop
  | zero,  zero  => True
  | zero,  pos _ => True
  | pos _, zero  => False
  | pos x, pos y => x <= y
instance : LE (DReal) := ⟨le⟩

@[simp]
theorem le_ext : ∀(a b: DReal), a ≤ b ↔ a.toReal ≤ b.toReal := by
  intro a b; (conv => lhs; unfold_projs; unfold toReal le); cases a <;> cases b <;> simp;
  case zero.pos a => exact LT.lt.le a.prop
  case pos.zero a => exact a.prop

theorem zero_le : ∀(a: DReal), 0 ≤ a := by
  intro a; rw [le_ext]; simp; cases a <;> simp
  case pos a => exact LT.lt.le a.prop

@[simp]
theorem zero_le_real : ∀(a: DReal), 0 ≤ a.toReal := by
  intro a; rw [←zero_ext, ←le_ext]; exact zero_le a

theorem zero_le_one' : (0 : DReal) ≤ 1 := by
  rw [le_ext]; simp

theorem le_total' : ∀ (a b: DReal), a ≤ b ∨ b ≤ a := by
  intro a b; rw [le_ext, le_ext]; simp  [@LinearOrder.le_total ℝ _ _ _]

-----------------------
-- STRICT INEQUALITY --
-----------------------

def lt : DReal -> DReal -> Prop
  | zero,  zero  => False
  | zero,  pos _ => True
  | pos _, zero  => False
  | pos x, pos y => x < y
instance : LT (DReal) := ⟨lt⟩

@[simp]
theorem lt_ext : ∀(a b: DReal), a < b ↔ a.toReal < b.toReal := by
  intro a b; (conv => lhs; unfold_projs); unfold toReal lt; cases a <;> cases b <;> simp;
  case zero.pos a => exact a.prop
  case pos.zero a => exact LT.lt.le a.prop

theorem zero_lt_pos : ∀a, zero < pos a := by
  intro a; rw [lt_ext]; simp; exact a.prop

theorem zero_lt_one'' : zero < 1 := by
  rw [lt_ext]; simp

--------------
-- ADDITION --
--------------

def add : DReal -> DReal -> DReal
  | zero,  zero  => zero
  | zero,  pos y => pos y
  | pos x, zero  => pos x
  | pos x, pos y => pos ⟨x+y, by simp [add_pos x.prop y.prop]⟩
instance : Add DReal := ⟨ add ⟩

@[simp]
theorem add_ext : ∀(a b: DReal), (a + b).toReal = a.toReal + b.toReal := by
  intro a b; (conv => lhs; unfold HAdd.hAdd instHAdd Add.add instAddDReal add);
  simp; cases a <;> cases b <;> simp

@[simp]
lemma zero_add' : ∀(a: DReal), zero + a = a := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma add_zero' : ∀(a: DReal), a + zero = a := by
  intro a; rw [eq_ext]; simp

lemma add_comm' : ∀(a b: DReal), a + b = b + a := by
  intro a b; rw [eq_ext]; simp [add_comm]

lemma add_assoc' : ∀(a b c: DReal), (a + b) + c = a + (b + c) := by
  intro a b c; rw [eq_ext]; simp [add_assoc]

theorem le_of_add_le_add_left' : ∀ (a b c: DReal), a + b ≤ a + c → b ≤ c := by
  intro a b c h; rw [le_ext] at *; simp_all [add_le_add_iff_left]

theorem add_le_add_left' : ∀ (a b : DReal), a ≤ b → ∀ (c : DReal), c + a ≤ c + b := by
  intro a b h c; rw [le_ext] at *; simp_all

--------------------
-- MULTIPLICATION --
--------------------

def mul : DReal -> DReal -> DReal
  | pos x, pos y => pos (⟨x*y, by simp [mul_pos x.prop y.prop]⟩)
  | _,     _     => zero
instance : Mul DReal := ⟨ mul ⟩

@[simp]
theorem mul_ext : ∀(a b: DReal), (a * b).toReal = a.toReal * b.toReal := by
  intro a b; (conv => lhs; unfold HMul.hMul instHMul Mul.mul instMulDReal mul);
  simp; cases a <;> cases b <;> simp

@[simp]
lemma mul_zero' : ∀(a: DReal), a * zero = zero := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma zero_mul' : ∀(a: DReal), zero * a = zero := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma mul_one' : ∀(a: DReal), a * 1 = a := by
  intro a; rw [eq_ext]; simp

@[simp]
lemma one_mul' : ∀(a: DReal), 1 * a = a := by
  intro a; rw [eq_ext]; simp

lemma mul_comm' : ∀(a b: DReal), a * b = b * a := by
  intro a b; rw [eq_ext]; simp [mul_comm]

lemma mul_assoc' : ∀(a b c: DReal), (a * b) * c = a * (b * c) := by
  intro a b c; rw [eq_ext]; simp [mul_assoc]

lemma left_distrib' : ∀(a b c: DReal), a * (b + c) = a * b + a * c := by
  intro a b c; rw [eq_ext]; simp [left_distrib]

lemma right_distrib' : ∀(a b c: DReal), (a + b) * c = a * c + b * c := by
  intro a b c; rw [eq_ext]; simp [right_distrib]

theorem mul_pos' {a b : DReal} : zero < a → zero < b → zero < a * b := by
  intro a b; rw [lt_ext] at *; simp [Real.mul_pos a b]

theorem mul_lt_mul_of_pos_left' : ∀ (a b c : DReal), a < b → zero < c → c * a < c * b := by
  intro a b c h1 h2; rw [lt_ext] at *; simp_all [mul_lt_mul_iff_left]

theorem mul_lt_mul_of_pos_right' : ∀ (a b c : DReal), a < b → zero < c → a * c < b * c := by
  intro a b c h1 h2; rw [lt_ext] at *; simp_all [mul_lt_mul_iff_right]

---------------
-- INVERSION --
---------------

section CauSeq.Inversion

open Classical
variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

noncomputable def inv' : CauSeq β abv → CauSeq.Completion.Cauchy abv :=
  fun f => CauSeq.Completion.mk <| if h : CauSeq.LimZero f then 0 else CauSeq.inv f h

def invc' (h: ¬ Quotient.liftOn x CauSeq.LimZero limZero_congr) : (f : CauSeq β abv) → ⟦f⟧ = x → CauSeq.Completion.Cauchy abv :=
  fun f _ => CauSeq.Completion.mk <| CauSeq.inv f (by aesop)

def invc (x: CauSeq.Completion.Cauchy abv) (h: ¬ Quotient.liftOn x CauSeq.LimZero limZero_congr) : CauSeq.Completion.Cauchy abv :=
  (Quotient.elim x (invc' h)) fun f g fxh gxh => by
    unfold invc'
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
    rw [← mul_one (CauSeq.Completion.mk (CauSeq.inv f hf)), ← Ig', ← mul_assoc, If, mul_assoc, Ig', mul_one]

@[simp]
theorem invc_correct {x: CauSeq.Completion.Cauchy abv} {h: ¬ Quotient.liftOn x CauSeq.LimZero limZero_congr}: invc x h = x⁻¹ := by
  unfold_projs; unfold invc
  rw [eq_elim_lifton]
  congr
  unfold invc' generalize
  simp
  funext f h''
  rw [← CauSeq.Completion.mk_eq_mk] at h''
  congr
  by_cases h' : CauSeq.LimZero f
  exfalso
  apply h
  rw [← h'']
  rw [Quotient.liftOn_mk CauSeq.LimZero limZero_congr f]
  assumption
  simp [h']

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

def inv :  DReal -> DReal
  | zero  => zero
  | pos x => pos (⟨⟨invc x.val.cauchy (@pos_not_limzero (by simp; exact @CauSeq.limZero_congr _  ℚ _ _ abs _) x.val x.prop)⟩, by simpa [Real.ofCauchy_inv, inv_pos] using x.prop⟩)
instance : Inv DReal := ⟨ inv ⟩

@[simp]
theorem inv_ext : ∀(a : DReal), (a⁻¹).toReal = a.toReal⁻¹ := by
  intro a; (conv => lhs; unfold Inv.inv instInvDReal inv); cases a <;> simp [Real.ofCauchy_inv];

lemma inv_zero' : zero⁻¹ = 0 := by
  rw [eq_ext]; simp

lemma mul_inv_cancel' : ∀ (a : DReal), a ≠ zero → a * a⁻¹ = 1 := by
  intro a h; rw [Ne, eq_ext, ←Ne] at *; simp_all [mul_inv_cancel]

---------------
-- MIN & MAX --
---------------

def minc' : DReal -> DReal -> DReal
  | zero,  zero  => zero
  | zero,  pos _ => zero
  | pos _, zero  => zero
  | pos x, pos y => pos ⟨minc x.val y.val, by simp [x.prop, y.prop]⟩

theorem minc_ext : ∀(a b: DReal), (minc' a b).toReal = Min.min a.toReal b.toReal := by
  intro a b; unfold minc'; cases a <;> cases b <;> simp;
  case zero.pos a => simp [min_eq_left (LT.lt.le a.prop)]
  case pos.zero a => simp [min_eq_right (LT.lt.le a.prop)]

def maxc' : DReal -> DReal -> DReal
  | zero,  zero  => zero
  | zero,  pos y => pos y
  | pos x, zero  => pos x
  | pos x, pos y => pos ⟨maxc x.val y.val, by simp [x.prop, y.prop]⟩

theorem maxc_ext : ∀(a b: DReal), (maxc' a b).toReal = Max.max a.toReal b.toReal := by
  intro a b; unfold maxc'; cases a <;> cases b <;> simp;
  case zero.pos a => simp [max_eq_right (LT.lt.le a.prop)]
  case pos.zero a => simp [max_eq_left (LT.lt.le a.prop)]

-----------------------------------
-- SEMIFIELD AND OTHER INSTANCES --
-----------------------------------

instance semifield : Semifield (DReal) :=
  { add := add
  , add_assoc := add_assoc'
  , zero_add := zero_add'
  , add_zero := add_zero'
  , add_comm := add_comm'
  , mul := mul
  , left_distrib := left_distrib'
  , right_distrib := right_distrib'
  , zero_mul := zero_mul'
  , mul_zero := mul_zero'
  , mul_assoc := mul_assoc'
  , one_mul := one_mul'
  , mul_one := mul_one'
  , mul_comm := mul_comm'
  , inv := inv
  , inv_zero := inv_zero'
  , mul_inv_cancel := mul_inv_cancel'
  , exists_pair_ne := by existsi 0; existsi 1; simp
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

instance partialOrder : PartialOrder DReal where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le a b := by
    unfold_projs; unfold lt le; cases a <;> cases b <;> simp; exact LT.lt.le;
  le_refl a := by
    unfold_projs; unfold le; cases a <;> simp
  le_trans a b c := by
    unfold_projs; unfold le; cases a <;> cases b <;> cases c <;> simp; exact LE.le.trans
  le_antisymm a b := by
    unfold_projs; unfold le; cases a <;> cases b <;> intro h1 h2 <;> simp_all; exact LE.le.antisymm h1 h2

instance : Preorder DReal := by infer_instance

noncomputable instance : LinearOrderedCommSemiring DReal :=
  { partialOrder,
    semiring with
    le_of_add_le_add_left := le_of_add_le_add_left',
    exists_pair_ne := ⟨0, 1, zero_lt_one''.ne⟩
    mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left'
    mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right'
    le_total := le_total'
    mul_comm := semifield.mul_comm
    decidableLE := open Classical in inferInstance
    add_le_add_left := add_le_add_left'
    zero_le_one := LT.lt.le zero_lt_one'' }

@[simp]
theorem max_ext : ∀(a b: DReal), (max a b).toReal = max a.toReal b.toReal := by
  intro a b; (conv => lhs; unfold_projs; unfold le); cases a <;> cases b <;> simp
  case zero.pos a => simp [max_eq_right (LT.lt.le a.prop)]
  case pos.zero a => simp [max_eq_left (LT.lt.le a.prop)]
  case pos.pos a b =>
      by_cases h : a ≤ b;
      . have : (↑a:ℝ) ≤ b := by simp_all [Subtype.coe_le_coe]
        simp_all
      . have : (↑a:ℝ) > b := by simp_all [Subtype.coe_le_coe]
        simp [h, ↓reduceIte, max_eq_left (LT.lt.le this)]

@[simp]
theorem min_ext : ∀(a b: DReal), (min a b).toReal = min a.toReal b.toReal := by
  intro a b; (conv => lhs; unfold_projs; unfold le); cases a <;> cases b <;> simp
  case zero.pos a => simp [min_eq_left (LT.lt.le a.prop)]
  case pos.zero a => simp [min_eq_right (LT.lt.le a.prop)]
  case pos.pos a b =>
      by_cases h : a ≤ b;
      . have : (↑a:ℝ) ≤ b := by simp_all [Subtype.coe_le_coe]
        simp_all
      . have : (↑a:ℝ) > b := by simp_all [Subtype.coe_le_coe]
        simp [h, ↓reduceIte, min_eq_right (LT.lt.le this)]

@[simp]
theorem maxc_ext' : ∀(a b: DReal), (maxc' a b) = max a b := by
  intro a b; unfold maxc'; cases a <;> cases b <;> simp [eq_ext];
  case zero.pos a => simp [max_eq_right (LT.lt.le (by aesop : (0:ℝ) < ↑a))]
  case pos.zero a => simp [max_eq_left (LT.lt.le (by aesop : (0:ℝ) < ↑a))]

@[simp]
theorem minc_ext' : ∀(a b: DReal), (minc' a b) = min a b := by
  intro a b; unfold minc'; cases a <;> cases b <;> simp [eq_ext];
  case zero.pos a => simp [min_eq_left (LT.lt.le (by aesop : (0:ℝ) < ↑a))]
  case pos.zero a => simp [min_eq_right (LT.lt.le (by aesop : (0:ℝ) < ↑a))]

open Classical
noncomputable def sSup (S: Set DReal) : DReal :=
  let S': Set ℝ := {toReal x | x ∈ S}
  if h : Set.Nonempty S' ∧ BddAbove S' then
    have h': ∃ (x : ℝ), IsLUB S' x := Real.exists_isLUB S' h.1 h.2
    let x := Classical.choose h'
    fromReal x (by
        have ⟨y, yh⟩ := h.1
        have : IsLUB S' (Classical.choose h') := choose_spec h'
        have : IsLUB S' x := by simp_all
        have : x ∈ upperBounds S' := by unfold IsLUB IsLeast at this; simp_all
        have ha : y ≤ x := by aesop
        have hb : 0 ≤ y := by aesop
        exact le_trans' ha hb)
  else 0
noncomputable instance : SupSet DReal := ⟨ sSup ⟩

noncomputable def sInf (S: Set DReal) : DReal :=
  let S': Set ℝ := {toReal x | x ∈ S}
  if h : Set.Nonempty S' ∧ BddAbove S' then
    have h': ∃ (x : ℝ), IsLUB S' x := Real.exists_isLUB S' h.1 h.2
    let x := Classical.choose h'
    fromReal x (by
        have ⟨y, yh⟩ := h.1
        have : IsLUB S' (Classical.choose h') := choose_spec h'
        have : IsLUB S' x := by simp_all
        have : x ∈ upperBounds S' := by unfold IsLUB IsLeast at this; simp_all
        have ha : y ≤ x := by aesop
        have hb : 0 ≤ y := by aesop
        exact le_trans' ha hb)
  else 0
noncomputable instance : InfSet DReal := ⟨ sInf ⟩


noncomputable instance : ConditionallyCompleteLattice DReal :=
  { le_csSup := sorry
  , csSup_le := sorry
  , csInf_le := sorry
  , le_csInf := sorry }

end DReal
