import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Chain
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Algebra.Order.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Data.DReal
open BigOperators Pointwise

set_option maxHeartbeats 2000000

namespace Real

lemma sSup_pointwise [CompleteLattice α] [Preorder β] [ConditionallyCompleteLinearOrder γ]
  (X: Set α) (cX: IsChain (· < ·) X) (f: α -> β) (mf: Monotone f) (g: α -> β) (mg: Monotone g)
  (op: β -> β -> γ) (mop: ∀a ∈ X, ∀b ∈ X, ∀c ∈ X, ∀d ∈ X, f a ≤ f c → g b ≤ g d → op (f a) (g b) ≤ op (f c) (g d))
  : sSup ((λx => op (f x) (g x)) '' X) = sSup (Set.image2 op (f '' X) (g '' X)) := by
    apply csSup_eq_csSup_of_forall_exists_le
    . intro x xfgX
      have ⟨a, ha1, ha2⟩ : ∃a ∈ X, x = op (f a) (g a) := by aesop
      have : op (f a) (g a) ∈ {c | ∃ a ∈ X, ∃ b ∈ X, op (f a) (g b) = c} := by apply Set.mem_image2_of_mem; simp_all; assumption
      existsi (op (f a) (g a))
      simp_all;
    . intro y yfXgX;
      have ⟨fa, fafX, gb, gbgX, hfagb⟩: ∃fa ∈ (f '' X), ∃gb ∈ (g '' X), op fa gb = y := by apply Set.mem_image2.mp yfXgX
      have ⟨a, ha1, ha2⟩ : ∃a ∈ X, fa = f a := by aesop
      have ⟨b, hb1, hb2⟩ : ∃b ∈ X, gb = g b := by aesop
      rw [ha2,hb2] at hfagb;
      let c := a ⊔ b
      have test := cX ha1 hb1; simp_all
      have : a ≤ b ∨ b < a := by by_cases h: a = b; left; simp_all; apply test at h; cases' h with h h; left; exact h.le; right; exact h
      have : c = a ∨ c = b := by rcases this with h | h; (right; apply sup_eq_right.mpr; assumption); (left; apply sup_eq_left.mpr; exact h.le)
      have hc : c ∈ X := by rcases this; simp_all; simp_all
      have : a ≤ c := by aesop
      have fac : f a ≤ f c := by aesop
      have : b ≤ c := by aesop
      have gbc : g b ≤ g c := by aesop
      existsi c
      simp_all
      rw [← hfagb]
      apply mop a ha1 b hb1 c hc c hc fac gbc

lemma sSup_add_le
  (A: Set ℝ) (bddA: BddAbove A) (neA: Set.Nonempty A)
  (B: Set ℝ) (bddB: BddAbove B) (neB: Set.Nonempty B)
  : sSup (A + B) ≤ sSup A + sSup B := by
  have a_b_le_sups: ∀a ∈ A, ∀b ∈ B, a + b ≤ sSup A + sSup B := by
    intro a aA b bB
    have a_le_sup : a ≤ sSup A := by simp_all only [le_csSup]
    have b_le_sup: b ≤ sSup B := by simp_all only [le_csSup]
    show a + b ≤ sSup A + sSup B;
      exact add_le_add a_le_sup b_le_sup
  have : ∀ab ∈ A+B, ab ≤ sSup A + sSup B := by
    intro ab ⟨a, aA, b, bA, ab_def⟩
    have : a + b ≤ sSup A + sSup B := a_b_le_sups a aA b bA
    show ab ≤ sSup A + sSup B;
      simp_all only
  show   sSup (A + B) ≤ sSup A + sSup B;
    apply csSup_le (by aesop) this

lemma sSup_add_ge
  (A: Set ℝ) (bddA: BddAbove A) (neA: Set.Nonempty A)
  (B: Set ℝ) (bddB: BddAbove B) (neB: Set.Nonempty B)
  : sSup (A + B) ≥ sSup A + sSup B := by
  have : BddAbove (A + B) := by
    simp_all [bddAbove_def];
    have ⟨bddAx, bddAp⟩ := bddA
    have ⟨bddBx, bddBp⟩ := bddB
    existsi (bddAx + bddBx); intro ab abAB;
    have ⟨a, aA, b, bB, ab_def⟩: ∃a ∈ A, ∃b ∈ B, a + b = ab := by simp_all [Set.mem_add]
    rw [← ab_def]; apply add_le_add; simp_all; simp_all;

  have ab_le_sSupAB: ∀ab ∈ A+B, ab ≤ sSup (A + B) := by simp_all only [le_csSup, implies_true];
  have : ∀a ∈ A, ∀b ∈ B, a + b ≤ sSup (A + B) := by
    intro a aA b bB;
    have : a + b ∈ A + B := by simp_all only [Set.add_mem_add]
    show   a + b ≤ sSup (A + B);
      simp_all only
  have : ∀a ∈ A, ∀b ∈ B, a ≤ sSup (A + B) - b := by
    intro a aA b bB; have := this a aA b bB; linarith
  have : ∀b ∈ B, sSup A ≤ sSup (A + B) - b := by
    intro a aA; apply csSup_le neA; simp_all
  have : ∀b ∈ B, sSup A + b ≤ sSup (A + B) := by
    intro a aA; have := this a aA; linarith
  have : ∀b ∈ B,  b ≤ - sSup A + sSup (A + B) := by
    intro b bB; have := this b bB; linarith
  have : sSup B ≤ - sSup A + sSup (A + B) := by
    apply csSup_le neB; simp_all
  show  sSup A + sSup B ≤ sSup (A + B);
    linarith

@[simp]
theorem sSup_add'
  (A: Set ℝ) (bddA: BddAbove A) (neA: Set.Nonempty A)
  (B: Set ℝ) (bddB: BddAbove B) (neB: Set.Nonempty B)
  : sSup (A + B) = sSup A + sSup B := le_antisymm (sSup_add_le A bddA neA B bddB neB) (GE.ge.le (sSup_add_ge A bddA neA B bddB neB))

@[simp]
theorem sSup_add'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· < ·) X) (f: α -> ℝ) (mf: Monotone f) (g: α -> ℝ) (mg: Monotone g)
  : sSup ((f + g) '' X) = sSup (f '' X) + sSup (g '' X) := by
  rw [← sSup_add']; apply sSup_pointwise;
  . aesop
  . aesop
  . aesop
  . intro a _ b _ c _ d _ ac bd; exact add_le_add ac bd
  . simp_all [Monotone.map_bddAbove]
  . aesop
  . simp_all [Monotone.map_bddAbove]
  . aesop

lemma sSup_mina_le (x: ℝ) (A: Set ℝ) (bddA: BddAbove A) (neA: Set.Nonempty A)
  : sSup {min x a | a ∈ A} ≤ min x (sSup A) := by
  have neXA: {min x a | a ∈ A}.Nonempty := by
    have ⟨neAx, neAp⟩ := neA
    unfold Set.Nonempty; simp_all; existsi (min x neAx); existsi neAx; simp_all
  have a_le_sups: ∀a ∈ A, min x a ≤ min x (sSup A) := by
    intro a aA; simp_all; right; simp_all only [le_csSup]
  have : ∀xa ∈ {min x a | a ∈ A}, xa ≤ min x (sSup A) := by
    intro ab ⟨a, aA, xa_def⟩
    have : min x a ≤ min x (sSup A) := a_le_sups a aA
    show ab ≤ min x (sSup A);
      simp_all only
  show   sSup {min x a | a ∈ A} ≤ min x (sSup A);
    apply csSup_le (by simp_all) this

lemma sSup_mina_ge (x: ℝ) (A: Set ℝ) (bddA: BddAbove A) (neA: Set.Nonempty A)
  : sSup {min x a | a ∈ A} ≥ min x (sSup A) := by
  have ba : BddAbove {min x a | a ∈ A} := by
    simp_all [bddAbove_def];
    have ⟨bddAx, bddAp⟩ := bddA
    existsi bddAx; intro a aA;
    right; exact bddAp a aA

  have ab_le_sSupAB: ∀xa ∈ {min x a | a ∈ A}, xa ≤ sSup {min x a | a ∈ A} := by simp_all only [le_csSup, implies_true];
  have : ∀a ∈ A, min x a ≤ sSup {min x a | a ∈ A} := by
    intro a aA;
    have : min x a ∈ {min x a | a ∈ A} := by aesop
    show   min x a ≤ sSup {min x a | a ∈ A};
      simp_all only
  show  min x (sSup A) ≤ sSup {min x a | a ∈ A};
  by_cases h: ∀a ∈ A, a ≤ x
  . rw [min_eq_right];
    simp_all
    apply csSup_le neA; intro b bA;
    have : min x b ∈ {min x a | a ∈ A} := by simp_all; existsi b; simp_all
    apply le_csSup_of_le ba this; simp_all
    exact csSup_le neA h
  . rw [min_eq_left];
    simp_all
    apply le_csSup; simp_all; simp_all
    have ⟨hx, hp1, hp2⟩ := h
    existsi hx; simp_all;
    exact LT.lt.le hp2
    simp_all
    have ⟨hx, hp1, hp2⟩ := h
    apply le_csSup_of_le bddA hp1;
    exact LT.lt.le hp2

@[simp]
lemma sSup_mina' (x: ℝ) (A: Set ℝ) (bddA: BddAbove A) (neA: Set.Nonempty A)
  : sSup {min x a | a ∈ A} = min x (sSup A) := le_antisymm (sSup_mina_le x A bddA neA) (GE.ge.le (sSup_mina_ge x A bddA neA))

lemma sSup_mul_le
  (A: Set ℝ) (bddA: BddAbove A) (neA: Set.Nonempty A) (posA: ∀a ∈ A, a ≥ 0)
  (B: Set ℝ) (bddB: BddAbove B) (neB: Set.Nonempty B) (posB: ∀b ∈ B, b ≥ 0)
  : sSup (A * B) ≤ sSup A * sSup B := by
  have ⟨ha, hp⟩ := neA
  have supA_nonneg : 0 ≤ sSup A := le_csSup_of_le bddA hp (posA ha hp).le
  have a_b_le_sups: ∀a ∈ A, ∀b ∈ B, a*b ≤ sSup A * sSup B := by
    intro a aA b bB
    have a_le_sup : a ≤ sSup A := by simp_all only [le_csSup]
    have b_le_sup: b ≤ sSup B := by simp_all only [le_csSup]
    show a * b ≤ sSup A * sSup B;
      exact mul_le_mul a_le_sup b_le_sup (posB b bB) supA_nonneg
  have : ∀ab ∈ A*B, ab ≤ sSup A * sSup B := by
    intro ab ⟨a, aA, b, bA, ab_def⟩
    have : a * b ≤ sSup A * sSup B := a_b_le_sups a aA b bA
    show ab ≤ sSup A * sSup B;
      simp_all only
  show   sSup (A * B) ≤ sSup A * sSup B;
    apply csSup_le (by aesop) this

lemma sSup_mul_ge
  (A: Set ℝ) (bddA: BddAbove A) (neA: Set.Nonempty A) (posA: ∀a ∈ A, a ≥ 0)
  (B: Set ℝ) (bddB: BddAbove B) (neB: Set.Nonempty B) (posB: ∀b ∈ B, b ≥ 0)
  : sSup (A * B) ≥ sSup A * sSup B := by
  have ⟨ha, hap⟩ := neA
  have ⟨hb, hbp⟩ := neB
  have supA_nonneg : 0 ≤ sSup A := le_csSup_of_le bddA hap (posA ha hap).ge.le
  have supB_nonneg : 0 ≤ sSup B := le_csSup_of_le bddB hbp (posB hb hbp).ge.le
  have : 0 ≤ (sSup A)⁻¹ := by simp_all
  have : 0 ≤ (sSup B)⁻¹ := by simp_all
  have bddAB : BddAbove (A * B) := by
    simp_all [bddAbove_def];
    have ⟨bddAx, bddAp⟩ := bddA
    have ⟨bddBx, bddBp⟩ := bddB
    existsi (bddAx * bddBx); intro ab abAB;
    have ⟨a, aA, b, bB, ab_def⟩: ∃a ∈ A, ∃b ∈ B, a * b = ab := by simp_all [Set.mem_mul]
    have a0 : 0 ≤ a := by simp_all [le_of_lt]
    have : 0 ≤ b := by simp_all [le_of_lt]
    have bddAp := bddAp a aA
    have := bddBp b bB
    rw [← ab_def]; apply mul_le_mul; simp_all; simp_all; simp_all; exact le_trans a0 bddAp
  have habp : ha*hb ∈ A*B := by simp_all [Set.mul_mem_mul]
  have posab : ha*hb ≥ 0 := (mul_nonneg (posA ha hap).ge.le (posB hb hbp).ge.le).ge
  have supAB_nonneg : 0 ≤ sSup (A*B) := le_csSup_of_le bddAB habp posab.ge.le
  simp_all
  by_contra h
  simp_all
  let ε := sSup A * sSup B - sSup (A * B)
  have ε_def : ε = sSup A * sSup B - sSup (A * B) := by rfl
  have : ε > 0 := by aesop
  -- have ⟨ε, hε1, hε2, hε3⟩ : ∃ε, sSup A * sSup B - c = ε ∧ ε > 0 ∧ sSup A * sSup B ≥ ε := by aesop
  by_cases hb0: sSup B = 0
  . have : sSup B ≤ 0 := by aesop
    have : ∀b ∈ B, b ≤ 0 := (csSup_le_iff bddB neB).mp this
    have : ∀b ∈ B, b = 0 := by intro b bB; exact (LE.le.ge_iff_eq (this b bB)).mp (posB b bB)
    have : B = {0} := by ext; simp_all; apply Iff.intro; intro h; apply this; assumption; intro h; rw [h]; rwa [this hb] at hbp; assumption
    have : A * B = {0} := by ext; simp_all;
    have : sSup (A * B) = 0 := by aesop
    have : sSup A * sSup B = 0 := by aesop
    simp_all
  by_cases ha0: sSup A = 0
  . have : sSup A ≤ 0 := by aesop
    have : ∀a ∈ A, a ≤ 0 := (csSup_le_iff bddA neA).mp this
    have : ∀a ∈ A, a = 0 := by intro a aA; exact (LE.le.ge_iff_eq (this a aA)).mp (posA a aA)
    have : A = {0} := by ext; simp_all; apply Iff.intro; intro h; apply this; assumption; intro h; rw [h]; rwa [this ha] at hap; assumption
    have : A * B = {0} := by ext; simp_all;
    have : sSup (A * B) = 0 := by aesop
    have : sSup A * sSup B = 0 := by aesop
    simp_all
  . let ε₀ := ε * (2 * sSup B)⁻¹
    have ε₀_def : ε₀ = ε * (2 * sSup B)⁻¹ := by rfl
    let ε₁ := ε * (2 * sSup A)⁻¹
    have ε₁_def : ε₁ = ε * (2 * sSup A)⁻¹ := by rfl
    have e00 : ε₀ > 0 := by simp_all; exact lt_of_le_of_ne supB_nonneg (Ne.intro hb0).symm
    have e10 : ε₁ > 0 := by simp_all; exact lt_of_le_of_ne supA_nonneg (Ne.intro ha0).symm
    have : ε₀ * ε₁ > 0 := (Real.mul_pos e00.lt e10.lt).gt
    have : sSup A - ε₀ < sSup A := by aesop
    have : sSup B - ε₁ < sSup B := by aesop
    have εAB : ε ≤ sSup A * sSup B := by aesop
    have : (2: ℝ)⁻¹ ≤ 1 := by norm_num
    have : ε * 2⁻¹ ≤ ε := by aesop
    have : ε * 2⁻¹ ≤ sSup A * sSup B := le_trans this εAB
    have : ε * (2 * sSup B)⁻¹ * sSup B ≤ sSup A * sSup B := by (conv_lhs => rw [mul_inv, mul_assoc, inv_mul_cancel_right₀ (Ne.intro hb0)]); assumption
    have : ε * (2 * sSup A)⁻¹ * sSup A ≤ sSup B * sSup A := by (conv_lhs => rw [mul_inv, mul_assoc, inv_mul_cancel_right₀ (Ne.intro ha0)]); (conv_rhs => rw [mul_comm]); assumption
    have : ε₀ * sSup B ≤ sSup A * sSup B := by aesop
    have : ε₀ ≤ sSup A := by aesop
    have posAe : 0 ≤ sSup A - ε₀ := by aesop
    have posBe : 0 ≤ sSup B - ε₁ := by aesop

    have : ¬ sSup A ≤ sSup A - ε₀ := by simp_all
    have := (csSup_le_iff bddA neA).not.mp this
    have ⟨a, ha1, ha2⟩ : ∃a ∈ A, sSup A - ε₀ < a := by aesop
    have : ¬ sSup B ≤ sSup B - ε₁ := by simp_all
    have := (csSup_le_iff bddB neB).not.mp this
    have ⟨b, hb1, hb2⟩ : ∃b ∈ B, sSup B - ε₁ < b := by aesop
    have t1 : sSup A * ε₁ = ε * 2⁻¹ := by (conv_lhs => rw [mul_comm, ε₁_def, mul_inv, mul_assoc, inv_mul_cancel_right₀ (Ne.intro ha0)])
    have t2 : ε₀ * sSup B = ε * 2⁻¹ := by (conv_lhs => rw [ε₀_def, mul_inv, mul_assoc, inv_mul_cancel_right₀ (Ne.intro hb0)])
    have : 0 < a := LE.le.trans_lt posAe ha2
    have : a * b > sSup (A * B) := calc
      a * b > (sSup A - ε₀) * (sSup B - ε₁) := (mul_lt_mul' ha2.le hb2 posBe this).gt
      _ = (sSup A - ε₀) * sSup B - (sSup A - ε₀) * ε₁ := by simp [mul_sub_left_distrib]
      _ = (sSup A * sSup B - ε₀ * sSup B) - (sSup A * ε₁ - ε₀ * ε₁) := by simp [mul_sub_right_distrib]
      _ = (sSup A * sSup B - ε * 2⁻¹) - (ε * 2⁻¹ - ε₀ * ε₁) := by rw [t1, t2]
      _ = sSup A * sSup B - ε + ε₀ * ε₁ := by ring_nf
      _ > sSup A * sSup B - ε := by simp_all
      _ = sSup (A * B) := by rw [ε_def]; ring_nf
    have : a * b ≤ sSup (A * B) := by apply le_csSup; simp_all; exact Set.mul_mem_mul ha1 hb1
    rw [← not_lt] at this; simp_all

lemma sSup_mul'
  (A: Set ℝ) (bddA: BddAbove A) (neA: Set.Nonempty A) (posA: ∀a ∈ A, a ≥ 0)
  (B: Set ℝ) (bddB: BddAbove B) (neB: Set.Nonempty B) (posB: ∀b ∈ B, b ≥ 0)
  : sSup (A * B) = sSup A * sSup B := le_antisymm (sSup_mul_le A bddA neA posA B bddB neB posB) (GE.ge.le (sSup_mul_ge A bddA neA posA B bddB neB posB))

@[simp]
theorem sSup_mul'' [CompleteLattice α]
  (X: Set α) (neX: Set.Nonempty X)
  (cX: IsChain (· < ·) X) (f: α -> ℝ) (mf: Monotone f) (g: α -> ℝ) (mg: Monotone g)
  (posf: ∀x ∈ X, (f x) ≥ 0) (posg: ∀x ∈ X, (g x) ≥ 0)
  : sSup ((f * g) '' X) = sSup (f '' X) * sSup (g '' X) := by
  rw [← sSup_mul']; apply sSup_pointwise;
  . aesop
  . aesop
  . aesop
  . intro a _ b bX c cX d _ ac bd; exact mul_le_mul ac bd (posg b bX) (posf c cX)
  . simp_all [Monotone.map_bddAbove]
  . aesop
  . aesop
  . simp_all [Monotone.map_bddAbove]
  . aesop
  . aesop

end Real
