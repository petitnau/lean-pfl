import Mathlib.Data.Set.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

theorem Nat.le_of_lt_add_one {a : ℕ} {b : ℕ} (H : a < b + 1) : a ≤ b := by induction a <;> aesop

theorem Monotone.f_step [Preorder α] {f: α →o α} : x ≤ f x -> f^[n] x ≤ f^[n+1] x := by
  intro hxfx
  induction n with
  | zero => simp_all
  | succ n ih => simp_all [Function.iterate_succ_apply']; exact f.monotone' ih

theorem Monotone.f_le [Preorder α] {f: α →o α} : x ≤ f x → m ≤ n -> f^[m] x ≤ f^[n] x := by
  intro hxfx
  induction n with
  | zero => intro hmn; simp_all
  | succ n ih =>
    intro hmn;
    have : m ≤ n ∨ m = n+1 := by cases hmn.lt_or_eq <;> simp_all [Nat.le_of_lt_add_one]
    cases this with
    | inl h =>
      simp_all; calc
          (⇑f)^[m] x ≤ (⇑f)^[n] x := by assumption
          (⇑f)^[n] x ≤ (⇑f)^[n+1] x := Monotone.f_step hxfx
    | inr => simp_all

theorem Monotone.f_step' [Preorder α] {f: α →o α} : f x ≤ x -> f^[n+1] x ≤ f^[n] x := by
  intro hxfx
  induction n with
  | zero => simp_all
  | succ n ih => simp_all [Function.iterate_succ_apply']; exact f.monotone' ih

theorem Monotone.f_le' [Preorder α] {f: α →o α} : f x ≤ x → m ≤ n -> f^[n] x ≤ f^[m] x := by
  intro hxfx
  induction n with
  | zero => intro hmn; simp_all
  | succ n ih =>
    intro hmn;
    have : m ≤ n ∨ m = n+1 := by cases hmn.lt_or_eq <;> simp_all [Nat.le_of_lt_add_one]
    cases this with
    | inl h =>
      simp_all; calc
          (⇑f)^[n+1] x ≤ (⇑f)^[n] x := Monotone.f_step' hxfx
          (⇑f)^[n] x ≤ (⇑f)^[m] x := by assumption
    | inr => simp_all

theorem Monotonee.chain [Preorder α] {f: α →o α} : f a ≤ a ∨ a ≤ f a → IsChain (· ≤ ·) {(f^[n] a) | n : ℕ} := by
  rintro h1 x ⟨xn,xh⟩ y ⟨yn,yh⟩; simp_all; intro _
  cases' h1 with h1 h1
  . by_cases h: xn ≤ yn
    . right; rw [← xh, ← yh]; exact Monotone.f_le' h1 h;
    . left; simp_all; rw [← xh, ← yh]; exact Monotone.f_le' h1 h.le;
  . by_cases h: xn ≤ yn
    . left; rw [← xh, ← yh]; exact Monotone.f_le h1 h;
    . right; simp_all; rw [← xh, ← yh]; exact Monotone.f_le h1 h.le;

theorem Monotonee.paral [CompleteLattice α] (f: α →o α) : a ≤ b → f^[n] a ≤ f^[n] b := by
  intro h;
  induction n
  simp_all; simp_all [Function.iterate_succ_apply'];
  apply f.monotone'; assumption

@[simp]
theorem Set.comprehension_nonempty {α: Type} [h: Nonempty α] (f: α -> β): {f x | x : α}.Nonempty := by
  have ⟨a⟩ := h; existsi (f a); existsi a; simp_all

def ScottContinuous' [Preorder α] [Preorder β] [SupSet α] [SupSet β]
  (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → IsChain (· ≤ ·) d → sSup (f '' d) = f (sSup d)

def CoScottContinuous' [Preorder α] [Preorder β] [InfSet α] [InfSet β]
  (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → IsChain (· ≤ ·) d → sInf (f '' d) = f (sInf d)

@[simp]
theorem set_nat_succ (f: ℕ -> β): {f (n+1) | n : ℕ} ∪ {f 0} = {f n | n : ℕ} := by
  ext x; apply Iff.intro;
  . intro h; simp_all; rcases h with h | ⟨n,hn⟩
    . existsi 0; simp_all
    . existsi n+1; simp_all
  . intro h; simp_all; rcases h with ⟨n,hn⟩; cases' n with n
    . left; simp_all
    . right; existsi n; simp_all

theorem lowerb [CompleteLattice α] (f: α →o α) (sc: ScottContinuous' f): sSup {f^[n] ⊥ | n : ℕ} = OrderHom.lfp f := by
  let X := sSup {f^[n] ⊥ | n : ℕ}
  have : {f^[n] ⊥ | n : ℕ}.Nonempty := by existsi ⊥; existsi 0; simp_all
  have := sc this (Monotonee.chain (Or.inr ((by simp): ⊥ ≤ f ⊥)))
  have : f X = X := calc
        f (sSup {f^[n] ⊥ | n : ℕ})
    _ = sSup {f (f^[n] ⊥) | n : ℕ} := by unfold Set.image at this; simp_all
    _ = sSup {f^[n+1] ⊥ | n : ℕ} := by simp_all [Function.iterate_succ_apply']
    _ = sSup ({f^[n+1] ⊥ | n : ℕ} ∪ {⊥}) := by simp_all
    _ = sSup ({f^[n+1] ⊥ | n : ℕ} ∪ {f^[0] ⊥}) := by simp_all
    _ = sSup {f^[n] ⊥ | n : ℕ} := by rw [set_nat_succ (f^[·] ⊥)]
  have : f.toFun.IsFixedPt X := by aesop
  have : ∀Y, f Y = Y → ∀n, f^[n] ⊥ ≤ Y := by
    intro Y h n;
    induction n with
    | zero => simp_all
    | succ n ih =>
      have : f ((⇑f)^[n] ⊥) ≤ f Y := f.mono ih
      simp_all [Function.iterate_succ_apply']
  have : IsLeast (f.toFun.fixedPoints) X := by unfold IsLeast; simp_all [mem_lowerBounds]; aesop
  have := OrderHom.isLeast_lfp f
  apply IsLeast.unique <;> aesop

theorem lowerb' [CompleteLattice α] (f: α →o α) (sc: ScottContinuous' f): f^[n] ⊥ ≤ OrderHom.lfp f := by
  rw [← lowerb]; apply le_sSup; aesop; simp_all

theorem upperb [CompleteLattice α] (f: α →o α) (sc: CoScottContinuous' f): sInf {f^[n] ⊤ | n : ℕ} = OrderHom.gfp f := by
  let X := sInf {f^[n] ⊤ | n : ℕ}
  have : {f^[n] ⊤ | n : ℕ}.Nonempty := by existsi ⊤; existsi 0; simp_all
  have := sc this (Monotonee.chain (Or.inl ((by simp): f ⊤ ≤ ⊤)))
  have : f X = X := calc
        f (sInf {f^[n] ⊤ | n : ℕ})
    _ = sInf {f (f^[n] ⊤) | n : ℕ} := by unfold Set.image at this; simp_all
    _ = sInf {f^[n+1] ⊤ | n : ℕ} := by simp_all [Function.iterate_succ_apply']
    _ = sInf ({f^[n+1] ⊤ | n : ℕ} ∪ {⊤}) := by simp_all
    _ = sInf ({f^[n+1] ⊤ | n : ℕ} ∪ {f^[0] ⊤}) := by simp_all
    _ = sInf {f^[n] ⊤ | n : ℕ} := by rw [set_nat_succ (f^[·] ⊤)]
  have : f.toFun.IsFixedPt X := by aesop
  have : ∀Y, f Y = Y → ∀n, Y ≤ f^[n] ⊤ := by
    intro Y h n;
    induction n with
    | zero => simp_all
    | succ n ih =>
      have : f Y ≤ f ((⇑f)^[n] ⊤) := f.mono ih
      simp_all [Function.iterate_succ_apply']
  have : IsGreatest (f.toFun.fixedPoints) X := by unfold IsGreatest; simp_all [mem_upperBounds]; aesop
  have := OrderHom.isGreatest_gfp f
  apply IsGreatest.unique <;> aesop

theorem upperb' [CompleteLattice α] (f: α →o α) (sc: CoScottContinuous' f): OrderHom.gfp f ≤ f^[n] ⊤:= by
  rw [← upperb]; apply sInf_le; aesop; simp_all

theorem sSup_apply' {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sSup s) a = sSup {f a | f ∈ s}  := by
      rw [sSup_apply]; unfold iSup Set.range; simp

theorem sInf_apply' {α : Type*} {β : α → Type*} [∀ i, InfSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sInf s) a = sInf {f a | f ∈ s}  := by
      rw [sInf_apply]; unfold iInf Set.range; simp
