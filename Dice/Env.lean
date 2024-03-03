import Dice.Ast
import Data.HList
import Mathlib.Topology.UnitInterval
import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLatticeIntervals
import Data.Prob
import Aesop
open BigOperators

def Distribution (τ: Ty): Type :=
  Value τ -> Probability

instance le {τ: Ty}: LE (Distribution τ) :=
  ⟨fun d1 d2 => ∀(v: Value τ), d1 v ≤ d2 v⟩

@[simp]
theorem le_ext : ∀(a b: Distribution τ), a ≤ b ↔ ∀v, a v ≤ b v := by
  intro a b; apply Iff.intro; all_goals (intro h; assumption)

instance lt {τ: Ty}: LT (Distribution τ) :=
  ⟨fun d1 d2 => d1 ≤ d2 ∧ ∃(v: Value τ), d1 v < d2 v⟩

@[simp]
theorem lt_ext : ∀(a b: Distribution τ), a < b ↔ a ≤ b ∧ ∃(v: Value τ), a v < b v := by
  intro a b; apply Iff.intro; all_goals (intro h; assumption)

instance preorder {τ: Ty}: Preorder (Distribution τ) :=
  ⟨ by
    simp [le]
  , by
    simp [le]
    intro a b c h1 h2 v;
    apply le_trans;
    exact h1 v
    exact h2 v
  , by
    simp [le]
  ⟩
open le


instance poset {τ: Ty}: PartialOrder (Distribution τ) :=
  ⟨ by
    intro d1 d2 h1 h2; funext v;
    unfold LE.le Preorder.toLE preorder le at h1 h2
    simp_all; exact (LE.le.le_iff_eq (h2 v)).mp (h1 v) ⟩

noncomputable instance sup {τ: Ty}: Sup (Distribution τ) :=
  ⟨ fun d1 d2 v => max (d1 v) (d2 v) ⟩

noncomputable instance inf {τ: Ty}: Inf (Distribution τ) :=
  ⟨ fun d1 d2 v => min (d1 v) (d2 v) ⟩

noncomputable instance semilatticesup {τ: Ty}: SemilatticeSup (Distribution τ) :=
  ⟨ by
    intro d1 d2 v;
    have : (d1 ⊔ d2) v = max (d1 v) (d2 v) := by rfl
    have : d1 v ≤ max (d1 v) (d2 v) := by simp
    aesop
  , by
    intro d1 d2 v
    have : (d1 ⊔ d2) v = max (d1 v) (d2 v) := by rfl
    have : d2 v ≤ max (d1 v) (d2 v) := by aesop
    aesop
  , by
    intro d1 d2 d3 h1 h2 v
    have : (d1 ⊔ d2) v = max (d1 v) (d2 v) := by rfl
    have : max (d1 v) (d2 v) ≤ d3 v := by simp [h1]; aesop
    aesop⟩

noncomputable instance semilatticeinf {τ: Ty}: SemilatticeInf (Distribution τ) :=
  ⟨ by
    intro d1 d2 v;
    have : (d1 ⊓ d2) v = min (d1 v) (d2 v) := by rfl
    have : min (d1 v) (d2 v) ≤ d1 v := by simp
    aesop
  , by
    intro d1 d2 v
    have : (d1 ⊓ d2) v = min (d1 v) (d2 v) := by rfl
    have : min (d1 v) (d2 v) ≤ d2 v := by aesop
    aesop
  , by
    intro d1 d2 d3 h1 h2 v
    have : (d2 ⊓ d3) v = min (d2 v) (d3 v) := by rfl
    have : d1 v ≤ min (d2 v) (d3 v) := by aesop
    aesop⟩

noncomputable instance supset {τ: Ty}: SupSet (Distribution τ) :=
  ⟨ fun s => fun v => sSup {d v | d ∈ s} ⟩
noncomputable instance infset {τ: Ty}: InfSet (Distribution τ) :=
  ⟨ fun s => fun v => sInf {d v | d ∈ s} ⟩

noncomputable instance lattice {τ: Ty}: Lattice (Distribution τ) :=
  { (inferInstance : SemilatticeInf (Distribution τ)),
    (inferInstance : SemilatticeSup (Distribution τ)) with }

noncomputable instance completelatticesup {τ: Ty}: CompleteSemilatticeSup (Distribution τ) :=
  ⟨ by
    intro s a H v
    let a' := a v
    let s' := {d v | d ∈ s}
    have : a' ∈ s' := by aesop
    simp [le_sSup this]; rw [←DReal.le_ext, ←Probability.le_ext]
    sorry
  , by
    intro s a H v
    let a' := a v
    let s' := {d v | d ∈ s}
    have H': ∀ b ∈ s, ∀ v', b v' ≤ a v' := by aesop
    have : ∀ b' ∈ s', b' ≤ a' := by
      intro b' H''
      have : a' = a v := by simp
      have ⟨b, H''', H''''⟩: ∃b ∈ s, b' = b v := by aesop
      simp [H'''', H' b H''' v]
      sorry
    sorry ⟩

noncomputable instance completelatticeinf {τ: Ty}: CompleteSemilatticeInf (Distribution τ) :=
  ⟨ by
    intro s a H v
    let a' := a v
    let s' := {d v | d ∈ s}
    have : a' ∈ s' := by aesop
    sorry
  , by
    intro s a H v
    let a' := a v
    let s' := {d v | d ∈ s}

    have H': ∀ b ∈ s, ∀ v', a v' ≤ b v' := by aesop
    have : ∀ b' ∈ s', a' ≤ b' := by
      intro b' H''
      have : a' = a v := by simp
      have ⟨b, H''', H''''⟩: ∃b ∈ s, b' = b v := by aesop
      simp [H'''', H' b H''' v]
      sorry
    sorry ⟩

instance top {τ: Ty}: Top (Distribution τ) :=
  ⟨ fun _ => 1 ⟩
instance bot {τ: Ty}: Bot (Distribution τ) :=
  ⟨ fun _ => 0 ⟩

noncomputable instance completelattice {τ: Ty}: CompleteLattice (Distribution τ) :=
  { semilatticesup, semilatticeinf, completelatticeinf, completelatticesup with
    le_top := sorry
  , bot_le := sorry }

abbrev Env: Type :=
  List Ty

abbrev Table (ρ: List (List Ty × Ty)) : Type :=
  HList (λ(π,τ) => HList Value π -> Distribution τ) ρ

def le_table : Table ρ -> Table ρ -> Prop
  | .nil, .nil => True
  | .cons x xs, .cons y ys => x ≤ y ∧ le_table xs ys
instance : LE (Table ρ) := ⟨ le_table ⟩

@[simp]
theorem le_table_refl : ∀ (a: Table ρ), a ≤ a := sorry

instance : Preorder (Table ρ) :=
  { le_trans := sorry
  , le_refl := le_table_refl
  }
