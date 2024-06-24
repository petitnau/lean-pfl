import Dice.Ast
import Data.HList
import Data.PSemiDistribution
import Mathlib.Topology.UnitInterval
import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLatticeIntervals
import Data.Probability
import Aesop
open BigOperators

set_option maxHeartbeats 2000000

abbrev Table (ρ: List (List Ty × Ty)) : Type :=
  HList (λ(π,τ) => 𝔻[π](τ)) ρ

namespace Table

theorem eq_ext : ∀(a b: Table ((π,τ)::Γ)), a = b ↔ HList.head a = HList.head b ∧ HList.tail a = HList.tail b := by
  intro a b; cases a ; cases b ; simp_all

abbrev cons {γ: Sig} {Γ: [Sig]'} (I: 𝔻[γ.1](γ.2)) (T: Table Γ): Table (γ::Γ) :=
  @HList.cons Sig (λ(π,τ) => HList Value π -> 𝔻(τ)) γ Γ I T

--------------------------
-- SIMPLE DISTRIBUTIONS --
--------------------------

def zero : Table Γ :=
  match Γ with
  | [] => []
  | _::_ => 0 ::ₕ zero
instance instZero : Zero (Table Γ) := ⟨zero⟩

@[simp]
theorem zero_nil_ext : (0 : Table []) = []ₕ := by aesop
@[simp]
theorem head_zero : HList.head (0 : Table ((π,τ)::Γ)) = 0 := by aesop
@[simp]
theorem tail_zero : HList.tail (0 : Table ((π,τ)::Γ)) = 0 := by aesop

def one : Table Γ :=
  match Γ with
  | [] => []
  | _::_ => 1 ::ₕ one
instance instOne : One (Table Γ) := ⟨one⟩

@[simp]
theorem one_nil_ext : (1 : Table []) = []ₕ := by aesop
@[simp]
theorem head_one : HList.head (1 : Table ((π,τ)::Γ)) = 1 := by aesop
@[simp]
theorem tail_one : HList.tail (1 : Table ((π,τ)::Γ)) = 1 := by aesop

------------------
-- INEQUALITIES --
------------------

def le : Table Γ -> Table Γ -> Prop
  | HList.nil,       HList.nil       => True
  | HList.cons x xs, HList.cons y ys => x ≤ y ∧ le xs ys
instance instLE : LE (Table Γ) := ⟨le⟩


@[simp]
def le_ext : le (a: Table Γ) b ↔ a ≤ b := by rfl
@[simp]
def le_nil_ext (a : Table []) : a ≤ []ₕ := by cases a; unfold_projs; unfold le; trivial
@[simp]
def le_cons_ext (a b: 𝔻[π](τ)) (as bs: Table Γ)
  : (@HList.cons _ _ (π,τ) Γ a as) ≤ (@HList.cons _ _ (π,τ) Γ b bs) ↔ a ≤ b ∧ as ≤ bs := by
    apply Iff.intro <;> (intro h; assumption)

instance instLT : LT (Table Γ) := ⟨fun a b => a ≤ b ∧ a ≠ b⟩

@[simp]
def lt_ext : (a : Table Γ) < b ↔ a ≤ b ∧ a ≠ b := by rfl

@[simp]
theorem zero_le : ∀(a: Table Γ), 0 ≤ a := by
  intro a; induction a with
  | nil => simp
  | cons a as ih => unfold_projs; unfold zero le; aesop

@[simp]
theorem le_one : ∀(a: Table Γ), a ≤ 1 := by
  intro a; induction a with
  | nil => simp
  | cons a as ih => unfold_projs; unfold one le; aesop

-------------
-- SUP INF --
-------------

noncomputable def sup : Table Γ -> Table Γ -> Table Γ
  | HList.nil,       HList.nil       => HList.nil
  | HList.cons x xs, HList.cons y ys => HList.cons (x ⊔ y) (sup xs ys)
noncomputable instance instSup: Sup (Table Γ) := ⟨sup⟩

@[simp]
theorem sup_nil_ext (a b: Table []) : a ⊔ b = []ₕ := by cases a; cases b; rfl
@[simp]
theorem sup_cons_ext (a b: 𝔻[π](τ)) (as bs: Table Γ)
  : (@HList.cons _ _ (π,τ) Γ a as) ⊔ (@HList.cons _ _ (π,τ) Γ b bs) = (@HList.cons _ _ (π,τ) Γ (a ⊔ b) (as ⊔ bs))
  := by rfl

noncomputable def inf : Table Γ -> Table Γ -> Table Γ
  | HList.nil,       HList.nil       => HList.nil
  | HList.cons x xs, HList.cons y ys => HList.cons (x ⊓ y) (inf xs ys)
noncomputable instance instInf: Inf (Table Γ) := ⟨inf⟩
@[simp]
theorem inf_nil_ext (a b: Table []) : a ⊓ b = []ₕ := by cases a; cases b; rfl
@[simp]
theorem inf_cons_ext (a b: 𝔻[π](τ)) (as bs: Table Γ)
  : (@HList.cons _ _ (π,τ) Γ a as) ⊓ (@HList.cons _ _ (π,τ) Γ b bs) = (@HList.cons _ _ (π,τ) Γ (a ⊓ b) (as ⊓ bs))
  := by rfl

noncomputable def sSup' : Set (Table Γ) -> Table Γ := λT =>
  match Γ with
  | [] => []ₕ
  | _::_ => (sSup {HList.head t | t ∈ T}) ::ₕ (sSup' {HList.tail t | t ∈ T})
noncomputable instance instSupSet : SupSet (Table Γ) := ⟨sSup'⟩

@[simp]
theorem sSup_nil_ext (s : Set (Table [])) : sSup s = []ₕ := by rfl
@[simp]
theorem sSup_cons_ext (s: Set (Table ((π,τ)::Γ)))
  : sSup s = @HList.cons _ _ (π,τ) Γ (sSup {HList.head t | t ∈ s}) (sSup {HList.tail t | t ∈ s})
  := by rfl

noncomputable def sInf' : Set (Table Γ) -> Table Γ := λT =>
  match Γ with
  | [] => []ₕ
  | _::_ => (sInf {HList.head t | t ∈ T}) ::ₕ (sInf' {HList.tail t | t ∈ T})
noncomputable instance instInfSet : InfSet (Table Γ) := ⟨sInf'⟩

@[simp]
theorem sInf_nil_ext (s : Set (Table [])) : sInf s = []ₕ := by rfl
@[simp]
theorem sInf_cons_ext (s: Set (Table ((π,τ)::Γ)))
  : sInf s = @HList.cons _ _ (π,τ) Γ (sInf {HList.head t | t ∈ s}) (sInf {HList.tail t | t ∈ s})
  := by rfl

instance instBot : Bot (Table Γ) := ⟨0⟩
instance instTop : Top (Table Γ) := ⟨1⟩

lemma sSup_apply (T: Set (Table Γ)) (h: Set.Nonempty T) : sSup {HList.get t i | t ∈ T} = HList.get (sSup T) i  := by
  induction i with
  | head =>
      rw [sSup_cons_ext]; conv => lhs; enter[1,x]; congr; ext; congr; ext; rw [HList.get_head_head]
      rfl
  | tail a ih =>
      have ⟨x, xh⟩ := h
      rw [sSup_cons_ext]; simp;
      have ih := ih {HList.tail x | x ∈ T} (by existsi (HList.tail x); aesop)
      simp_all; conv => lhs; enter[1,x]; congr; ext; congr; ext; rw [HList.get_tail_tail]
      aesop

lemma sInf_apply (T: Set (Table Γ)) (h: Set.Nonempty T) : sInf {HList.get t i | t ∈ T} = HList.get (sInf T) i  := by
  induction i with
  | head =>
      rw [sInf_cons_ext]; conv => lhs; enter[1,x]; congr; ext; congr; ext; rw [HList.get_head_head]
      rfl
  | tail a ih =>
      have ⟨x, xh⟩ := h
      rw [sInf_cons_ext]; simp;
      have ih := ih {HList.tail x | x ∈ T} (by existsi (HList.tail x); aesop)
      simp_all; conv => lhs; enter[1,x]; congr; ext; congr; ext; rw [HList.get_tail_tail]
      aesop

---------------
-- INSTANCES --
---------------
theorem le_antisymm' : ∀ (a b : Table Γ), a ≤ b → b ≤ a → a = b := by
    intro a b ab ba; induction a with
    | nil => cases b; simp
    | cons a as ih =>
        cases b; rw [eq_ext]; rw [le_cons_ext] at ab ba;
        simp_all; constructor
        . exact le_antisymm ab.left ba.left
        . exact ih _ ab.right ba.right

instance instPartialOrder: PartialOrder (Table Γ) :=
  { le_refl := by
      intro a; induction a with
      | nil => simp
      | cons a as ih => rw [le_cons_ext]; simp_all
  , le_trans := by
      intro a b c; induction a with
      | nil => cases b; cases c; simp
      | cons a as ih =>
          cases b; cases c
          rw [le_cons_ext, le_cons_ext, le_cons_ext]
          intro h1 h2; constructor;
          exact le_trans h1.left h2.left
          exact ih _ _ h1.right h2.right
  , lt_iff_le_not_le := by
      intro a b; apply Iff.intro
      . intro h; rw [lt_ext] at h; simp_all; intro h1;
        exact h.right (le_antisymm' a b h.left h1)
      . intro h; rw [lt_ext]; simp_all; intro h1; rw [h1] at h;
        simp_all
  , le_antisymm := le_antisymm'
  }

noncomputable instance instCompleteLattice : CompleteLattice (Table Γ) :=
  { le_sup_left := by
      intro a b; induction a with
      | nil => simp
      | cons a as ih => cases b; aesop
  , le_sup_right := by
      intro a b; induction a with
      | nil => simp
      | cons a as ih => cases b; aesop
  , sup_le := by
      intro a b c h1 h2; induction a with
      | nil => cases b; cases c; simp
      | cons a as ih => cases b; cases c; aesop
  , inf_le_left := by
      intro a b; induction a with
      | nil => cases b; simp
      | cons a as ih => cases b; aesop
  , inf_le_right := by
      intro a b; induction a with
      | nil => cases b; simp
      | cons a as ih => cases b; aesop
  , le_inf := by
      intro a b c h1 h2; induction a with
      | nil => cases b; cases c; simp
      | cons a as ih => cases b; cases c; aesop
  , le_sSup := by
      intro s a h; induction a with
      | nil => simp
      | cons a as ih =>
          rw [sSup_cons_ext, le_cons_ext]; constructor
          . apply le_sSup; aesop
          . apply ih; simp_all only [Set.mem_setOf_eq];
            existsi (a :: as); simp_all
  , sSup_le := by
      intro s a h; induction a with
      | nil => simp
      | cons a as ih =>
          rw [sSup_cons_ext, le_cons_ext]; constructor
          . apply sSup_le; intro b bB;
            have ⟨w, wh1, wh2⟩ : ∃w ∈ s, b = HList.head w := by aesop
            have := h w wh1;
            cases w; rw [le_cons_ext] at this; aesop
          . apply ih {x | ∃ t ∈ s, HList.tail t = x}; intro b bB
            have ⟨w, wh1, wh2⟩ : ∃w ∈ s, b = HList.tail w := by aesop
            have := h w wh1;
            cases w; rw [le_cons_ext] at this; aesop
  , sInf_le := by
      intro s a h; induction a with
      | nil => simp
      | cons a as ih =>
          rw [sInf_cons_ext, le_cons_ext]; constructor
          . apply sInf_le; aesop
          . apply ih; simp_all only [Set.mem_setOf_eq];
            existsi (a :: as); simp_all
  , le_sInf := by
      intro s a h; induction a with
      | nil => simp
      | cons a as ih =>
          rw [sInf_cons_ext, le_cons_ext]; constructor
          . apply le_sInf; intro b bB;
            have ⟨w, wh1, wh2⟩ : ∃w ∈ s, b = HList.head w := by aesop
            have := h w wh1;
            cases w; rw [le_cons_ext] at this; aesop
          . apply ih {x | ∃ t ∈ s, HList.tail t = x}; intro b bB
            have ⟨w, wh1, wh2⟩ : ∃w ∈ s, b = HList.tail w := by aesop
            have := h w wh1;
            cases w; rw [le_cons_ext] at this; aesop
  , le_top := le_one
  , bot_le := zero_le }

end Table
