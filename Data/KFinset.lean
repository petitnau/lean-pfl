import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Basic

structure KFinset (k: Type) (v: Type): Type where
  key: Finset k
  val: k -> v

unsafe instance reprKFinset [Repr (Finset (k × v))]: Repr (KFinset k v) :=
  ⟨fun (s : KFinset k v) (_ : ℕ) =>
    Std.Format.text "Distribution: ¬" ++ repr (Finset.map ⟨fun v => (v, s.val v), by intro _ _ _; simp_all⟩ s.key) ⟩
