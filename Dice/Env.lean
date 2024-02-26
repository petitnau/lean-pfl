import Dice.Ast
import Data.HList

abbrev Env: Type :=
  List Ty

def Distribution (τ: Ty): Type :=
  Value τ -> Rat

abbrev Table (T: List (List Ty × Ty)) : Type :=
  HList (λ(π,τ) => HList Value π -> Distribution τ) T
