import Dice.Semantics
import Data.HList
import Data.KFinset
open Ty Value AExpr Expr Program
open Std

------------------
-- OTHER MACROS --
------------------
syntax "prob " term : term
syntax "prob 0" : term
macro_rules
| `(prob 1) => `((1: Probability))
| `(prob $t) => `(Probability.fromRealPos (($t): ℚ) (by norm_num))
| `(prob 0) => `((0: Probability))

------------
-- SYNTAX --
------------

-- Indices
declare_syntax_cat index
syntax "Z" : index
syntax "S" index : index
syntax " ⟪ " index " ⟫ᵢ " : term
macro_rules
  | `(⟪ Z ⟫ᵢ)           => `(Member.head)
  | `(⟪ S $i:index ⟫ᵢ)  => `(Member.tail (⟪ $i ⟫ᵢ))

-- Values
declare_syntax_cat value
syntax " true " : value
syntax " false " : value
syntax " ( " value " ) " : value
syntax " ( " value " , " value " )" : value
syntax " ⟪ " value " ⟫ᵥ " : term
macro_rules
  | `(⟪ true ⟫ᵥ)                    => `(VTrue)
  | `(⟪ false ⟫ᵥ)                   => `(VFalse)
  | `(⟪ ($v1:value, $v2:value) ⟫ᵥ)  => `(VPair ⟪ $v1 ⟫ᵥ ⟪ $v2 ⟫ᵥ)
  | `(⟪ ($v:value) ⟫ᵥ)              => `(⟪ $v:value ⟫ᵥ)

-- Atomic expressions
declare_syntax_cat aexpr
syntax index : aexpr
syntax value : aexpr
syntax " ( " aexpr " ) " : aexpr
syntax " ⟪ " aexpr " ⟫ₐ " : term
macro_rules
  | `(⟪ $v:value ⟫ₐ)      => `(AValue ⟪ $v ⟫ᵥ)
  | `(⟪ $i:index ⟫ₐ)      => `(AVar ⟪ $i ⟫ᵢ)
  | `(⟪ ( $a:aexpr ) ⟫ₐ)  => `(⟪ $a ⟫ₐ)
declare_syntax_cat aexprs

syntax  aexpr : aexprs
syntax  aexpr ", " aexprs : aexprs
syntax " ⟪ " aexprs " ⟫ₐₛ " : term
macro_rules
  | `(⟪ $a:aexpr ⟫ₐₛ)  => `(HList.cons ⟪ $a ⟫ₐ HList.nil )
  | `(⟪ $a:aexpr ,  $as:aexprs ⟫ₐₛ)  => `(HList.cons ⟪ $a ⟫ₐ ⟪ $as ⟫ₐₛ)

-- Expressions
declare_syntax_cat expr
syntax value : expr
syntax aexpr : expr
syntax " fst " aexpr : expr
syntax " snd " aexpr : expr
syntax " ( " aexpr " , " aexpr " )" : expr
syntax " let " expr " in " expr : expr
syntax " flip " scientific : expr
syntax " if " aexpr " then " expr " else " expr : expr
syntax " observe " aexpr : expr
syntax " [ " index " ](" ")" : expr
syntax " [ " index " ]( " aexprs " )" : expr
syntax " ( "  expr " ) " : expr
syntax " ⟪ "  expr " ⟫ₑ " : term
macro_rules
  | `(⟪ fst $a:aexpr ⟫ₑ)              => `(Fst ⟪ $a ⟫ₐ)
  | `(⟪ snd $a:aexpr ⟫ₑ)              => `(Snd ⟪ $a ⟫ₐ)
  | `(⟪ ($a1:aexpr, $a2:aexpr) ⟫ₑ)    => `(Pair ⟪ $a1 ⟫ₐ ⟪ $a2 ⟫ₐ)
  | `(⟪ let $e1:expr in $e2:expr ⟫ₑ)  => `(Let ⟪ $e1 ⟫ₑ ⟪ $e2 ⟫ₑ)
  | `(⟪ flip $n:scientific ⟫ₑ)        => `(Flip (FlipProb.fromRat $n (by norm_num)))
  | `(⟪ if $a:aexpr then $e1:expr else $e2:expr ⟫ₑ) => `(Ifte ⟪ $a ⟫ₐ ⟪ $e1 ⟫ₑ ⟪ $e2 ⟫ₑ)
  | `(⟪ observe $a:aexpr ⟫ₑ)          => `(Observe ⟪ $a ⟫ₐ)
  | `(⟪ [ $i:index ]( ) ⟫ₑ)           => `(Call ⟪ $i ⟫ᵢ [])
  | `(⟪ [ $i:index ]( $as:aexprs ) ⟫ₑ)=> `(Call ⟪ $i ⟫ᵢ ⟪ $as ⟫ₐₛ)
  | `(⟪ $v:value ⟫ₑ)                  => `(Atomic (AValue ⟪ $v ⟫ᵥ))
  | `(⟪ $a:aexpr ⟫ₑ)                  => `(Atomic ⟪ $a ⟫ₐ)
  | `(⟪ ( $e:expr ) ⟫ₑ)               => `(⟪ $e ⟫ₑ)

-- Syntactic sugar
syntax " ! " aexpr : expr
syntax aexpr " || " aexpr : expr
syntax aexpr " && " aexpr : expr
macro_rules
  | `(⟪ ! $a:aexpr ⟫ₑ) => `(Ifte ⟪ $a ⟫ₐ ⟪ false ⟫ₑ ⟪ true ⟫ₑ)
  | `(⟪ $a1:aexpr || $a2:aexpr ⟫ₑ) => `(Ifte ⟪ $a1 ⟫ₐ ⟪ true ⟫ₑ (Atomic ⟪ $a2 ⟫ₐ))
  | `(⟪ $a1:aexpr && $a2:aexpr ⟫ₑ) => `(Ifte ⟪ $a1 ⟫ₐ (Atomic ⟪ $a2 ⟫ₐ) ⟪ false ⟫ₑ)

-- Function
declare_syntax_cat funct
syntax " fun " " (Bool): " " Bool " " { " expr " } ": funct
syntax " ⟪ "  funct " ⟫f " : term
macro_rules
  | `(⟪ fun (Bool): Bool { $e:expr }⟫f) => `((⟪ $e ⟫ₑ : Func _ [TBool] TBool))

-- Program
declare_syntax_cat prog
syntax expr : prog
syntax funct prog : prog
syntax " ⟪ "  prog " ⟫ₚ " : term
macro_rules
  | `(⟪ $f:funct $p:prog ⟫ₚ) => `(PFunc ⟪ $f ⟫f ⟪ $p ⟫ₚ)
  | `(⟪ $e:expr ⟫ₚ) => `(PExpr ⟪ $e ⟫ₑ)

--------------
-- EXAMPLES --
--------------

open Classical

def diceExample1: Program 𝔹 [] [] := ⟪
  let (flip 0.3) in
  let (flip 0.8) in
  let (S Z || Z) in
  let (observe Z) in
  S S S Z⟫ₚ
-- #eval (toFinset <| normProb <| semProgramC' .nil <| diceExample1)

def diceExample3: Program (𝔹 :×: 𝔹) [] [([𝔹], 𝔹)] := ⟪
  fun (Bool): Bool {
    let (!Z) in
    let (flip 0.5) in
    if Z then S Z else S S Z
  }
  let [Z](true) in
  let [Z](false) in
  (Z, S Z)
⟫ₚ
def I3: Table [([𝔹], 𝔹)] := (fun _ _ => prob 1/2)::[]
-- #eval (toFinset <| normProb <| semProgramC' I3 <| diceExample3)
def test: Expr (.cons (.cons 𝔹 .nil, 𝔹) .nil) [𝔹] 𝔹 := ⟪
  let (!Z) in
  let (flip 0.5) in
  if Z then S Z else S S Z⟫ₑ  

def diceExample4: Program 𝔹 [] [([𝔹], 𝔹)] := ⟪
  fun (Bool): Bool {
    if Z then Z
    else (
      let (flip 0.5) in
      [Z](Z)
    )
  }
  let (flip 0.5) in
  [Z](Z)⟫ₚ
def I4: Table [([𝔹], 𝔹)] := (fun
  | _, VTrue  => 1
  | _, VFalse => 0)::[]
-- #eval (toFinset <| normProb <| semProgramC' I4 <| diceExample4)

def diceExample5: Program 𝔹 [] [([𝔹], 𝔹)] := ⟪
  fun (Bool): Bool {
    let (flip 0.5) in
    if Z then S Z
    else (
      let (flip 0.5) in
      let (S S Z || Z) in
      [Z](Z)
    )
  }
  [Z](false)⟫ₚ
def I5: Table [([𝔹], 𝔹)] := (fun
  | VTrue::[],  VTrue  => prob 1
  | VTrue::[],  VFalse => prob 0
  | VFalse::[], VTrue  => prob 1/3
  | VFalse::[], VFalse => prob 2/3)::[]
-- #eval (toFinset <| normProb <| semProgramC' I5 <| diceExample5)

def diceExample6: Program 𝔹 [] [([𝔹], 𝔹)] := ⟪
  fun (Bool): Bool {
    let (flip 0.5) in
    let (observe Z) in
    if S Z then [Z](false) else false
  }
  [Z](false)⟫ₚ
def I6: Table [([𝔹], 𝔹)] := (fun
  | VTrue::[],  VTrue  => prob 0
  | VTrue::[],  VFalse => prob 0
  | VFalse::[], VTrue  => prob 0
  | VFalse::[], VFalse => prob 0)::[]
