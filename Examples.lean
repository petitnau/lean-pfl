import Dice.Semantics
open Ty Value AExpr Expr Program

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
syntax " [ " index " ]( " aexpr " )" : expr
syntax " ( "  expr " ) " : expr
syntax " ⟪ "  expr " ⟫ₑ " : term
macro_rules
  | `(⟪ fst $a:aexpr ⟫ₑ)              => `(Fst ⟪ $a ⟫ₐ)
  | `(⟪ snd $a:aexpr ⟫ₑ)              => `(Snd ⟪ $a ⟫ₐ)
  | `(⟪ ($a1:aexpr, $a2:aexpr) ⟫ₑ)    => `(Pair ⟪ $a1 ⟫ₐ ⟪ $a2 ⟫ₐ)
  | `(⟪ let $e1:expr in $e2:expr ⟫ₑ)  => `(Let ⟪ $e1 ⟫ₑ ⟪ $e2 ⟫ₑ)
  | `(⟪ flip $n:scientific ⟫ₑ)        => `(Flip $n)
  | `(⟪ if $a:aexpr then $e1:expr else $e2:expr ⟫ₑ) => `(Ifte ⟪ $a ⟫ₐ ⟪ $e1 ⟫ₑ ⟪ $e2 ⟫ₑ)
  | `(⟪ observe $a:aexpr ⟫ₑ)          => `(Observe ⟪ $a ⟫ₐ)
  | `(⟪ [ $i:index ]( $a:aexpr ) ⟫ₑ)  => `(Call ⟪ $i ⟫ᵢ (HList.cons ⟪ $a ⟫ₐ HList.nil))
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
  | `(⟪ fun (Bool): Bool { $e:expr }⟫f) => `((⟪ $e ⟫ₑ : Function _ [TBool] TBool))

-- Program
declare_syntax_cat prog
syntax expr : prog
syntax funct prog : prog
syntax " ⟪ "  prog " ⟫ₚ " : term
macro_rules
  | `(⟪ $f:funct $p:prog ⟫ₚ) => `(Func ⟪ $f ⟫f ⟪ $p ⟫ₚ)
  | `(⟪ $e:expr ⟫ₚ) => `(Expression ⟪ $e ⟫ₑ)

--------------
-- EXAMPLES --
--------------

def diceExample1': Program [] [] TBool := ⟪
  let (flip 0.3) in
  let (flip 0.8) in
  let (S Z || Z) in
  let (observe Z) in
  S S S Z⟫ₚ
#eval (toFinset <| normalize <| semProgram' .nil <| diceExample1') == {(VTrue, 15/43), (VFalse, 28/43)}

def diceExample2: Program [] [] TBool := ⟪
  let (flip 0.3) in
  let (flip 0.8) in
  let (Z, false) in
  let (S S Z, Z) in
  let (snd Z) in
  (fst Z)⟫ₚ
#eval (toFinset <| normalize <| semProgram' .nil <| diceExample2) == {(VTrue, 8/10), (VFalse, 2/10)}

def diceExample3: Program [] [([TBool], TBool)] (TBool :×: TBool) := ⟪
  fun (Bool): Bool {
    let (!Z) in
    let (flip 0.5) in
    if Z then S Z else S S Z
  }
  let [Z](true) in
  let [Z](false) in
  (Z, S Z)
  ⟫ₚ
#eval (toFinset <| normalize <| semProgram' (HList.cons (fun _ _ => 0) HList.nil) <| diceExample3)

def diceExample4: Program [] [([TBool], TBool)] TBool := ⟪
  fun (Bool): Bool {
    if Z then Z
    else (
      let (flip 0.5) in
      [Z](Z)
    )
  }
  let (flip 0.5) in
  [Z](Z)⟫ₚ
def I4: Table [([TBool], TBool)] := HList.cons (fun _ v => match v with | VTrue => 1 | VFalse => 0) HList.nil
#eval (toFinset <| normalize <| semProgram' I4 <| diceExample4)

def diceExample5: Program [] [([TBool], TBool)] TBool := ⟪
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
def I5: Table [([TBool], TBool)] := HList.cons (fun xs v =>
  let (HList.cons x HList.nil) := xs
  match x, v with
  | VTrue, VTrue => 1
  | VTrue, VFalse => 0
  | VFalse, VTrue => 1/3
  | VFalse, VFalse => 2/3) HList.nil
#eval (toFinset <| normalize <| semProgram' I5 <| diceExample5)
