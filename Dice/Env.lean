import Dice.Ast

def Env: Type := List Ty
def Distribution (τ: Ty): Type := Value τ -> Rat
