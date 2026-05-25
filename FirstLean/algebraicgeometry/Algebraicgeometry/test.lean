import Mathlib.Data.Real.Basic

namespace my_comp

structure Comp₀ where
  Re : ℝ
  Im : ℝ

def add (x y : Comp₀) : Comp₀ :=
  ⟨x.Re + y.Re, x.Im + y.Im⟩

def myComp₀ : Comp₀ :=
  ⟨1, 2⟩

def myComp₁ : Comp₀ :=
  ⟨2, 3⟩

protected theorem add_comm (x y : Comp₀) : add x y = add y x := by
  rw[add, add]
  simp
  constructor
  · apply add_comm
  · apply add_comm


example {A B : Set (ℝ)} : A ∩ B = B ∩ A := by
  ext x
  constructor
  · intro x
    rcases x with ⟨a, b⟩
    trivial
  

theorem aux {a b : ℝ} : max a b = max b a := by
  sorry

#check my_comp.add_comm
