class Category (O : Type) where
  H : O → O → Type
  i : (x : O) → H x x
  c : (f : H x y) → (g : H y z) → H x z
  id_comp : (f : H x y) → c (i x) f = f

open Category

noncomputable section

axiom O : Type
variable {I : Category O}

def O' := O

axiom X : O
axiom Y : O

-- Worked in Lean3, but not in Lean4 prior to NNNN.
example (f : H X Y) : @c O' I X X Y (i X) f = f := by simp [id_comp]
