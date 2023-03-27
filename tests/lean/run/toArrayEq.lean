inductive Foo
  | foo : Nat → Foo
  | foos : Array Foo → Foo
  deriving BEq

example : Foo.foo 0 ≠ Foo.foo 1 := by simp (config := { decide := true })

example : #[0] ≠ #[1] := by simp (config := { decide := true })

example : #[Foo.foo 0] ≠ #[Foo.foo 1] := by simp (config := { decide := true })

example : Foo.foos #[.foo 0] ≠ Foo.foos #[.foo 1] := by simp (config := { decide := true })
