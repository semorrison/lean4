example : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true, decide := true })

example : if x = 0 then y + x = y else x ≠ 0 := by
  split
  simp_all
  simp_all (config := { decide := true })

example : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true, decide := true })
  split -- Error: no goals to be solved
