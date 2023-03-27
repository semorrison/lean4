example (a : α) : ¬ some (some a) = some none := by simp (config := { decide := true })
