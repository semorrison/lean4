variable {f: Fin l} {f₀: Fin 0} (h: l = 0) (h': (h▸f) = f₀)
example: l = 0              := by simp_all
example (h'': l ≠ 0): False := by simp_all (config := { decide := true })

example: l = 0              := by simp [*] at *
example (h'': l ≠ 0): False := by simp (config := { decide := true }) [*] at *
