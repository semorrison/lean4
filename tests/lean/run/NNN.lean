universe u v

def TypeMax := Type max u v

example : Type max v u = TypeMax.{v} := rfl
example : Type max v u = TypeMax.{u} := rfl
