import  data.real.basic

universes u1 u2
class incidence_geometry :=
(point : Type u1)
(line : Type u2)

(online : point → line → Prop)

(LC1: ∀ {a b : point}, a≠ b→ ∃ (L:line), online a L ∧ online b L)

open incidence_geometry

variables[AxA: incidence_geometry]

include AxA

-------------------------------------------------- API --------------------------------------------
def lineofpair {a b : point} (ab: a≠ b): line :=
begin
  let L := (LC1 ab).some,
  exact L,
end
