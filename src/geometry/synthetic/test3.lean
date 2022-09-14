import set_theory.zfc

universes u
/-

class incidence_geometry :=
(pts : Type u) (lines : set (set pts))
(I1 : ∀ {a b : pts}, a ≠ b → ∃ l ∈ lines,
 a ∈ l ∧ b ∈ l ∧ (∀ l' ∈ lines, a ∈ l' → b ∈ l' → l' = l))
(I2 : ∀ l ∈ lines, ∃ a b : pts, a ≠ b ∧ a ∈ l ∧ b ∈ l)
(I3 : ∃ a b c : pts, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬(∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l))

open incidence_geometry

variable [I : incidence_geometry]

include I


-/

class incidence_geometry :=
(point : Type u)
(lines : set (set point))
(eqd : point → point → point → point → Prop)

(B: point → point → point → Prop)
[dec_B : ∀ a b c, decidable (B a b c)]
-- Equidistance of 4 Points
(P1 {} : point) (P2 {} : point) (P3 {} : point)

(I1a : ∀ (a b : point), a≠b → ∃ (l ∈  lines) , a∈ l ∧ b∈ l)
open incidence_geometry

variables[A: incidence_geometry]

include A

---------------------------------------
