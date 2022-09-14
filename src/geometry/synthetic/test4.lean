import  data.set tactic.interactive set_theory.zfc
class incidence_geometry (point : Type):=
(lines : set (set point))
(eqd : point → point → point → point → Prop)

(B: point → point → point → Prop)
[dec_B : ∀ a b c, decidable (B a b c)]
-- Equidistance of 4 Points
(P1 {} : point) (P2 {} : point) (P3 {} : point)

(I1a : ∀ (a b : point), a≠b → ∃ (l ∈  lines) , a∈ l ∧ b∈ l)
open incidence_geometry

variables {point : Type} [A : incidence_geometry point]


class axioms2 (point : Type) extends incidence_geometry point :=
(B1 : ∀ a b c : point, B a b c → B c b a )
open axioms2

variable [A2 : axioms2 point]
include A2

lemma trivi (a b c d: point) : eqd a a a a → eqd a a a a:=
begin
have := B1 a a a,
simp,
end

class axioms3 (point : Type) extends axioms2 point :=
(A: ∀ (a : point), a=a)
open axioms2 axioms3

variable [A3 : axioms3 point]
include A3

lemma eqdsym (a b c d: point) : eqd a b c d → eqd c d a b:=
begin
intro hyp,

have := C2 a b a b c d (C4 a b) hyp,
end
