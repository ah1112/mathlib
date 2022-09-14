import geometry.synthetic.test3_1

open_locale classical


class axioms3  extends axioms2 :=
(C1 : ∀ a b c : point, a=a )

variable [C : axioms3]

open incidence_geometry axioms2 axioms3

include C


theorem trivi2 (a : point) {l : set point}(H : l ∈ lines): ∃ (p : point), (p ∉ l) :=
begin
  have t1:= I1a a a,
  have t2:= B1 a a a,
  have t3:= C1 a a a,
  by_cases h1: P1∉ l,use P1,
  by_cases h2: P2∉ l, use P2,
  by_cases h3: P3∉ l, use P3,
  push_neg at h1 h2 h3,
  exfalso,
  have : ∃ (l∈ lines), (P1∈ l ∧ P2∈ l∧ P3∈ l),
  {
    use l,
    exact ⟨H, h1, h2, h3 ⟩,
  },
  sorry,--exact I3 this,
end


------------------------------------
