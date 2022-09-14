import geometry.synthetic.test3

open_locale classical


class axioms2  extends incidence_geometry :=
(B1 : ∀ a b c : point, B a b c → B c b a )

variable [B : axioms2]

open incidence_geometry axioms2

include B


theorem ptoffline {l : set point}(H : l ∈ lines): ∃ (p : point), (p ∉ l) :=
begin
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

lemma trivi (a b c d: point) : eqd a a a a → eqd a a a a:=
begin
  have := I1a a b,
  exact id,
end

------------------------------------
