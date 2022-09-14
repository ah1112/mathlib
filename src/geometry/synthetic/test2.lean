import  data.set tactic.interactive set_theory.zfc
class incidence_geometry (point : Type):=
(lines : set (set point))
(eqd : point → point → point → point → Prop)

(B: point → point → point → Prop)
[dec_B : ∀ a b c, decidable (B a b c)]
-- Equidistance of 4 Points
(P1 {} : point) (P2 {} : point) (P3 {} : point)

(I1a : ∀ (a b : point), a≠b → ∃ (l ∈  lines) , a∈ l ∧ b∈ l)
(I1b : ∀ (a b : point), ∀ (l l'∈  lines), a≠b →  a∈  l →  b∈  l →  a∈  l' →  b∈  l'  →l=l')
(I2 : ∀ l ∈ lines, ∃ (X:point×point), X.1 ∈ l ∧  X.2 ∈ l ∧ X.1≠ X.2)
(I3 : ¬ ∃ l ∈ lines , P1∈  l ∧ P2∈  l ∧ P3∈  l)
open incidence_geometry

variables {point : Type} [A : incidence_geometry point]

theorem ptoffline {l : set point}(H : l ∈ A.lines): ∃ (p : point), (p ∉ l) :=
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
  exact I3 this,
end

theorem LinesOnePt {p p': point} {l1 l2 :  set point} (l1≠ l2) (h1 : l1 ∈ A.lines)(h2 : l2 ∈  A.lines): p∈  l1 →  p∈  l2 →  p'∈  l1 →  p'∈  l2 → p=p':=
begin
  intros hyp1 hyp2 hyp3 hyp4,
  apply by_contra,
  intros h,
  exact H( I1b p p' l1 l2 h1  h2 h hyp1 hyp3 hyp2 hyp4),
end

def parallel (l1 l2 :  set point) : Prop := (l1 ∈ A.lines)∧ (l2 ∈ A.lines) ∧ l1∩l2=∅

class axioms2 (point : Type) extends incidence_geometry point :=
(Pa : ∀ (a : point), ∀ (l ∈ lines ), ((¬ a∈ l) → ∃ (l'∈  lines), parallel l l' ∧ a ∈ l'))
(Pb : ∀ (a : point), ∀ (l ∈ lines), ∀ (l1 ∈ lines), ∀ (l2 ∈ lines), parallel l l1
∧ parallel l l2 ∧ a∈ l1 → ¬ a∈ l2)
(B1 : ∀ a b c : point, B a b c → B c b a )
(B2 : ∀ a b : point , ∃ c : point , B a b c)
(B2b : ∀ a x : point , B a x a → x=a)
(B3 : ∀ l ∈ lines, ∀ a b c ∈ l, xor (xor (B a b c) (B b c a)) (B c a b))
(B4 : ∀ a b c d: point, ∀ l∈ lines, (¬ a ∈ l ) ∧(¬ b ∈ l ) ∧(¬ c ∈ l ) ∧ (d ∈ l) ∧ (B a d b) →
∃ (e : point ), (e ∈ l) ∧ (B a e c ∧ ¬ B b e c) ∨ (B b e c ∧ ¬ B a e c))
open axioms2

variable [A2 : axioms2 point]
include A2

def lineseg (a b : point) : set point := {x : point | B a x b}

lemma linesegsingleton ( a : point) : lineseg a a = {a} :=
begin
  have := I2, -- not necessary
  have := B1 a a a , -- now works
  sorry,
end
