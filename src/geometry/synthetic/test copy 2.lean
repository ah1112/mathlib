import  data.set --tactic.interactive set_theory.zfc
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

variables {point : Type} [incidence_geometry point]

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
  dsimp [lineseg],
  ext,
  split,{
    intro hyp,
    simp at hyp,
    simp,
    sorry,--have := B2b ,
  },
  sorry,
end

def triangle (a b c : point) : set point :=lineseg a b ∪ lineseg a c ∪ lineseg b c

theorem PlaneSep {l : set point} (hl : l ∈ A.lines): ∃ (S1 S2 : set point), S1≠∅ ∧ S2≠∅ ∧
(∀ (a b : point), ¬ (a∈ l)→ ¬ (b∈ l) → ((lineseg a b ∩ l = ∅ ↔ ((a∈ S1 ∧ b∈ S1)∨ (a ∈ S2 ∧ b ∈ S2)))∧
(lineseg a b ∩ l ≠ ∅ ↔ (a∈ S1 ∧ b∈ S2)∨ (a ∈ S2 ∧ b ∈ S1)))):=
begin
  obtain ⟨p, hp ⟩  := ptoffline hl,
  let S1 := {x : point | lineseg x p ∩ l =∅ },
  let S2 := {x : point | x∉ l ∧ lineseg x p ∩ l ≠ ∅  },
  use [S1, S2],
  split,
  {
    have : p∈ S1,{
      dsimp [S1],

    },
   intro hyp,
   exact set.eq_empty_iff_forall_not_mem.mp hyp p this,
  },
end

theorem LineSep (a : point) (l ∈ A.lines) : ∃ (S1 S2 : set point), S1≠∅ ∧ S2≠∅ ∧
(∀ ( b c : point), b∈ S1 ∧ c∈ S1 ↔ ¬ (a ∈ lineseg b c))∧
 (∀ ( d e : point), d∈ S1 ∧ e∈ S2 ↔ ¬ (a ∈ lineseg d e))∧
 (∀ ( f g : point ), f∈ S1 ∧ g∈ S2 ↔ a ∈ lineseg f g ):=sorry

def samesideline (a b c : point) : Prop := ¬ (a ∈ lineseg b c)
def difsideline (a b c : point) : Prop := (a ∈ lineseg b c)
def ray (a b : point) : set point := {a}∪{x : point | samesideline a b x}
def angle (a b c : point) : set point := ray a b ∪ ray a c
def samesideplane (l : set point) (a b : point) : Prop := l∈ A.lines ∧ lineseg a b ∩ l =∅
def vertexray (a b : point )(h: ray a b) : point := a
def linetwopts (a b : point) (l : set point): Prop := l∈ A.lines ∧  a∈ l ∧ b ∈ l

lemma linetwoptsym (a b : point) (l : set point) : linetwopts a b l → linetwopts b a l :=
begin
  intro hyp,exact ⟨ hyp.1, hyp.2.2, hyp.2.1⟩ ,
end

def insideang (a b c : point) (lab lcb : set point) (h: angle a b c) (h2 : linetwopts a b lab)
    (h3 : linetwopts c b lcb) :=
    {d : point | lab ∈ A.lines ∧ lcb ∈ A.lines ∧ samesideplane lab d c ∧ samesideplane lcb d a}
def insidetri (a b c : point) (lab lac lbc : set point)
  (hab: linetwopts a b lab) (hbc : linetwopts b c lbc ) (hac : linetwopts a c lac)
  (angabc : angle a b c) (angbac : angle b a c) (angacb : angle a c b):=
  {x : point | (x∈ insideang a b c lab lbc angabc hab (linetwoptsym b c lbc hbc)∧
  (x∈ insideang b a c lab lac angbac (linetwoptsym a b lab hab) (linetwoptsym a c lac hac))
   ∧ (x∈ insideang a c b lac lbc angacb hac hbc ))}

theorem crossbar (a b c d : point) (lab lcb : set point) (h: angle a b c) (h2 : linetwopts a b lab)
    (h3 : linetwopts c b lcb) (h1 : d∈ insideang a b c lab lcb h h2 h3) : ray a d ∩ lineseg b c ≠ ∅ :=
begin
sorry,
end

class axioms3 (point : Type) extends axioms2 point :=
(A: ∀ (a : point), a=a)
(C1a: ∀ (a b c e: point), ∃ (d : point), d∈ ray c e → eqd a b c d )
(C1b: ∀ (a b c d d1 e: point), d∈ ray c e → eqd a b c d → eqd a b c d1 → d=d1)
(C2: ∀ (a b c d e f : point), eqd a b c d → eqd c d e f → eqd a b e f)
(C3: ∀ (a b c d e f : point), B a b c → B d e f → eqd a b d e → eqd b c e f→ eqd a c d f)
(C4: ∀ (a b : point), eqd a b a b)
open axioms3

variable [A3 : axioms3 point]
include A3

lemma eqdsym (a b c d: point) : eqd a b c d → eqd c d a b:=
begin
intro hyp,

--have := C2 a b a b c d (C4 a b) hyp,
end
