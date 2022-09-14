import set_theory.zfc data.real.basic

universes u

class incidence_geometry :=
(point : Type u)
(lines : set (set point))
(eqd : point → point → point → point → Prop)

(B: point → point → point → Prop)
[dec_B : ∀ a b c, decidable (B a b c)]
-- Equidistance of 4 Points
(P1 {} : point) (P2 {} : point) (P3 {} : point)

(I1a : ∀ (a b : point), ∃ (l :  set point) , l∈ lines ∧ a∈ l ∧ b∈ l)
(I1b : ∀ (a b : point), ∀ (l l'∈  lines), a≠b →  a∈  l →  b∈  l →  a∈  l' →  b∈  l'  →l=l')
(I2 : ∀ l ∈ lines, ∃ (X:point×point), X.1 ∈ l ∧  X.2 ∈ l ∧ X.1≠ X.2)
(I3 : ¬ ∃ l ∈ lines , P1∈  l ∧ P2∈  l ∧ P3∈  l)

open incidence_geometry

variables[AxA: incidence_geometry]

include AxA

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

theorem LinesOnePt (p p': point) (l1 l2 :  set point) (l1≠ l2) (h1 : l1 ∈ lines)(h2 : l2 ∈  lines): p∈  l1 →  p∈  l2 →  p'∈  l1 →  p'∈  l2 → p=p':=
begin
  intros hyp1 hyp2 hyp3 hyp4,
  apply by_contra,
  intros h,
  exact H( I1b p p' l1 l2 h1  h2 h hyp1 hyp3 hyp2 hyp4),
end

def parallel (l1 l2 :  set point) : Prop := (l1 ∈ lines)∧ (l2 ∈ lines) ∧ l1∩l2=∅

def noncol (a b c : point) : Prop := ∀ (l∈ lines), (a∈ l ∧ b∈ l → c∉ l)

lemma noncolperm (a b c : point) : noncol a b c → noncol a c b:=
  begin
    intro hyp,
    unfold noncol,
    intros l lhyp,
    have := hyp l lhyp,
    intro lol,
    have trivi : (b ∈ l ∨ b∉ l):= by finish,
    cases trivi,
    have dumb: a∈ l ∧ b∈ l,
    {
      finish,
    },
    exfalso,
    apply this dumb,finish,finish,
end

lemma noncolneq (a b c : point) : noncol a b c → a≠ b ∧ b≠ c ∧ a≠ c :=
begin
  intro non,
  split,
  {
    intro eq,
    rw eq at non,
    rcases I1a b c with ⟨l,lhyp,binl,cinl ⟩ ,
    have : ¬ noncol b b c,
    {
      unfold noncol,push_neg,use l,split,exact lhyp,finish,
    },
    exact this non,
  },
  split,
  {
    intro eq,
    rw eq at non,
    rcases I1a a c with ⟨l,lhyp,binl,cinl ⟩ ,
    have : ¬ noncol a c c,
    {
      unfold noncol,push_neg,use l,split,exact lhyp,finish,
    },
    exact this non,
  },
    intro eq,
    rw eq at non,
    rcases I1a b c with ⟨l,lhyp,binl,cinl ⟩ ,
    have : ¬ noncol c b c,
    {
      unfold noncol,push_neg,use l,split,exact lhyp,finish,
    },
    exact this non,
end
---------------------------------------
