import geometry.synthetic.axioms_2

open_locale classical


class axioms3  extends axioms2 :=
(eqa : point → point → point → point →point  → point → Prop)
(C1a: ∀ (a b c e: point), ∃ (d : point), d∈ ray c e → eqd a b c d )
(C1b: ∀ (a b c d d1 e: point), d∈ ray c e → eqd a b c d → eqd a b c d1 → d=d1)
(C2: ∀ (a b c d e f : point), eqd a b c d → eqd a b e f → eqd c d e f)
(C3: ∀ (a b c d e f : point), B a b c → B d e f → eqd a b d e → eqd b c e f→ eqd a c d f)
(C2b: ∀ (a b : point), eqd a b a b)
(C4: ∀ (a b c d f : point),∃ (e : point), eqa b a c e d f)
(C4b: ∀ (a b c d f e e' : point), eqa b a c e d f → eqa b a c e' d f → ray d e = ray d e' )
(C5: ∀ (a1 b1 c1 a2 b2 c2 a3 b3 c3 : point), eqa a1 b1 c1 a2 b2 c2 → eqa a1 b1 c1 a3 b3 c3 → eqa a2 b2 c2 a3 b3 c3)
(C5b: ∀ (a b c : point), eqa a b c a b c)
(C6: ∀ (a b c d e f : point), eqd a b d e→ eqd a c d f→ eqa b a c e d f → eqd b c e f ∧ eqa a b c d e f ∧ eqa a c b d f e)

variable [AxC : axioms3]

open incidence_geometry axioms2 axioms3

include AxC

lemma eqdsym (a b c d: point) : eqd a b c d → eqd c d a b:=
begin
intro hyp, exact C2 a b c d a b hyp (C2b a b),
end

lemma eqdtrans (a b c d e f : point) : eqd a b c d → eqd c d e f → eqd a b e f :=
begin
  intros hyp1 hyp2, exact C2 c d a b e f (eqdsym _ _ _ _ hyp1) hyp2,
end

lemma linebehave1 (a b c d : point) : B a b c → B b c d → B a c d :=
begin
  intros hyp1 hyp2,
  rcases B1b b c d hyp2 with ⟨l,lhyp,bhyp,chyp,dhyp⟩ ,
  rcases B1b a b c hyp1 with ⟨l',l'hyp,ahyp',bhyp',chyp'⟩ ,
  have unique := I1b b c l l' lhyp l'hyp (B1c a b c hyp1).2.1 bhyp chyp bhyp' chyp',
  rw ←  unique at ahyp',clear l'hyp bhyp' chyp' unique l',
  rcases LineSep c l lhyp with ⟨S1,S2,S1n,S2n,S1S2,hyp⟩ ,
  have lol : c∈ lineseg b d,
  {
    right,finish,
  },
  have lol2: c∉ lineseg a b,by_contra,
  {
    have : B a c b ,
    {
      sorry,
      },
    have lol3 :=B3 l lhyp a b c ahyp' bhyp chyp,
    finish,
  },
  have key := (hyp b d).2.2 lol,
  have key1 := (hyp a b).1.2 lol2,cases key1,
  {
    have trivi : b∈ S1 ∧ d ∈ S2,
    {
      cases key,
      {
        finish,
      },
      {
        have : b ∈ S1∩ S2,
        split,finish,finish,rw  S1S2 at this,finish,
      },

    },
    have key2 : a∈ S1 ∧ d ∈ S2 := by finish,
    have key3 := (hyp a d).2.1,
    have trivi : c∈ lineseg a d := by finish,
    cases trivi,cases trivi_1,
    {
      rw trivi_1 at lol2,unfold lineseg at lol2,have : a≠ a :=by finish,exfalso, finish,
    },  sorry,sorry,
  },
  have trivi : b∈ S2 ∧ d ∈ S1,
  {
    cases key,
    have : b ∈ S1∩ S2,
    split,finish,finish,rw  S1S2 at this,finish,exact key,
  },
    have key2 : a∈ S2 ∧ d ∈ S1 := by finish,
    have key3 := (hyp a d).2.1,
    have trivi : c∈ lineseg a d := by finish,sorry,--exact trivi,
end

lemma lateray (a b : point)(diff : a≠ b): ∃ (c : point), ∀ x ∈ ray b c, samesideline a b x :=
begin
  cases B2 a b diff with c hyp,
  use c,
  intros x rayhyp,
  cases rayhyp with hyps,
  {
    cases I1a a b with l lhyp,
    use l,
    split, exact lhyp.1,
    split, exact lhyp.2.1,
    split, exact lhyp.2.2,
    have trivi : x=b,
    exact set.mem_singleton_iff.mp hyps,
    split,
    {
      rw trivi,
      exact lhyp.2.2,
    },
    rw trivi,
    by_contra,
    apply diff,
    exfalso,
    cases h,cases h,exact diff h,exact diff h,have := B1c b a b h,have : b=b := by refl,finish,
  },
  have trivi : samesideline b c x,tauto,
  rcases trivi with ⟨ l, hypl, hypbl, hypcl, hypxl, bnot⟩ ,
  unfold samesideline,
  by_contra,
  push_neg at h,
    rcases B1b a b c hyp with ⟨l',l'hyp, ahyp,bhyp,chyp ⟩ ,
    rw ← (I1b b c l l' hypl l'hyp ((B1c a b c hyp).2.1) hypbl hypcl bhyp chyp) at ahyp,
  have :=h l hypl ahyp hypbl hypxl,
  have lol :  B b a x,
  {
    cases this,cases this,exfalso, exact diff this,exfalso,sorry,
    exact this,
  },
  have lol3 := B1 x b c (linebehave1 x a b c (B1 b a x lol) hyp),
  apply bnot,
  right, exact lol3,
end

def sumseg (a b c d e: point) (h: B a b e) (h1: eqd b e c d): set point := lineseg a e

theorem sumcong (a b c d a' b' c' d' e e' : point) (h : B a b e)(h' : B a' b' e') (h1 : eqd b e c d)
(h1': eqd b' e' c' d') (hyp : eqd a b a' b')(hyp1 : eqd c d c' d'):eqd a e a' e':=
begin
  sorry,
end

theorem diffseg (a b c d e f : point)(h : B a b c)(h' : e∈ ray d f)(h1 : eqd a b d e ∧ eqd a c d f):
B d e f ∧ eqd b c e f:=
begin
  sorry,
end

def lessseg (a b c d : point) : Prop := ∃ (e : point), B c e d ∧ eqd a b c e

theorem congrless1 (a b c d a' b' c' d' : point) (h: eqd a b a' b' ∧ eqd c d c' d'):lessseg a b c d↔ lessseg a' b' c' d':=
begin
  sorry,
end

theorem congrless2 (a b c d e f : point)(h: lessseg a b c d ∧ lessseg c d e f):lessseg a b e f:=
begin
  sorry,
end

theorem angsym (a1 b1 c1 a2 b2 c2 : point)  :eqa a1 b1 c1 a2 b2 c2→  eqa a2 b2 c2 a1 b1 c1 :=
begin
  sorry,
end

theorem angtrans (a1 b1 c1 a2 b2 c2 a3 b3 c3 : point):  eqa a1 b1 c1 a2 b2 c2  → eqa a2 b2 c2 a3 b3 c3 → eqa a1 b1 c1 a3 b3 c3:=
begin
  sorry,
end

def sumang (a b c d : point) (lab lac : set point)(ang : angle b a c)(h2 : linetwopts b a lab)
    (h3 : linetwopts c a lac)
(h: ray a d ⊂ insideang b a c lab lac ang h2 h3): set point := angle b a c

def supl (a b c d : point)(l ∈ lines):Prop :=a∈ l ∧ c∈l ∧ d∈ l ∧ difsideline d a c

theorem suplmiss (a b c d a1 b1 c1 d1: point)(l1 : set point)(H1 : l1∈ lines )(l2∈ lines): supl a b c d l1 H1 → supl a1 b1 c1 c1 l2 H→ eqa b a c b1 a1 c1 → eqa b a d b1 a1 d1:=
begin
  sorry,
end

def vert (a b c a1 c1 : point): Prop :=  noncol a b c∧ B a b c1 ∧ B a1 b c

theorem vertcon (a b c a1 c1 : point) :vert a b c a1 c1 → eqa a b c a1 b c1 :=
begin
  sorry,
end

theorem angaddcon (a b c d a1 b1 c1 d1: point) (lab lac la1b1 la1c1 la1d1: set point)(ang : angle b a c)
(ang1: angle b1 a1 c1)(h2 : linetwopts b a lab)(h21 : linetwopts b1 a1 la1b1) (h31 : linetwopts c1 a1 la1c1)
    (h3 : linetwopts c a lac) (h4: linetwopts a1 d1 la1d1)(h: ray a d ⊂ insideang b a c lab lac ang h2 h3) :
    eqa d a c d1 a1 c1→ eqa b a d b1 a1 d1 → ∀ x∈ ray a1 b1, ¬ samesideplane la1d1 x c1 →
    eqa b a c b1 a1 c1 ∧ ray a1 d1 ⊂ insideang b1 a1 c1 la1b1 la1c1 ang1 h21 h31 :=
begin
  sorry,
end

def angless (a b c d e f : point)(lde ldf : set point)(ang : angle e d f)(h2 : linetwopts e d lde)
    (h3 : linetwopts f d ldf) : Prop := ∃ (g: point), ray d g ⊂ insideang e d f lde ldf ang h2 h3 ∧ eqa b a c g d f

theorem angless1 (a b c d e f a1 b1 c1 d1 e1 f1: point)(lde ldf lde1 ldf1: set point)(ang : angle e d f)(h2 : linetwopts e d lde)
    (h3 : linetwopts f d ldf)(ang1 : angle e1 d1 f1)(h21 : linetwopts e1 d1 lde1)
    (h31 : linetwopts f1 d1 ldf1) : eqa a b c a1 b1 c1 → eqa d e f d1 e1 f1 → angless a b c d e f lde ldf ang h2 h3 ↔
    angless a1 b1 c1 d1 e1 f1 lde1 ldf1 ang1 h21 h31 :=
  begin
    sorry,
  end

theorem angless2 (a b c a1 b1 c1 a2 b2 c2 : point)(lde ldf lde1 ldf1 lde2 ldf2: set point)(ang : angle a1 b1 c1)(h2 : linetwopts e d lde)
    (h3 : linetwopts f d ldf)(ang1 : angle e1 d1 f1)(h21 : linetwopts e1 d1 lde1)
    (h31 : linetwopts f1 d1 ldf1) : eqa a b c a1 b1 c1 → eqa d e f d1 e1 f1 → angless a b c d e f lde ldf ang h2 h3 ↔
    angless a1 b1 c1 d1 e1 f1 lde1 ldf1 ang1 h21 h31 :=
  begin
    sorry,
  end
------------------------------------
