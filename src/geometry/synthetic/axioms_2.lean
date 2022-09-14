import geometry.synthetic.axioms_1

open_locale classical


class axioms2  extends incidence_geometry :=
(Pa : ∀ (a : point), ∀ (l ∈ lines ), ((¬ a∈ l) → ∃ (l'∈  lines), parallel l l' ∧ a ∈ l'))
(Pb : ∀ (a : point), ∀ (l ∈ lines), ∀ (l1 ∈ lines), ∀ (l2 ∈ lines), parallel l l1
∧ parallel l l2 ∧ a∈ l1 → ¬ a∈ l2)
(B1 : ∀ a b c : point, B a b c → B c b a )
(B1b : ∀ a b c : point, B a b c → ∃ (l ∈ lines), a∈ l ∧ b∈ l ∧ c ∈ l)
(B1c : ∀ a b c : point, B a b c → a≠ b ∧ b≠ c ∧ a≠ c)
(B2 : ∀ a b : point , a≠ b → ∃ c : point , B a b c)
(B3 : ∀ l ∈ lines, ∀ a b c ∈ l, (B a b c ∧ ¬ B b a c ∧ ¬ B a c b)∨(¬ B a b c ∧  B b a c ∧ ¬ B a c b)∨ (¬ B a b c ∧ ¬ B b a c ∧ B a c b))
(B4 : ∀ a b c d: point, noncol a b c →  ∀ (l∈ lines), (d ∈ l) → (a∉l) → (b∉l) → (c∉l)→ (B a d b) →
∃ (e : point ), (e ∈ l) ∧ ((B a e c ∧ (∀ f, f∈ l → ¬ B b f c)) ∨ (B b e c ∧ (∀ f, f∈ l → ¬ B a f c))))

variable [AxB : axioms2]

open incidence_geometry axioms2

include AxB

lemma interB (l : set point) (H: l ∈ lines):∀ a b c ∈ l, B a b c → ¬ B b a c ∧ ¬ B a c b :=
begin
  intros a b c ha hb hc hB,
  have := B3 l H a b c ha hb hc,
  tauto,
end

def lineseg (a b : point) : set point := {a,b}∪{x : point | B a x b}

lemma linesym (a b : point) : lineseg a b = lineseg b a :=
begin
  ext1,
  split,
  {
    intro hyp,
    cases hyp,
    left,finish,
    right, exact B1 a x b hyp,
  },
  intro hyp,
  cases hyp,
  left, finish,
  right,
  exact B1 b x a hyp,
end

def triangle (a b c : point) : set point :=lineseg a b ∪ lineseg a c ∪ lineseg b c

def temp (a b  : point) (l ∈ lines) : Prop := ((a∉l∧  b∉l) ∧ ( a=b ∨ lineseg a b ∩ l = ∅ ))

def tempeqv (a : point) (l∈ lines) : set point := {b:point|temp a b l H}

lemma refltemp (a  : point) (l ∈ lines) (h: a∉ l)  :temp a a l H :=
begin
  unfold temp,
  intros,
  split,finish,
  left,
  finish,
end

lemma symtemp (a b  : point) (l ∈ lines)  (hyp : temp a b l H) : temp b a l H :=
begin
  unfold temp,
  split,split,exact hyp.1.2,exact hyp.1.1,
  cases hyp.2,
  {
    finish,
  },
  {
    right,
    rw linesym b a,finish,
  },
end

lemma transtempnoncol (a b c : point) (l ∈ lines) (hyp : noncol a b c):temp a b l H → temp b c l H  → temp a c l H  :=
begin
  intros hyp1 hyp2,unfold temp,split,split,exact hyp1.1.1,exact hyp2.1.2,
  cases hyp1.2,
  {
    cases hyp2.2,
    {
      finish,
    },
    {
      rw h,finish,
    },
  },
  {
    cases hyp2.2,
    {
      rw← h,finish,
    },
    right,
    ext1,
    split,
    {
      intro hyp3,
      exfalso,

      {
       cases hyp3.1 with hyp4,
       {
         cases hyp4,
         {
           have : a∈ l := by finish,exact hyp1.1.1 this,
         },
         have : c∈ l := by finish, exact hyp2.1.2 this,
       },

       cases B4 a c b x (noncolperm a b c hyp) l H hyp3.2 h_2 with e concl,
       cases concl.2,
       {
         have : e∈ lineseg a b ∩ l,
         {
           split,
           {
             right,
             exact h_3.1,
           },
           {
             exact concl.1,
           },
         },
         finish,
       },
        have : e∈ lineseg b c ∩ l,
         {
           split,
           {
             right,
             exact B1 c e b h_3.1,
           },
           {
             exact concl.1,
           },
         },
         finish,

      },
    },
    tauto,
  },
end

lemma transtempcol (a b c : point) (l ∈ lines) (this : ¬ noncol a b c) (extra : a≠ b ∧ b≠ c ∧ a ≠ c): temp a b l H → temp b c l H  → temp a c l H  :=
begin
  intros hyp1 hyp2,
  have h: a∉l∧ b∉l∧ c∉l,
  {
    split,exact hyp1.1.1,split,exact hyp2.1.1,exact hyp2.1.2,
  },
    {
      unfold noncol at this,
      push_neg at this,
      rcases this with ⟨m, mhyp, hyp3 ⟩ ,
      have sep : ∃ (p : point), p∈ l ∧ p∉ m,
      {
        rcases I2 l H with ⟨ppair,p1h,p2h,pdiff ⟩ ,
        have lem2 : ppair.1∉ m ∨ ppair.2∉ m,
        {
          by_contra hyp5,
          push_neg at hyp5,
          have hyp4:= I1b ppair.1 ppair.2 l m H mhyp pdiff  p1h p2h hyp5.1 hyp5.2,
          rw hyp4 at h,
          have : a∈ m ∧ a∉ m,
          split,exact hyp3.1.1,exact h.1,finish,
        },
        cases lem2,
        use ppair.1,finish,use ppair.2,finish,
      },
      rcases sep with ⟨d, dinl, dnotinm ⟩ ,
      have trivi : d≠ a,
      {
        by_contra,
        push_neg at h,
        rw h at dinl,
        have lol: a∈ l ∧ a∉ l:= by finish,
        exact lol.2 lol.1,
      },
      cases B2 d a trivi with e ehyp,
      have enotinl : e∉l,
      {
        by_contra lol,
        rcases B1b d a e ehyp with ⟨l',l'hyp,dl',al',el' ⟩ ,
        have := I1b d e l l' H l'hyp (B1c d a e ehyp).2.2 dinl lol dl' el',
        rw this at h,
          have : a∈ l' ∧ a∉ l',
          split,exact al',exact h.1,finish,
      },
      have ael : lineseg a e ∩ l =∅ ,
      {
        ext1 f,
        split,
        {
          intro fhyp,
          exfalso,
          by_cases  f=d,
          rcases B1b d a e ehyp with ⟨L,Lhyp,dinL,ainL, einL ⟩ ,
          rw h at fhyp,
          cases fhyp.1,
          cases h_1,
          {
            exact trivi h_1,
          },
          {
            exact (B1c d a e ehyp).2.2 h_1,
          },
          have := B3 L Lhyp d a e dinL ainL einL,finish,
          {
            {
            rcases B1b d a e ehyp with ⟨LL,LLhyp,dinLL,ainLL,einLL⟩ ,
            have : f∈ LL,
            {
              cases fhyp.1,cases h_1,exfalso,rw h_1 at fhyp,finish,
              have : f=e := by finish,
              exfalso, rw this at fhyp,exact enotinl fhyp.2,
              rcases B1b a f e h_1 with ⟨LLL,LLLhyp,ainLLL,finLLL, einLLL ⟩ ,
              have := (B1c a f e h_1).2.2,
              have :=I1b a e LL LLL LLhyp LLLhyp this ainLL einLL ainLLL einLLL,finish,
            },

            {
              have :=I1b f d l LL H LLhyp h fhyp.2 dinl this dinLL,
              rw ← this at ainLL,
              have : a ∈ l ∧ a ∉ l:= by finish,
              exfalso,
              exact this.2 this.1,
            },
          },
          },
        },
        tauto,
      },
      have key : temp a e l H,split,split,exact h.1,exact enotinl,
      right,finish,
      have hyp4 : e ∉ m,
      {
      intro enotinm,
      rcases B1b d a e ehyp with ⟨L,Lhyp,dinL,ainL, einL ⟩ ,
      have := I1b a e m L mhyp Lhyp ((B1c d a e ehyp).2.1) hyp3.1.1 enotinm ainL einL,
      have : d∉m ∧ d∈ m := by finish,exact this.1 this.2,
      },
      have lol2 : noncol e a b,
      {
        unfold noncol,intros L Lhyp eainL binL,
        have := I1b a b m L mhyp Lhyp extra.1 hyp3.1.1 hyp3.1.2 eainL.2 binL,
        rw this at hyp4,
        exact hyp4 eainL.1,
      },
      have key2 : temp e b l H ,
      {
        have : temp e a l H,
        {
          apply symtemp,exact key,
        },
        exact transtempnoncol e a b l H lol2 this hyp1,
      },
      have key3 : temp e c l H,
      {
        have : noncol e b c,
        {
        unfold noncol,intros L Lhyp eainL binL,
        have := I1b b c m L mhyp Lhyp extra.2.1 hyp3.1.2 hyp3.2 eainL.2 binL,
        rw this at hyp4,
        exact hyp4 eainL.1,
        },
        exact transtempnoncol e b c l H this key2 hyp2,
      },
      have lol : noncol a e c,
      {
        unfold noncol,intros L Lhyp eainL binL,
        have := I1b a c m L mhyp Lhyp extra.2.2 hyp3.1.1 hyp3.2 eainL.1 binL,
        rw this at hyp4,
        exact hyp4 eainL.2,
      },
      have := transtempnoncol a e c l H lol key key3,exact this,
    },
end

theorem transtemp (a b c : point) (l ∈ lines):temp a b l H → temp b c l H → temp a c l H :=
begin
  intros tempab tempbc,
  split,split,exact tempab.1.1,exact tempbc.1.2,
  by_cases a=b,
  {
    unfold temp at tempbc,
    rw ← h at tempbc,
    cases tempbc.2,
    left,assumption,right,assumption,
  },
  {
    by_cases a= c,
    {
      rw h,
      left, refl,
    },
    by_cases b=c,
    {
      rw ← h,
      cases tempab.2,left,assumption,right,assumption,
    },
    have : a≠ b ∧ b≠ c ∧ a≠ c := by finish,
    by_cases noncol a b c,
    {
      exact (transtempnoncol a b c l H h tempab tempbc).2,
    },
    exact (transtempcol a b c l H h this tempab tempbc).2,
  },
end

lemma linesegsingleton (p : point) : lineseg p p = {p}:=
begin
ext,
split,
intro hyp,
cases hyp,finish,
exfalso,
have : B p x p, finish,
apply (B1c p x p this).2.2,
refl,
intro xhyp,
have :x=p := by finish,left,finish,
end

lemma Bprop (a b c : point) (l∈ lines) (anol : a∉ l) (binl : b∈ l) (Bhyp : B a b c) : c∉l :=
begin
  intro cinl,
  rcases B1b a b c Bhyp with ⟨L, Lhyp,ainL,binL,cinL ⟩,
  have := I1b b c l L H Lhyp _ binl cinl binL cinL,rw this at anol,exact anol ainL,
  exact (B1c a b c Bhyp).2.1,
end

lemma PlaneSeplem (a b c : point) (l∈ lines) :a∉l → b∉l→ c∉l→ ¬ temp a c l H→ ¬ temp b c l H → temp a b l H :=
begin
  intros anol bnol cnol hypac hypbc,
  by_cases noncol a b c,
  {
    unfold temp at hypac hypbc,
    unfold noncol at h,
    push_neg at hypbc hypac,
    unfold temp,split,
    {
      split,exact anol,exact bnol,
    },
    have phyp:∃ (p: point), p∈ lineseg b c ∩ l,
    {
      have : lineseg b c ∩ l≠ ∅ ,
      {
        have trivi: b∉l ∧ c∉l,finish,exact (hypbc trivi).2,
      },
      have lol:=mt set.eq_empty_iff_forall_not_mem.2 this, push_neg at lol,exact lol,
    },
    have qhyp: ∃ (q: point), q∈ lineseg a c ∩ l,
    {
      have : lineseg a c ∩ l≠ ∅ ,
      {
        have trivi : a∉l ∧c∉ l,finish,exact (hypac trivi).2,
      },
      have lol:=mt set.eq_empty_iff_forall_not_mem.2 this, push_neg at lol,exact lol,
    },
    cases phyp with p phyp,
    cases qhyp with q qhyp,
    have key1: B a q c ∧ B b p c,
    {
      split,
      {
        cases qhyp.1,
        {
          cases h_1,
          {
            rw h_1 at qhyp,exfalso,
            exact anol qhyp.2,
          },
          have trivi : q=c:= by finish,
          rw trivi at qhyp,exfalso,
          exact cnol qhyp.2,
        },finish,
      },
      cases phyp.1,
        {
          cases h_1,
          {
            rw h_1 at phyp,exfalso,
            exact bnol phyp.2,
          },
          have trivi : p=c:= by finish,
          rw trivi at phyp,exfalso,
          exact cnol phyp.2,
        },finish,
    },
    by_contra hyp,push_neg at hyp,
    have rhyp: ∃ (r: point), r∈ lineseg a b ∩ l,have lol:=mt set.eq_empty_iff_forall_not_mem.2 hyp.2, push_neg at lol,exact lol,
    cases rhyp with r rhyp,
    have key : B a r b,
    {
      cases rhyp.1,
        {
          cases h_1,
          {
            rw h_1 at rhyp,exfalso,
            exact anol rhyp.2,
          },
          have trivi : r=b:= by finish,
          rw trivi at rhyp,exfalso,
          exact bnol rhyp.2,
        },finish,
    },
    rcases B4 a b c r h l H rhyp.2 key with ⟨e,ehyp, Bhyp ⟩ ,
    cases Bhyp,
    {
      exact Bhyp.2 p phyp.2 key1.2,
    },
    exact Bhyp.2 q qhyp.2 key1.1,
  },
  sorry,
end

theorem PlaneSep {l : set point} (hl : l ∈ lines): ∃ (S1 S2 : set point), S1≠∅ ∧ S2≠∅ ∧ S1∩S2=∅ ∧
(∀ (a b : point), ¬ (a∈ l)→ ¬ (b∈ l) → ((lineseg a b ∩ l = ∅ ↔ ((a∈ S1 ∧ b∈ S1)∨ (a ∈ S2 ∧ b ∈ S2)))∧
(lineseg a b ∩ l ≠ ∅ ↔ (a∈ S1 ∧ b∈ S2)∨ (a ∈ S2 ∧ b ∈ S1)))):=
begin
/-
cases ptoffline hl with p hp,
use [tempeqv p l hl],
cases I2 l hl with X Xhyp,
cases B2 p X.1 _ with c chyp,
{
  use tempeqv c l hl,
  split,{
    intro hyp,
    have : p∈ tempeqv p l hl,
    {
      unfold tempeqv,unfold temp,split,finish,finish,
    },
    exact set.eq_empty_iff_forall_not_mem.mp hyp p this,
  },
  split,
  {
    intro hyp,
    have : c ∈ tempeqv c l hl,
    unfold tempeqv,unfold temp,split,
    {
      have := Bprop p X.1 c l hl hp Xhyp.1 chyp,finish,
    },
    left, refl,
    exact set.eq_empty_iff_forall_not_mem.mp hyp c this,
  },
split,
{
  ext,split,
  {
    intro hyp,exfalso,unfold tempeqv at hyp,
    have : ¬ temp c p l hl,
    {
      have : X.1∈ lineseg c p∩ l,
      {
        split, right, exact B1 p X.1 c chyp,exact Xhyp.1,
      },
      unfold temp,push_neg,intro lol,split,exact ne_comm.mp (B1c _ _ _ chyp).2.2,intro hyp1,
      exact set.eq_empty_iff_forall_not_mem.mp hyp1 X.1 this,
    },
    have := symtemp p c l hl (transtemp p x c l hl hyp.1 (symtemp c x l hl hyp.2)),finish,
  },
  tauto,
},
intros a b anotinl bnotinl,split,
{
  split,
  {
    intro hyp,
    sorry,
  },sorry,
},sorry,
},
intro lol,
rw lol at hp,
exact hp Xhyp.1,

-/
  obtain ⟨p, hp ⟩  := ptoffline hl,
  let S1 := {x : point | lineseg x p ∩ l =∅ },
  let S2 := {x : point | x∉ l ∧ lineseg x p ∩ l ≠ ∅  },
  use [S1, S2],
  split,
  {--S1≠ ∅
    have : p∈ S1,{
      dsimp [S1],
      rw linesegsingleton p,finish,

    },
   intro hyp,
   exact set.eq_empty_iff_forall_not_mem.mp hyp p this,
  },
  split,
  {--S2≠ ∅
    obtain ⟨⟨ y,y2⟩ ,hy ⟩ :=I2 l hl,
    have : p≠ y,
    {
      by_contra,push_neg at h, rw h at hp,exact hp hy.1,
    },
    obtain ⟨ c , hc⟩ := B2 p y this,
    have : c∈ S2,
    {
      split,
      {
        exact Bprop p y c l hl hp hy.1 hc,
      },
      rw set.ne_empty_iff_nonempty,use y,
      split,
      {
        right,exact B1 _ _ _ hc,
      },
      exact hy.1,
    },
    intro hyp,
     exact set.eq_empty_iff_forall_not_mem.mp hyp c this,

  },
  split,
  {--S1∩S2=∅
    ext,
    split,
    {
      rintros ⟨xins1,xins2 ⟩,
      exfalso,
      exact xins2.2 xins1,
    },
    tauto,
  },
intros a b ha hb,
split,
{

split,
{
  intro lineab,
  by_cases a∈ S1,
  {
    left,split,exact h,
    by_contra bs2,
    simp at bs2,
    obtain ⟨d, hd⟩  :=set.ne_empty_iff_nonempty.mp bs2 ,
    by_cases hnoncol : (noncol b p a),
    {
      have neq:= noncolneq b p a hnoncol,
      have Bbdp : B b d p,
      {
        cases hd.1,
        {
          cases h_1,
          {
            exfalso,
            rw ← h_1 at hb,
            exact hb hd.2,
          },
          {
            have : d=p := by finish,
            rw ← this at hp,
            exfalso,
            exact hp hd.2,
          },

        },exact h_1,
      },
      obtain ⟨ e,he, pasch⟩  := B4 b p a d hnoncol l hl hd.2 hb hp ha Bbdp,
      cases pasch,
      {
        have : e∈ lineseg a b∩ l,
        {
          split,
          {
            right,
            exact B1 _ _ _ pasch.1,
          },exact he,
        },
        rw lineab at this,finish,
      },
      {
        simp at h,
        have : e∈ lineseg a p ∩ l,
        {
          split,
          {
            right,
            exact B1 _ _ _ pasch.1,
          },exact he,
        },
        rw h at this, finish,
      },
    },
  unfold noncol at hnoncol,push_neg at hnoncol,
  rcases hnoncol with ⟨L, hL, bpinL, ainL ⟩,
  have := B3 L hL a b p ainL bpinL.1 bpinL.2,
  cases this,
  {
    have : a∉S1,
  },

  },
  sorry,
},
sorry,
},
sorry,

end

theorem LineSep (a : point) (l ∈ lines) : ∃ (S1 S2 : set point), S1≠∅ ∧ S2≠∅ ∧ S1∩S2=∅ ∧
(∀ ( b c : point), ((b∈ S1 ∧ c∈ S1)∨(b ∈ S2 ∧ c∈ S2)↔ ¬ (a∈ lineseg b c))∧
 ((b∈ S1 ∧ c∈ S2)∨(b ∈ S2 ∧ c∈ S1)↔ (a∈ lineseg b c))):=sorry

def samesideline (a b c : point) : Prop :=∃ l∈ lines, a∈ l∧ b∈ l∧ c∈ l ∧ ¬ (a ∈ lineseg b c)
def difsideline (a b c : point) : Prop := (b ∈ lineseg a c)
def ray (a b : point) : set point := {a}∪{x : point | samesideline a b x}
def angle (a b c : point) : set point := ray a b ∪ ray a c
def samesideplane (l : set point) (a b : point) : Prop := l∈ lines ∧ lineseg a b ∩ l =∅
def vertexray (a b : point )(h: ray a b) : point := a
def linetwopts (a b : point) (l : set point): Prop := l∈ lines ∧  a∈ l ∧ b ∈ l

/-
lemma difsidebtw (a b c : point) (H: difsideline a b c) : B a b c :=by finish
lemma sidebtw (a b c : point) (H: samesideline a b c) : B a b c ∨ B a c b :=
begin
  unfold samesideline at H,
  obtain ⟨l, Hl, aonl, bonl, conl, anoseg ⟩ := H,
  have := B3 l Hl a b c aonl bonl conl,
  unfold lineseg at anoseg,
  have lol : ¬ B b a c := by finish,
  tauto,
end
-/
lemma linetwoptsym (a b : point) (l : set point) : linetwopts a b l → linetwopts b a l :=
begin
  intro hyp,exact ⟨ hyp.1, hyp.2.2, hyp.2.1⟩ ,
end

def insideang (a b c : point) (lab lcb : set point) (h: angle a b c) (h2 : linetwopts a b lab)
    (h3 : linetwopts c b lcb) :=
    {d : point | lab ∈ lines ∧ lcb ∈ lines ∧ samesideplane lab d c ∧ samesideplane lcb d a}
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
------------------------------------
