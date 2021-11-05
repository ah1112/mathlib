import set_theory.zfc data.real.basic

universes u1 u2 u3
class incidence_geometry :=
(point : Type u1)
(line : Type u2)
(circle : Type u3)

(online : point → line → Prop)
(sameside : point → point → line → Prop)
(B: point → point → point → Prop)
(oncircle : point → circle → Prop)
(inside : point → circle → Prop)
(center : point → circle → Prop)
(interlineline : line → line → Prop)
(interlinecircle : line → circle → Prop)
(intercirclecircle : circle → circle → Prop)
(length : point → point → real )
(angle : point→ point → point → real)

(P1 : ∀ (S: set point), ∃ (a : point) , a∉ S) --Does not work for S=everything. What to do?
(P2 : ∀ (L :  line), ∃ (a: point ), online a L)
(P3 : ∀ (L : line) , ∀ (b c : point), online b L→ online c L→b≠ c→ ∃ (a : point), online a L ∧  B b a c)
(P4 : ∀ (L : line), ∀ (b c : point), online b L → online c  L → b≠ c→ ∃ (a : point), B b c a)
(P5: ∀ (L : line), ∀ (b : point), ¬ online b L → ∃ (a: point), a≠ b ∧ sameside a b L)
(P6: ∀ (L : line), ∀ (b : point), ¬ online b L → ∃ (a: point), ¬ sameside a b L)
(P7: ∀ (α : circle), ∃ (a : point), oncircle a α)
(P8: ∀ (α : circle), ∃ (a : point), inside a α)
(P9: ∀ (α : circle), ∃ (a : point), ¬ inside a α ∧ ¬ oncircle a α )

(LC1: ∀ (a b : point), a≠ b→ ∃ (L:line), online a L ∧ online b L)
(LC2: ∀ (a b : point), a≠ b→ ∃ (α : circle), center a α ∧ oncircle b α )

(I1: ∀ (L M : line), interlineline L M → ∃ (a: point), online a L ∧ online a M)
(I2: ∀ (L : line), ∀ (α : circle),interlinecircle L α → ∃ (a : point), online a L ∧ oncircle a α ) --Should be proven
(I3: ∀ (L : line), ∀ (α : circle),interlinecircle L α → ∃ (a b : point), online a L ∧ online b L
  ∧ oncircle a α ∧ oncircle b α ∧ a≠ b)
(I4: ∀ (b c : point), ∀ (L : line), ∀ (α : circle), inside b α → online b L → ¬ inside c α →
  ¬ oncircle c α → online c L →∃ (a : point), oncircle a α ∧ online a L∧ B b a c)
(I5: ∀ (b c : point), ∀ (L: line), ∀ (α : circle), inside b α → online b L → c≠ b → online c L →
  ∃ (a : point), oncircle a α ∧ online a L ∧ B a b c)
(I6: ∀ (α β : circle), intercirclecircle α β → ∃ (a : point), oncircle a α ∧ oncircle a β) --can be proven
(I7: ∀ (α β : circle), intercirclecircle α β → ∃ (a b: point), oncircle a α ∧ oncircle a β ∧ oncircle b α ∧ oncircle b β∧ a≠ b)
(I8: ∀ (b c d : point), ∀ (α β : circle), ∀ (L : line), intercirclecircle α β → center c α → center d β
 → online c L → online d L → ¬ online b L → ∃ (a : point), oncircle a α ∧ oncircle a β ∧ sameside a b L)
(I9: ∀ (b c d : point), ∀ (α β : circle), ∀ (L : line), intercirclecircle α β → center c α → center d β
 → online c L → online d L → ¬ online b L → ∃ (a : point), oncircle a α ∧ oncircle a β ∧ ¬ sameside a b L∧ ¬ online a L)

(G1: ∀ (a b : point), ∀ (L M: line), a≠ b →  online a L → online b L → online a M → online b M → L=M)
(G2: ∀ (a b : point), ∀ (α : circle), center a α → center b α → a=b) --should be proven?
(G3: ∀ (a : point), ∀ (α : circle), center a α → inside a α )
(G4: ∀ (a : point), ∀ (α : circle), inside a α → ¬ oncircle a α )

(B1: ∀ (a b c : point), B a b c → B c b a ∧ a≠ b ∧ a≠ c ∧ b ≠ c∧ ¬  B b a c) -- slightly modified, hope no issue?
(B2: ∀ (a b c : point), ∀ (L : line), B a b c→ online a L → online b L → online c L)
(B3: ∀ (a b c : point), ∀ (L : line), B a b c→ online a L → online c L → online b L)--can be proven?
(B4: ∀ (a b c d : point), B a b c→ B a d b → B a d c)
(B5: ∀ (a b c d : point), B a b c→ B b c d → B a b d)
(B6: ∀ (a b c : point), ∀ (L : line), online a L → online b L → online c L → a≠ b → a≠ c → b≠ c → B a b c ∨ B b a c ∨ B a c b)
(B7: ∀ (a b c d : point), B a b c → B a b d → ¬ B c b d)

(S1: ∀ (a : point), ∀ (L : line), ¬ online a L → sameside a a L)
(S2: ∀ (a b : point), ∀ (L : line), sameside a b L → sameside b a L)
(S3: ∀ (a b : point), ∀ (L : line), sameside a b L → ¬ online a L)
(S4: ∀ (a b c : point), ∀ (L : line), sameside a b L → sameside a c L → sameside b c L)
(S5: ∀ (a b c : point), ∀ (L : line), ¬ online a L → ¬ online b L → ¬ online c L→ ¬ sameside a b L→ sameside a c L ∨ sameside b c L)

(Pa1: ∀ (a b c : point), ∀ (L : line), B a b c → sameside a c L → sameside a b L)
(Pa2: ∀ (a b c : point), ∀ (L : line), B a b c → online a L → ¬ online b L → sameside b c L)
(Pa3: ∀ (a b c : point), ∀ (L : line), B a b c → online b L → ¬ sameside a c L)
(Pa4: ∀ (a b c : point), ∀ (L M : line), L≠ M → a≠ c → online a M → online b M → online c M→ online b L → a≠ b → c≠ b → ¬ sameside a c L → B a b c)

(T1: ∀ (a b c d : point), ∀ (L M N : line), online a L → online a M → online a N → online b L → online c M
  → online d N → sameside c d L → sameside b c N → ¬ sameside b d M)
(T2: ∀ (a b c d : point), ∀ (L M N : line), online a L → online a M → online a N → online b L → online c M
  → online d N → sameside c d L → ¬ sameside b d M → ¬ online d M → b≠ a → sameside b c N)
(T3: ∀ (a b c d e: point), ∀ (L M N : line), online a L → online a M → online a N → online b L → online c M
  → online d N → sameside c d L →  sameside b c N → sameside d e M → sameside c e N→ sameside c e L)

(C1: ∀ (a b c : point), ∀ (L: line), ∀ (α : circle ), online a L → online b L → online c L
  → inside a α → oncircle b α → oncircle c α → b≠ c→ B b a c)
(C2: ∀ (a b c : point), ∀ (α : circle), inside a α ∨ oncircle a α → inside b α ∨ oncircle b α → B a c b → inside c α)
(C3: ∀ (a b c : point), ∀ (α : circle), inside a α ∨ oncircle a α → ¬ inside c α → B a c b → ¬ inside b α ∧ ¬ oncircle b α)
(C4: ∀ (a b c d : point), ∀ (α β : circle), ∀ (L : line), α ≠ β → c≠ d→ intercirclecircle α β → oncircle c α
  → oncircle c β → oncircle d α → oncircle d β → center a α → center b β → online a L → online b L → ¬ sameside c d L)
----------------------
(Int1: ∀ (a b : point), ∀ (L M : line), ¬ sameside a b L → online a M → online b M → interlineline L M)
(Int2: ∀ (a b : point), ∀ (L : line), ∀ (α : circle ), inside a α ∨ oncircle a α → inside b α ∨ oncircle b α
  → ¬ sameside a b L → interlinecircle L α )
(Int3: ∀ (a : point), ∀ (L: line), ∀ (α : circle), inside a α → online a L → interlinecircle L α )
(Int4: ∀ (a b : point), ∀ (α β : circle), oncircle a α → inside b α ∨ oncircle b α → inside a β →  ¬ inside b β
  → intercirclecircle α β )
(Int5: ∀ (a b : point), ∀ (α β : circle), inside a α → oncircle b α → inside b β → oncircle a β → intercirclecircle α β )

(M1: ∀ (a b : point), length a b = 0 ↔ a =b)
(M2: ∀ (a b : point), length a b = length b a)
(M3: ∀ (a b c : point), a≠ b→ a≠c → angle a b c = angle c b a)
(M4: ∀ (a b c : point), angle a b c ≤ 180 ∧ 0 ≤ angle a b c)
(M5: ∀ (a b : point), 0 ≤ length a b)

(DS1: ∀ (a b c : point), B a b c → length a b + length b c = length a c)
(DS2: ∀ (a b c : point), ∀ (α β : circle), center a α → center a β → oncircle b α → oncircle c β → length a b = length a c → α =β )
(DS3: ∀ (a b c : point), ∀ (α : circle), center a α → oncircle b α → (length a b = length a c ↔ oncircle c α))
(DS4: ∀ (a b c : point), ∀ (α : circle), center a α → oncircle b α → (length a c < length a b ↔ inside c α))

(A1: ∀ (a b c : point), ∀ (L: line), a≠ b → a≠ c→ online a L → online b L → online c L ∧ ¬ B b a c ↔ angle b a c =0)
(A2: ∀ (a b c d : point), ∀ (L M : line), online a L → online b L → online a M → online c M → a ≠ b → a≠ c
  → ¬ online d M → ¬ online d L → L≠ M → angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L)
(A3: ∀ (a b c d : point), ∀ (L : line), online a L → online b L → B a c b → ¬ online d L → angle a c d = angle d c b ↔ angle a c d =90)
(A4: ∀ (a b c a1 b1 c1 : point),∀ (L M: line), online a L → online b L→ online b1 L → online a M→ online c M
   → online c1 M → b≠ a → b1≠ a → c≠ a → c1≠ a → ¬ B b a b1 → ¬ B c a c1 → angle b a c = angle b1 a1 c1)
(A5: ∀ (a b c d : point), ∀ (L M N : line), online a L → online b L → online b M → online c M → online c N → online d N → b ≠ c
  → sameside a d N → angle a b c + angle b c d < 180 → ∃ (e : point), online e L ∧ online e N ∧ sameside e a M)

--Probably should ask about the superposition thing?

open incidence_geometry

variables[AxA: incidence_geometry]

include AxA

theorem eqtri (a b : point) (hab : a≠ b): ∃ (c : point), length a b = length b c ∧ length b c = length a c∧ c≠ a ∧ c≠ b :=
begin
  rcases LC2 a b hab with ⟨α, acen, bcirc⟩ ,
  rcases LC2 b a (ne.symm hab) with ⟨β, bcen, acirc ⟩,
  rcases I6 α β (Int5 a b α β (G3 a α acen) bcirc (G3 b β bcen) acirc) with ⟨c,cona,conb ⟩ ,
  use c,
  split,
  { have := (DS3 b a c β bcen acirc).2 conb,rw ← this,exact M2 a b,} ,
  have := (DS3 b a c β bcen acirc).2 conb,
  have this1:= (DS3 a b c α acen bcirc).2 cona,
  rw ← this1,rw← this,split, exact M2 b a,
  split,
  intro lol,rw lol at this1,
  have := (M1 a a).2,
  have : length a b = 0 := by finish,
  exact hab ((M1 a b).1 this),
  intro lol, rw lol at this,
  have := (M1 b b).2,
  have : length b a = 0 := by finish,
  exact ne.symm (hab) ((M1 b a).1 this),
end

lemma nonzerolen (a b : point) : a≠ b → 0<length a b :=
begin
  intro hab,
  have lol:= not_imp_not.2 (M1 a b).1 hab,
  have := M5 a b,
  exact (ne.symm lol).le_iff_lt.mp this,
end

lemma offline (a b : point) (L : line) : online a L → online b L → a≠ b → ∃ (c : point), ¬ online c L := --not used
begin
  intros aL bL hab,
  rcases eqtri a b hab with ⟨ c⟩ ,
  use c,
  by_contra cL,
  have := B6 a b c L aL bL cL hab (ne.symm h.2.2.1) (ne.symm h.2.2.2),
  cases this,
  {
    have := DS1 a b c this,
    linarith [h.1, h.2.1,nonzerolen a b hab],
  },
  cases this,
  {
    have := DS1 b a c this,rw M2 at this,
    linarith [h.1, h.2.1,nonzerolen a b hab],
  },
  have := DS1 a c b this,rw M2 c b at this,
  linarith [h.1, h.2.1,nonzerolen a b hab],
end

lemma diffline (a b : point) (L : line) : online a L → online b L → a≠ b → ∃ (M : line), L≠ M ∧ online a L ∧ online a M:=--not used
begin
  intros aL bL hab,
  cases offline a b L aL bL hab with lol hlol,
  rcases LC1 lol a _,
  use w,split,
  {
  intro Lw,rw Lw at hlol, exact hlol h.1,
  },finish,
  intro hyp,rw hyp at hlol,exact hlol aL,
end

lemma twolinenosame (a b : point) (L M : line) : L≠ M → a≠ b → online a L → online b L → online a M → ¬ online b M := --not used
begin
  intros LM hab aL bL aM bM,
  exact LM (G1 a b L M hab aL bL aM bM ),
end

theorem ex (a b c: point)(L: line)(hab: a≠ b) (hbc: b≠ c)(aL: online a L):
  ∃(d : point), online d L ∧ length a d = length b c :=
  begin
    rcases eqtri a b hab with ⟨ d, len1, len2, hda, hdb⟩ ,
    rcases LC1 d a hda with ⟨M, dM, aM ⟩,
    rcases LC1 d b hdb with ⟨N, dN, bN ⟩,
    rcases LC2 b c hbc with ⟨α, bcen, ccirc ⟩,
    rcases I5 b d N α (G3 b α bcen) bN hdb dN with ⟨g,gcirc,gN,Bgbd ⟩ ,
    have hyp : length d g = length d b + length b g := by linarith [DS1 d b g (B1 g b d Bgbd).1],
    rw M2 d b at hyp,rw len2 at hyp,
    have hyp2: length a d < length d g,
    {
      by_contra,push_neg at h,
      have : length b g = 0:= by linarith [M5 b g],
      exact (ne.symm (B1 g b d Bgbd).2.1) ( (M1 b g).1 this),
    }, rw M2 a d at hyp2,
    rcases LC2 d g (ne.symm(B1 g b d Bgbd).2.2.1) with ⟨β,dcen,gcirc2 ⟩,
    rcases I5 a d M β ((DS4 d g a β dcen gcirc2).1 hyp2) aM hda dM with ⟨ f,fcirc,fM,Bfad ⟩ ,
    have key2: length f a = length b g := by linarith [DS1 f a d Bfad,(DS3 d f g β dcen fcirc ).2 gcirc2, M2 d f ],
    have key3:= (DS3 b c g α bcen ccirc).2 gcirc, rw ← key2 at key3,
    rcases LC2 a f (ne.symm (B1 f a d Bfad).2.1) with ⟨γ ,acen2,fcirc3 ⟩ ,
    rcases I2 L γ (Int3 a L γ (G3 a γ acen2) aL) with ⟨ h, hL,hcirc ⟩ ,
    use h,
    split,exact hL,
    rw ← (DS3 a f h γ acen2 fcirc3).2 hcirc,rw M2,finish,
  end

theorem excor (a b c : point)(hab: a≠ b) (hbc: b≠ c) : ∃ (p: point), B a b p ∧ length b p = length c b :=
begin
  rcases LC1 a b hab with ⟨L,aL,bL ⟩ ,
  rcases LC2 b c hbc with ⟨α , bcirc, ccirc⟩ ,
  rcases I5 b a L α (G3 b α bcirc) bL hab aL with ⟨p,pcirc,pL,Bpba ⟩ ,
  use p,split,exact (B1 p b a Bpba).1,
  rw ((DS3 b p c α bcirc pcirc).2 ccirc),
  exact M2 b c,
end

theorem excor2 (a b c d : point)(hab: a≠ b) (hbc: b≠ c)(hcd: c≠ d) :∃ (p: point), B a b p ∧ length b p = length c d :=
begin
  rcases LC1 a b hab with ⟨ L, aL, bL⟩,
  rcases ex b c d L hbc hcd bL with ⟨ p1,p1L,len ⟩ ,
  by_cases b=p1,
  {
    exfalso,
    rw h at len,
    have :length c d =0:= by finish [(M1 p1 p1).2],
    exact hcd ((M1 c d).1 this),
  },
  by_cases hap1: a=p1,
  {
    rcases LC2 b a (ne.symm hab) with ⟨α, bcen, acirc ⟩ ,
    rcases I3 L α (Int3 b L α (G3 b α bcen ) bL) with ⟨e,f ,eL,fL,ecirc,fcirc, hef⟩ ,
    by_cases hyp: a=e,
    {
      use f,
      split,
      {
      exact C1 b a f L α bL aL fL (G3 b α bcen) acirc fcirc (by finish),
      },rw ← hap1 at len,
      have := (DS3 b a f α bcen (by finish)).2 fcirc,finish,
    },use e,
    split,
    {
    exact C1 b a e L α bL aL eL (G3 b α bcen) acirc ecirc hyp,
    },
    have := (DS3 b a e α bcen (by finish)).2 ecirc, finish,
  },
  rcases excor a b p1 hab h with ⟨ p, hypp⟩ ,
  use p, split,exact hypp.1,rw M2 b p1 at len,
  finish,
end

lemma doubleorder (a b : ℝ ) : a ≤ b ∨ b ≤ a :=
begin
  exact le_total a b,
  --wlog h : (a ≤ b ∧ b≤ c) using [a b c, a c b , b a c, b c a, c a b, c b a],
end

lemma tripleorder (a b c : ℝ ) : a ≤  b ∧ b ≤ c ∨ a ≤ c ∧ c ≤ b ∨ b ≤ a ∧ a ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b ∨ c ≤ b ∧ b ≤ a :=
begin
  cases le_total a b;cases le_total a c; cases le_total b c;finish,
end

theorem tan1 (a b c: point) (hab: a≠ b) (hbc: b≠ c): ∃ (α β : circle), ∃ ( d: point), center a α ∧ center d β ∧ oncircle b α
  ∧ oncircle b β ∧ B a b d ∧ length  d b= length c b:=
begin
  let C:= length a b,
  let A:= length b c,
  let B:= length a c,
  wlog h : (A ≤ B ∧ B≤ C) using [A B C, A C B , B A C, B C A, C A B, C B A], exact tripleorder A B C,
  rcases LC2 a b hab with ⟨α, cena, ona ⟩ ,
  use α ,
  rcases excor a b c hab hbc with ⟨ b1, Babb1, len⟩ ,
  rcases LC2 b1 b (ne.symm (B1 a b b1 Babb1).2.2.2.1) with ⟨β, b1circ, bcirc⟩ ,
  use β, use b1,
  split, exact cena,split,exact b1circ,split,exact ona,split,exact bcirc,split,exact Babb1,rw M2 b1 b,assumption,
end

theorem Blem (a b c : point) : B a b c → length a b < length a c ∧ length b c < length a c :=
begin
  intro Babc,have := DS1 a b c Babc,rw ← this,split,
  linarith [(ne.symm (not_imp_not.2 (M1 b c).1 (B1 a b c Babc).2.2.2.1)).le_iff_lt.mp (M5 b c)],
  linarith [(ne.symm (not_imp_not.2 (M1 a b).1 (B1 a b c Babc).2.1)).le_iff_lt.mp (M5 a b)],
end

theorem Blem1 (a b c d : point) : c≠ d → B a b c → B a b d → B b c d ∨ B b d c:=
begin
  intros hcd Babc Babd,
  have := B7 a b c d Babc Babd,
  rcases LC1 a b (B1 a b c Babc).2.1 with ⟨L, aL, bL⟩,
  have := B6 b c d L bL (B2 a b c L Babc aL bL) (B2 a b d L Babd aL bL) (B1 a b c Babc).2.2.2.1 (B1 a b d Babd).2.2.2.1 hcd,
  cases this,left,assumption,cases this_1,exfalso,exact this this_1,right, exact this_1,
end

theorem DS5 (a b c: point) (α : circle) : center a α → oncircle b α → (length a c > length a b ↔ ¬ oncircle c α ∧ ¬ inside c α) :=
begin
  intros acen bcirc,
  split,
  {
    intro len,
    split,
    {
      have : length a b ≠ length a c := by linarith, finish [DS3 a b c α acen bcirc],
    },
    have : length a b ≤   length a c := by linarith,have : ¬ (length a b > length a c) := by finish, finish [DS4 a b c α acen bcirc],
  },

  intro hyp,
  have :length a b ≠ length a c,
  {
    finish [DS3 a b c α acen bcirc],
  },
  have := (DS4 a b c α acen bcirc).1,finish,
end

theorem tan2 (a d c' : point)(had: a≠ d) (hdc: d≠ c')(hac: a≠ c'): ∃ (α β γ : circle),∃ (a1 b1 c1 d1 e1 f1 : point),
  center a1 α ∧ center b1 β ∧ center c1 γ
  ∧ oncircle d1 α ∧ oncircle d1 β ∧ oncircle e1 α ∧ oncircle e1 γ ∧ oncircle f1 β ∧ oncircle f1 γ
  ∧ B a1 d1 b1 ∧ B a1 e1 c1 ∧ B b1 f1 c1
  ∧ length a1 d1 = length a d ∧ length b1 d1 = length d c' ∧ length c1 e1 = length a c' :=
  begin
    rcases tan1 a d c' had hdc with ⟨α,β,b,acen,bcen,dona,donb,Badb,len⟩ ,

    rcases excor2 d a d a (ne.symm had) had (ne.symm had) with ⟨e,Bdae,len2 ⟩,
    rcases excor2 a e a c' (B1 d a e Bdae).2.2.2.1 (ne.symm (B1 d a e Bdae).2.2.2.1) hac with ⟨f,Baef,len3⟩,
    rcases excor2 d b d b (B1 a d b Badb).2.2.2.1 (ne.symm (B1 a d b Badb).2.2.2.1) (B1 a d b Badb).2.2.2.1 with ⟨g,Bdbg,len4 ⟩,
    rcases excor2 b g a c' (B1 d b g Bdbg).2.2.2.1 (B1 g b a (B5 g b d a (B1 d b g Bdbg).1 (B1 a d b Badb).1)).2.2.1 hac with ⟨h,Bbgh,len5⟩ ,
    rcases LC2 a f (B1 a e f Baef).2.2.1 with ⟨δ,acen2,fcirc⟩ ,
    rcases LC2 b h (B1 b g h Bbgh).2.2.1 with ⟨ε,bcen2,hcirc⟩,
    rcases excor2 a d a c' had (ne.symm had) hac with ⟨l,Badl,len6 ⟩,
    have duh : inside f δ ∨ oncircle f δ, right, assumption,
    have key: ¬ inside f ε,
    {
      intro infe,
      have key:= (DS4 b h f ε bcen2 hcirc).2 infe,
      rw ← (DS1 b g h Bbgh) at key, rw len4 at key,rw M2 d b at key, rw len at key,rw len5 at key, rw M2 b f at key,
      rw←  DS1 f a b (B5 f a d b ((B1 d a f (B5 d a e f Bdae Baef)).1) Badb) at key, rw M2 f a at key,
      rw ← DS1 a e f Baef at key, rw len2 at key,rw len3 at key,rw ←  DS1 a d b Badb at key, rw M2 at key, rw M2 d b at key,
      rw len at key,linarith [nonzerolen a d had],
    },
    have key2: intercirclecircle δ ε,
    {
      by_cases hbl: b=l,
      {
        have lol:= DS1 a d b Badb, rw hbl at lol , rw len6 at lol,rw M2 a d at lol,
        have := DS1 a e f Baef,rw len3 at this,rw len2 at this,rw lol at this,rw hbl at bcen2,
        exact Int4 l f δ ε ((DS3 a f l δ acen2 fcirc).1 (eq.symm this)) duh (G3 l ε  bcen2) key,
      },
      have lol:= DS1 a d l Badl,rw len6 at lol,
      have := DS1 a e f Baef,rw len2 at this, rw len3 at this,rw M2 at this, rw this at lol,
      have key2:= Blem1 a d b l hbl Badb Badl,
      cases key2,
      {
        have := DS1 d b l key2,rw M2 d b at this,rw len at this,rw len6 at this,
        have lol2:=(DS1 b g h Bbgh),rw len4 at lol2,rw M2 d b at lol2, rw len at lol2,rw len5 at lol2, rw ← this at lol2,
        have : length b l < length b h := by linarith [nonzerolen c' d (ne.symm hdc)],
        exact Int4 l f δ ε ((DS3 a f l δ acen2 fcirc).1 lol) duh ((DS4 b h l ε bcen2 hcirc).1 this) key,
      },
      {
        have := DS1 d l b key2,rw M2 d b at this,rw len at this,rw len6 at this,
        have lol2:=(DS1 b g h Bbgh),rw len4 at lol2,rw M2 d b at lol2, rw len at lol2,rw len5 at lol2, rw ← this at lol2,
        have : length l b < length b h := by linarith [nonzerolen a c' hac], rw M2 l b at this,
        exact Int4 l f δ ε ((DS3 a f l δ acen2 fcirc).1 lol) duh ((DS4 b h l ε bcen2 hcirc).1 this) key,
      },
    },
    rcases I6 δ ε key2 with ⟨c,cdel,cep ⟩,
    have hac1 : a ≠ c,
    {
      intro hac, rw hac at acen2,
      exact (G4 c δ (G3 c δ acen2)) cdel,
    },
    rcases LC1 a c hac1 with ⟨L,aL, cL ⟩ ,
    have := Int3 a L α  (G3 a α  acen) aL,

    have := (DS3 a c f δ acen2 cdel).2 fcirc,rw ← DS1 a e f Baef at this, rw len2 at this, rw len3 at this,
    have : length a c > length d a := by linarith [nonzerolen a c' hac],
    have key5:= (DS5 a d c α acen dona).1, rw M2 a d at key5,

    rcases I4 a c L α  (G3 a α  acen) aL (key5 this).2 (key5 this).1 cL with ⟨j,jcirc,jL,Bajc ⟩ ,
    rcases LC2 c j (ne.symm  (B1 a j c Bajc).2.2.2.1) with ⟨γ, ccen, jcirc2 ⟩ ,
      have hbc : b ≠ c,
    {
      intro hbc, rw hbc at bcen2,
      exact (G4 c ε  (G3 c ε  bcen2)) cep,
    },
    rcases LC1 b c hbc with ⟨M,bM, cM ⟩ ,
    have := Int3 b M β   (G3 b β bcen) bM,

    have := (DS3 b c h ε  bcen2 cep).2 hcirc,rw ← DS1 b g h Bbgh at this, rw len4 at this, rw len5 at this,
    have : length b c > length d b := by linarith [nonzerolen a c' hac],
    have key5:= (DS5 b d c β bcen donb).1, rw M2 b d at key5,

    rcases I4 b c M β   (G3 b β   bcen) bM (key5 this).2 (key5 this).1 cM with ⟨k,kcirc,kM,Bbkc ⟩ ,
    rcases LC2 c k (ne.symm  (B1 b k c Bbkc).2.2.2.1) with ⟨γ1 , ccen1, kcirc1 ⟩ ,

    have := DS1 a j c Bajc, rw (DS3 a j d α acen jcirc).2 dona at this, rw (DS3 a c f δ acen2 cdel).2 fcirc at this,
    rw ← DS1 a e f Baef at this, rw len2 at this, rw len3 at this,rw M2 a d at this,
    have key3: length j c = length a c' := by linarith,

    have := DS1 b k c Bbkc, rw (DS3 b k d β  bcen kcirc).2 donb at this, rw (DS3  b c h ε  bcen2 cep).2 hcirc at this,
    rw ← DS1 b g h Bbgh at this, rw len at this, rw len4 at this,rw len5 at this, rw M2 d b at this, rw len at this,
    have key4: length j c = length k c := by linarith,rw M2 at key4, rw M2 k c at key4,

    have := DS2 c j k γ γ1 ccen ccen1 jcirc2 kcirc1 key4, rw ← this at kcirc1,

    use α,use β,use γ,use a,use b,use c,use d,use j, use k,
    split, exact acen,split, exact bcen,split, exact ccen,split, exact dona,split, exact donb,
    split, exact jcirc,split, exact jcirc2,split, exact kcirc,split, exact kcirc1,split, exact Badb,
    split, exact Bajc,split, exact Bbkc, split, refl, rw M2 d c', split, exact len,rw M2 c j,exact key3,
  end

theorem tan3 (a' b' c' a b c d e f: point)(α β γ : circle) : a'≠ b' → b'≠ c' → a'≠ c'
→ center a α → center b β → center c γ → oncircle d α → oncircle d β → oncircle e α → oncircle e γ
→ oncircle f β → oncircle f γ → B a d b → B a e c→ B b f c
→ length a d = length a' b' → length b d = length b' c' → length c e = length a' c'
→ ∃ (z g h i: point),∃ (ζ : circle), center z ζ ∧ oncircle g α ∧ oncircle g ζ ∧ oncircle h β  ∧ oncircle h ζ
∧ oncircle i γ ∧ oncircle i ζ ∧ B a g z ∧ B b h z ∧ B c i z :=
begin
intros hab1 hbc1 hac1 acen bcen ccen dcirca dcircb ecirca ecircc fcircb fcircc Badb Baec Bbfc len1 len2 len3,

rcases LC1 d f _ with ⟨L,dL,fL ⟩,
end
