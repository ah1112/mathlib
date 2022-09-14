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
(rightangle : real)
(area : point → point → point → real)

(P1 : ∀ (S: set point), ∃ (a : point) , a∉ S) --Does not work for S=everything. What to do?
(P2 : ∀ (L :  line), ∃ (a: point ), online a L)
(P3 : ∀ (L : line) , ∀ (b c : point), online b L→ online c L→b≠ c→ ∃ (a : point), online a L ∧  B b a c)
(P4 : ∀ (L : line), ∀ (b c : point), online b L → online c  L → b≠ c→ ∃ (a : point), B b c a)
(P5: ∀ (L : line), ∀ (b : point), ¬ online b L → ∃ (a: point), a≠ b ∧ sameside a b L)
(P6: ∀ (L : line), ∀ (b : point), ¬ online b L → ∃ (a: point), ¬ sameside a b L)
(P7: ∀ (α : circle), ∃ (a : point), oncircle a α)
(P8: ∀ (α : circle), ∃ (a : point), inside a α)
(P9: ∀ (α : circle), ∃ (a : point), ¬ inside a α ∧ ¬ oncircle a α )

(LC1: ∀ {a b : point}, a≠ b→ ∃ (L:line), online a L ∧ online b L)
(LC2: ∀ {a b : point}, a≠ b→ ∃ (α : circle), center a α ∧ oncircle b α )

(I1: ∀ (L M : line), interlineline L M → ∃ (a: point), online a L ∧ online a M)
(I2: ∀ {L : line}, ∀ {α : circle},interlinecircle L α → ∃ (a : point), online a L ∧ oncircle a α ) --Should be proven
(I3: ∀ {L : line}, ∀ {α : circle},interlinecircle L α → ∃ (a b : point), online a L ∧ online b L
  ∧ oncircle a α ∧ oncircle b α ∧ a≠ b)
(I4: ∀ (b c : point), ∀ (L : line), ∀ (α : circle), inside b α → online b L → ¬ inside c α →
  ¬ oncircle c α → online c L →∃ (a : point), oncircle a α ∧ online a L∧ B b a c)
(I5: ∀ {b c : point}, ∀ {L: line}, ∀ {α : circle}, inside b α → online b L → c≠ b → online c L →
  ∃ (a : point), oncircle a α ∧ online a L ∧ B a b c)
(I6: ∀ {α β : circle}, intercirclecircle α β → ∃ (a : point), oncircle a α ∧ oncircle a β) --can be proven
(I7: ∀ {α β : circle}, intercirclecircle α β → ∃ (a b: point), oncircle a α ∧ oncircle a β ∧ oncircle b α ∧ oncircle b β∧ a≠ b)
(I8: ∀ (b c d : point), ∀ (α β : circle), ∀ (L : line), intercirclecircle α β → center c α → center d β
 → online c L → online d L → ¬ online b L → ∃ (a : point), oncircle a α ∧ oncircle a β ∧ sameside a b L)
(I9: ∀ (b c d : point), ∀ (α β : circle), ∀ (L : line), intercirclecircle α β → center c α → center d β
 → online c L → online d L → ¬ online b L → ∃ (a : point), oncircle a α ∧ oncircle a β ∧ ¬ sameside a b L∧ ¬ online a L)

(G1: ∀ (a b : point), ∀ (L M: line), a≠ b →  online a L → online b L → online a M → online b M → L=M)
(G2: ∀ (a b : point), ∀ (α : circle), center a α → center b α → a=b) --should be proven?
(G3: ∀ {a : point}, ∀ {α : circle}, center a α → inside a α )
(G4: ∀ (a : point), ∀ (α : circle), inside a α → ¬ oncircle a α )

(B1: ∀ {a b c : point}, B a b c → B c b a ∧ a≠ b ∧ a≠ c ∧ b ≠ c∧ ¬  B b a c) -- slightly modified, hope no issue?
(B2: ∀ {a b c : point}, ∀ {L : line}, B a b c→ online a L → online b L → online c L)
(B3: ∀ (a b c : point), ∀ (L : line), B a b c→ online a L → online c L → online b L)--can be proven?
(B4: ∀ (a b c d : point), B a b c→ B a d b → B a d c)
(B5: ∀ (a b c d : point), B a b c→ B b c d → B a b d)
(B6: ∀ {a b c : point}, ∀ {L : line}, online a L → online b L → online c L → a≠ b → a≠ c → b≠ c → B a b c ∨ B b a c ∨ B a c b)
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

(C1: ∀ {a b c : point}, ∀ {L: line}, ∀ {α : circle }, online a L → online b L → online c L
  → inside a α → oncircle b α → oncircle c α → b≠ c→ B b a c)
(C2: ∀ (a b c : point), ∀ (α : circle), inside a α ∨ oncircle a α → inside b α ∨ oncircle b α → B a c b → inside c α)
(C3: ∀ (a b c : point), ∀ (α : circle), inside a α ∨ oncircle a α → ¬ inside c α → B a c b → ¬ inside b α ∧ ¬ oncircle b α)
(C4: ∀ (a b c d : point), ∀ (α β : circle), ∀ (L : line), α ≠ β → c≠ d→ intercirclecircle α β → oncircle c α
  → oncircle c β → oncircle d α → oncircle d β → center a α → center b β → online a L → online b L → ¬ sameside c d L)

(Int1: ∀ (a b : point), ∀ (L M : line), ¬ sameside a b L → online a M → online b M → interlineline L M)
(Int2: ∀ (a b : point), ∀ (L : line), ∀ (α : circle ), inside a α ∨ oncircle a α → inside b α ∨ oncircle b α
  → ¬ sameside a b L → interlinecircle L α )
(Int3: ∀ {a : point}, ∀ {L: line}, ∀ {α : circle}, inside a α → online a L → interlinecircle L α )
(Int4: ∀ (a b : point), ∀ (α β : circle), oncircle a α → inside b α ∨ oncircle b α → inside a β →  ¬ inside b β
  → intercirclecircle α β )
(Int5: ∀ {a b : point}, ∀ {α β : circle}, inside a α → oncircle b α → inside b β → oncircle a β → intercirclecircle α β )

(M1: ∀ {a b : point}, length a b = 0 ↔ a =b)
(M2: ∀ (a b : point), length a b = length b a)
(M3: ∀ (a b c : point), a≠ b→ a≠c → angle a b c = angle c b a)
(M4: ∀ (a b c : point), angle a b c ≤ 2*rightangle ∧ 0 ≤ angle a b c)
(M5: ∀ (a b : point), 0 ≤ length a b)
--(M6: 0 < rightangle) I believe this can be deduced from M4 together with A1 (there exist nonzero angles)
(M6: ∀ (a b : point), area a a b = 0)
(M7: ∀ (a b c : point), 0 ≤ area a b c)
(M8: ∀ (a b c : point), area a b c = area c a b ∧ area a b c = area a c b)
(M9: ∀ (a b c a1 b1 c1 : point), length a b = length a1 b1 → length b c = length b1 c1 → length c a = length c1 a1
  → angle a b c = angle a1 b1 c1 → angle b a c = angle b1 a1 c1 → angle a c b = angle a1 c1 b1 → area a b c = area a1 b1 c1)

(DS1: ∀ {a b c : point}, B a b c → length a b + length b c = length a c)
(DS2: ∀ {a b c : point}, ∀ {α β : circle}, center a α → center a β → oncircle b α → oncircle c β → length a b = length a c → α =β )
(DS3: ∀ {a b c : point}, ∀ {α : circle}, center a α → oncircle b α → (length a b = length a c ↔ oncircle c α))
(DS4: ∀ {a b c : point}, ∀ {α : circle}, center a α → oncircle b α → (length a c < length a b ↔ inside c α))

(A1: ∀ (a b c : point), ∀ (L: line), a≠ b → a≠ c→ online a L → online b L → (online c L ∧ ¬ B b a c ↔ angle b a c =0))
(A2: ∀ (a b c d : point), ∀ (L M : line), online a L → online b L → online a M → online c M → a ≠ b → a≠ c
  → ¬ online d M → ¬ online d L → L≠ M → angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L)
(A3: ∀ (a b c d : point), ∀ (L : line), online a L → online b L → B a c b → ¬ online d L → angle a c d = angle d c b ↔ angle a c d =rightangle)
(A4: ∀ {a b c a1 b1 c1 : point},∀ {L M: line}, online a L → online b L→ online b1 L → online a M→ online c M
   → online c1 M → b≠ a → b1≠ a → c≠ a → c1≠ a → ¬ B b a b1 → ¬ B c a c1 → angle b a c = angle b1 a1 c1)
(A5: ∀ (a b c d : point), ∀ (L M N : line), online a L → online b L → online b M → online c M → online c N → online d N → b ≠ c
  → sameside a d N → angle a b c + angle b c d < 2*rightangle → ∃ (e : point), online e L ∧ online e N ∧ sameside e a M)

(DA1: ∀ (a b c : point), ∀(L : line), online a L → online b L → a≠ b → (area a b c = 0 ↔ online c L))
(DA2: ∀ (a b c d: point), ∀ (L : line), a≠ b → b≠ c → c ≠ a → online a L → online b L → online c L → ¬ online d L
  → (B a c b ↔ area a c d + area d c b = area a d b))

(S: ∀ {a b c d e f : point}, length a b = length d e → length a c = length d f → (angle b a c = angle e d f ↔
 length b c = length e f)) --Euclid Prop 4,8

open incidence_geometry

variables[AxA: incidence_geometry]

include AxA

theorem flip1 {a b c d : point}(abcd: length a b = length c d) : length b a = length c d :=by rwa M2 a b at abcd
theorem flip2 {a b c d : point}(abcd: length a b = length c d) : length a b = length d c :=(flip1 abcd.symm).symm
theorem flipboth {a b c d : point}(abcd: length a b = length c d): length b a = length d c :=flip2 (flip1 abcd)

theorem Beasy (a b : point) : ¬ B a b a ∧ ¬ B a a b :=⟨  λ Baba, (B1 Baba).2.2.1 rfl,λ Baab, (B1 Baab).2.1 rfl⟩

theorem A4mod {a b c b1 c1 : point} (Babb1: B a b b1) (Bacc1 : B a c c1): angle b a c = angle b1 a c1 :=
begin
  rcases LC1 (B1 Babb1).2.1 with ⟨L, aL, bL⟩ ; rcases LC1 (B1 Bacc1).2.1 with ⟨M, aM, cM⟩ ,
  exact A4 aL bL (B2 Babb1 aL bL) aM cM (B2 Bacc1 aM cM) (B1 Babb1).2.1.symm (B1 Babb1).2.2.1.symm (B1 Bacc1).2.1.symm
    (B1 Bacc1).2.2.1.symm (B1 Babb1).2.2.2.2 (B1 Bacc1).2.2.2.2,
end

theorem A4mod1 {a b c b1 : point} (ac: a≠ c) (Babb1 : B a b b1): angle b a c = angle b1 a c :=
begin
  rcases LC1 (B1 Babb1).2.1 with ⟨L, aL, bL⟩ ,rcases LC1 ac with ⟨M, aM, cM⟩ ,
  exact A4 aL bL (B2 Babb1 aL bL) aM cM cM (B1 Babb1).2.1.symm (B1 Babb1).2.2.1.symm ac.symm ac.symm (B1 Babb1).2.2.2.2 (Beasy c a).1,
end

theorem sss {a b c d e f : point} (lab : length a b = length d e) (lbc: length b c = length e f) (lac: length a c = length d f):
   angle a b c = angle d e f ∧ angle b a c = angle e d f ∧ angle a c b = angle d f e
   := ⟨(S (flipboth lab) lbc).2 lac,(S lab lac).2 lbc,(S (flipboth lac) (flipboth lbc)).2 lab ⟩

theorem sas {a b c d e f : point} (ab: length a b = length d e )(ac: length a c = length d f)(Abac: angle b a c = angle e d f):    --Euclid I.4
 length b c = length e f ∧ angle a b c = angle d e f ∧ angle a c b = angle d f e
 :=⟨(S ab ac).1 Abac,(sss ab ((S ab ac).1 Abac) ac).1, (sss ab ((S ab ac).1 Abac) ac).2.2⟩

def iseqtri (a b c : point) : Prop := length a b = length a c  ∧ length b c = length b a∧ length c a = length c b ∧ a≠ b ∧ b≠ c∧ c≠ a

lemma makeeqtriaux {a b c : point} (hab : a≠ b) (h1: length a b = length a c) (h2: length b c = length b a):b≠ c ∧ c≠ a :=
begin
split,
intro bc,rw M1.mpr bc at h2,
exact hab (M1.mp h2.symm).symm,
intro ca,rw M1.mpr ca.symm at h1,
exact hab (M1.mp h1),
end

theorem makeeqtri {a b : point} (hab : a≠ b): ∃ (c : point), iseqtri a b c := --Euclid 1.1
begin
  rcases LC2 hab with ⟨α, acen, bcirc⟩ ,rcases LC2 (ne.symm hab) with ⟨β, bcen, acirc ⟩,
  rcases I6 (Int5 (G3 acen) bcirc (G3 bcen) acirc) with ⟨c,cona,conb ⟩ ,
  use c,
  have abeqac:= (DS3 acen bcirc).2 cona,
  have bceqba:= (DS3 bcen conb).mpr acirc,
  have caeqcb: length c a = length c b:= flip1 ((rfl.congr (eq.symm (flipboth bceqba))).mp (eq.symm abeqac)),
  exact ⟨abeqac,bceqba,caeqcb,hab,makeeqtriaux hab abeqac bceqba ⟩,
end

theorem makeeqtri1 {a b : point} (hab : a≠ b): ∃ (c d: point), iseqtri a b c ∧ iseqtri a b d ∧ c≠ d:= --Euclid 1.1
begin
  rcases LC2 hab with ⟨α, acen, bcirc⟩,rcases LC2 (ne.symm hab) with ⟨β, bcen, acirc ⟩,
  rcases I7 (Int5 (G3 acen) bcirc (G3 bcen) acirc) with ⟨c,d,cona,conb,dona,donb,cd ⟩ ,
  use c,use d,
  have abeqac:= (DS3 acen bcirc).2 cona,have abeqad:= (DS3 acen bcirc).2 dona,
  have bceqba:= (DS3 bcen conb).mpr acirc,have bdeqba:= (DS3 bcen donb).mpr acirc,
  have caeqcb:= flip1 ((rfl.congr (eq.symm (flipboth bceqba))).mp (eq.symm abeqac)),have daeqdb:= flip1 ((rfl.congr (eq.symm (flipboth bdeqba))).mp (eq.symm abeqad)),
  exact ⟨⟨abeqac,bceqba,caeqcb,hab,makeeqtriaux hab abeqac bceqba ⟩ ,⟨abeqad,bdeqba,daeqdb,hab,makeeqtriaux hab abeqad bdeqba⟩ ,cd ⟩ ,
  end

lemma nonzerolen {a b : point}(hab : a≠ b) : 0<length a b := (ne.symm (not_imp_not.2 M1.1 hab)).le_iff_lt.mp (M5 a b)

lemma nonzerolenconv {a b : point} (len : 0 < length a b) : a≠ b :=
begin
  intros ab,rw ab at len,have : b=b := rfl,linarith [M1.mpr this],--ask about
end

lemma DS1rev {a b c : point} {L : line}(ab : a≠ b) (bc: b≠ c) (ac : a≠ c) (aL : online a L) (bL : online b L) (cL : online c L) (len: length a b + length b c ≤ length a c): B a b c :=
begin
  have Bs:= B6 aL bL cL ab ac bc,cases Bs,assumption,cases Bs,
  have := DS1 Bs, rw M2 at this, linarith[nonzerolen ab],
  have := DS1 Bs, rw M2 c b at this,linarith[nonzerolen bc],
end
/-
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
-/
theorem ex {a b c: point}{L: line}(hab: a≠ b) (hbc: b≠ c)(aL: online a L):∃(d : point), online d L ∧ length a d = length b c := --Euclid 1.2,3 (generalizations and corrollaries)
  begin
    rcases makeeqtri hab with ⟨d, len1, len2, len3,hab, hbd, hda⟩,
    rcases LC1 hda with ⟨M, dM, aM ⟩, rcases LC1 hbd.symm with ⟨N, dN, bN ⟩,rcases LC2 hbc with ⟨α, bcen, ccirc ⟩,
    rcases I5 (G3 bcen) bN hbd.symm dN with ⟨g,gcirc,gN,Bgbd ⟩ ,
    have hyp : length d g = length d b + length b g := by linarith [DS1 (B1 Bgbd).1],rw M2 d b at hyp,rw len2 at hyp,
    have hyp2: length a d < length d g,
    {
      by_contra,push_neg at h,
      have : length b g = 0:= by linarith [M5 b g, flipboth len3],
      exact (ne.symm (B1 Bgbd).2.1) (M1.mp this),
    }, rw M2 a d at hyp2,
    rcases LC2 (ne.symm(B1 Bgbd).2.2.1) with ⟨β,dcen,gcirc2 ⟩,
    rcases I5 ((DS4 dcen gcirc2).1 hyp2) aM hda dM with ⟨ f,fcirc,fM,Bfad ⟩ ,
    have key2: length f a = length b g := by linarith [DS1 Bfad,(DS3 dcen fcirc).2 gcirc2, M2 d f,flipboth len3],
    have key3:= (DS3 bcen ccirc).2 gcirc, rw ← key2 at key3,
    rcases LC2 (ne.symm (B1 Bfad).2.1) with ⟨γ ,acen2,fcirc3 ⟩ ,
    rcases I2 (Int3 (G3 acen2) aL) with ⟨ h, hL,hcirc ⟩,
    use h,split,exact hL,rw ← (DS3 acen2 fcirc3).2 hcirc,rw M2,linarith,
  end

theorem excor {a b c : point}(hab: a≠ b) (hbc: b≠ c) : ∃ (p: point), B a b p ∧ length b p = length c b :=
begin
  rcases LC1 hab with ⟨L,aL,bL ⟩ ,
  rcases LC2 hbc with ⟨α , bcirc, ccirc⟩ ,
  rcases I5 (G3 bcirc) bL hab aL with ⟨p,pcirc,pL,Bpba ⟩ ,
  use p,split,exact (B1 Bpba).1,
  rw ((DS3 bcirc pcirc).2 ccirc),exact M2 b c,
end

theorem excor2 {a b c d : point}(hab: a≠ b) (hbc: b≠ c)(hcd: c≠ d) :∃ (p: point), B a b p ∧ length b p = length c d :=
begin
  rcases LC1 hab with ⟨ L, aL, bL⟩,
  rcases ex hbc hcd bL with ⟨ p1,p1L,len ⟩ ,
  by_cases b=p1, { exfalso,rw h at len,exact hcd ((M1 c d).1 (by linarith [(M1 p1 p1).2 rfl])), },
  by_cases hap1: a=p1,
  {
    rcases LC2 (ne.symm hab) with ⟨α, bcen, acirc ⟩ ,
    rcases I3 (Int3 (G3 bcen ) bL) with ⟨e,f ,eL,fL,ecirc,fcirc, hef⟩ ,
    by_cases hyp: a=e,
    {
      use f,split,rw ← hyp at hef,{exact C1 bL aL fL (G3 bcen) acirc fcirc hef,},
      rw ← hap1 at len,linarith[(DS3 bcen acirc).2 fcirc],
    },use e,
    split,exact C1 bL aL eL (G3 bcen) acirc ecirc hyp,rw← ((DS3 bcen acirc).2 ecirc),rwa← hap1 at len,
  },
  rcases excor hab h with ⟨p, hypp⟩ ,
  use p, split,exact hypp.1,linarith[hypp.2,flip1 len],
end

theorem excor3 (a b c d : point) : a≠ d → c≠ d→ length c d < length a b → ∃ (p : point), B a p b ∧ length a p = length c d :=
begin
  intros ad cd big,
  rcases LC1 (nonzerolenconv a b (by linarith [M5 c d])) with ⟨L, aL, bL ⟩ ,
  rcases P4 L b a bL aL (nonzerolenconv a b (by linarith [M5 c d])).symm with ⟨q, Bbaq⟩ , --is this axiom useless?
  rcases excor q a d (B1 Bbaq).2.2.2.1.symm ad with ⟨p,Bqap,len ⟩, rw M2 d a at len,

  have pL :=(B2 Bqap (B2 Bbaq bL aL) aL),

  by_cases a = c,
  have bp: b≠ p,
  {
    intro bp, rw bp at big,rw ← h at big, linarith,
  },
  rw ← h at big, rw ← len at big,
  have key:= B6 a b p L aL bL pL (B1 Bbaq).2.1.symm (B1 Bqap).2.2.2.1 bp,
  cases key,
  linarith [DS1 _ _ _ key,nonzerolen b p (B1 key).2.2.2.1],cases key, exfalso,
  exact (B7 q a p b Bqap (B1 Bbaq).1) (B1 key).1,
  use p,split,assumption,finish,
  --same as above but with a≠ c
  rcases excor2 q a c d (B1 Bbaq).2.2.2.1.symm h cd with ⟨p,Bqap,len ⟩,
  rw ← len at big,
  have bp: b≠ p,
  {
    intro bp,rw bp at big, linarith,
  },
  have pL :=(B2 Bqap (B2 Bbaq bL aL) aL),
  have key:= B6 a b p L aL bL pL (B1 Bbaq).2.1.symm (B1 Bqap).2.2.2.1 bp,
  cases key,
  linarith [DS1 _ _ _ key,nonzerolen b p (B1 key).2.2.2.1],cases key, exfalso,
  exact (B7 q a p b Bqap (B1 Bbaq).1) (B1 key).1,
  use p,split,assumption,finish,
end

theorem isoangle (a b c: point) : a≠ b → b≠ c → length a b = length a c →
 angle a b c = angle a c b  := -- Euclid I.5 (part 1)
begin
  intros ab bc labac,
  exact (sas a b c a c b labac labac.symm (M3 b a c ab.symm bc)).2.2.symm,
end

theorem Beasy2 (a b c d e: point) (L : line) : b≠ d → online a L → online b L → ¬ online d L→ B a b c → B a d e → b≠e :=
begin
  intros bd aL bL dL Babc Bade be,
  rw ← be at Bade,
  have := B3 a d b L Bade aL bL,finish,
end

theorem Beasy3 (a b c : point) : B a b c → ∃ (L : line), online a L∧ online b L∧ online c L ∧ a≠ b ∧ b≠ c ∧ c≠ a:=
begin
  intro Babc,
  rcases LC1 (B1 Babc).2.1 with ⟨L,aL,bL ⟩,
  have := B2 Babc aL bL,have := B1 Babc,finish,
end

theorem Beasy4 (a b c : point) : ¬ B a b c →  ¬ B c b a :=
begin
intros Babc Bcba,have := B1 Bcba,finish,
end

theorem Beasy5 (a b c d: point) : c≠ d → B a b c → B a b d → B b c d ∨ B b d c :=
begin
  intros cd Babc Babd,
  rcases Beasy3 a b c Babc with ⟨L,aL,bL,cL,ab, bc,ca ⟩,
  have dL:= B2 Babd aL bL,
  have key:= B6 b c d L bL cL dL bc (B1 Babd).2.2.2.1 cd,
  cases key,left,assumption,cases key,
  have := B7 a b c d Babc Babd,finish,right, assumption,
end

/-
theorem Beasy5 (a b c d: point) : c≠ d → B a b c → B a b d → B a c d ∨ B a d c :=
begin
  intros cd Babc Babd,
  rcases Beasy3 a b c Babc with ⟨L,aL,bL,cL,ab, bc,ca ⟩,
  have dL:= B2 a b d L Babd aL bL,
  have key:= B6 a c d L aL cL dL ca.symm (B1 a b d Babd).2.2.1 cd,
  cases key,left,assumption,cases key,
  have := DS1 c a d key,
  have := DS1 a b c Babc,
  have := DS1 a b d Babd, have:= (B1 c a d key).1,
  end
-/

theorem isoangleext (a b c d e : point) (L : line): b≠ c → online a L → online b L → ¬ online c L→ B a b d → B a c e → length a b = length a c → length a d = length a e→
 angle c b d = angle b c e := -- Euclid I.5 (part 2)
begin
  intros bc aL bL cL Babd Bace labac ladae,
  have prev:= sas a b c a c b labac labac.symm (M3 b a c (B1 Babd).2.1.symm bc),
  have key:= A4mod1 a b c d (B1 Bace).2.1 Babd,
  have key1:= A4mod1 a c b e (B1 Babd).2.1 Bace,
  rw M3 b a c (B1 Babd).2.1.symm bc at key, rw key at key1,
  rcases LC1 (B1 Bace).2.2.1 with ⟨M, aM,eM⟩,
  have lol:= B3 a c e M Bace aM eM,
  have : ¬ online b M,
  {
    intro bM,
    have := G1 a b L M (B1 Babd).2.1 aL bL aM bM,rw this at cL,
    finish,
  },
  have lol3:= Beasy2 a c e b d M bc.symm aM lol this Bace Babd,
  have lol4:= Beasy2 a b d c e L bc aL bL cL Babd Bace,

  have := M3 d a c (B1 Babd).2.2.1.symm lol3.symm, rw (this) at key1,
  have := M3 e a b (B1 Bace).2.2.1.symm lol4.symm, rw this at key1,

  have lol2:= sas a c d a b e labac.symm ladae key1,
  exact (sss b c d c b e (prev.1) lol2.1 (by linarith[DS1 a b d Babd,DS1 a c e Bace])).2.1,
end

theorem isosidelem (a b c : point) (L : line) : a≠ b → b≠ c → c≠ a → online a L → online b L
→ angle a b c = angle a c b → ¬ B b a c → ¬ online c L :=
begin
  intros ab bc ca aL bL ang Bbac cL,
  have Bet:=  B6 a b c L aL bL cL ab ca.symm bc,cases Bet,
    {
      have : online b L ∧ ¬ B a c b,split,exact bL, exact Beasy4 b c a (B1 (B1 Bet).1).2.2.2.2,
      have :=(A1 c a b L ca bc.symm cL aL).1 this,rw this at ang,
      have := not_imp_not.2 (A1 b a c L ab.symm bc bL aL).2,push_neg at this,finish,
    },
    cases Bet,
    {
      exact Bbac Bet,
    },
    have : online c L ∧ ¬ B a b c,split,exact cL, exact Beasy4 c b a (B1 (B1 Bet).1).2.2.2.2,
    have := (A1 b a c L ab.symm bc bL aL).1 this ,rw this at ang,
    have :=not_imp_not.2 (A1 c a b L ca bc.symm cL aL).2, push_neg at this,finish,
end

theorem isoside (a b c : point) :¬ B b a c→  a≠ b → b≠ c → c≠ a → angle a b c = angle a c b → length a b = length a c:=
begin--Euclid I.6
  intros Bbac ab bc ca ang,
  have := nonzerolen a b ab,
  have := nonzerolen a c ca.symm,
  wlog h : (length a c ≤ length a b) using [b c, c b], exact le_total (length a c) (length a b),
  by_cases h_1:length a c = length a b, linarith,
  have big : length a c < length a b := (ne.le_iff_lt h_1).mp h, rw M2 a b at big,
  rcases excor3 b a a c bc ca.symm big with ⟨d,Bbda,bdac⟩,
  rw M2 a c at bdac,
  have dbcacb:= A4mod1 b d c a bc Bbda, rw ang at dbcacb,

  have eq:=sas  c a b  b d c bdac.symm (M2 c b) dbcacb.symm,
  rcases Beasy3 b d a Bbda with ⟨L,bL,dL,aL,bd,da,ab⟩,
  have := (DA2 b a d c L ab.symm da.symm bd.symm bL aL dL (isosidelem a b c L ab bc ca aL bL ang Bbac)).1 Bbda,

  have key:= M9 c a b b d c bdac.symm eq.1 (M2 b c) eq.2.1 dbcacb.symm eq.2.2,rw ← key at this,
  rw (M8 c a b).1 at this,simp at this, rw ← (M8 d a c).1 at this,exfalso,
  exact (isosidelem a b c L ab bc ca aL bL ang Bbac) ((DA1 d a c L dL aL da).1 this),

  exact (this (Beasy4 b a c Bbac) ca.symm bc.symm ab.symm ang.symm this_2 this_1).symm,
end

theorem bisang (a b c : point) : a≠ b → a≠ c → ∃(f : point), angle b a f = angle c a f := --Euclid I.9
begin
  intros ab ac,
  rcases excor2 a b a c ab ab.symm ac with ⟨d, Babd, bdac⟩,
  rcases excor2 a c a b ac ac.symm ab with ⟨e, Bace, ceab⟩,
  by_cases d=e,
  {
    rw h at Babd,
    use e,
    rcases Beasy3 a b e Babd with ⟨L,aL,bL,eL,ab,be,ea⟩,
    have := (A1 a b e L ab ea.symm aL bL).1 _,
    have := (A1 a c e L (B1 Bace).2.1 ea.symm aL (B3 a c e L Bace aL eL)).1 _,linarith,split,assumption,
    exact (B1 Bace).2.2.2.2,split,assumption,exact (B1 Babd).2.2.2.2,
  },
  rcases makeeqtri1 d e h with ⟨f, f1,eqtri,eqtri1,ff1 ⟩,dsimp [iseqtri] at eqtri,dsimp [iseqtri] at eqtri1,
  by_cases a=f,
  {
  have af1: a≠ f1 := by finish,
    use f1,
  have key: length a d = length a e,
  {
    have := DS1 a b d Babd,
    have := DS1 a c e Bace,linarith,
  },
  rw M2 f1 d at eqtri1 , rw M2 f1 e at eqtri1,
  have ang:= (sss a d f1 a e f1 key (eqtri1.2.2.1) rfl).2.1,

  have := A4mod1 a b f1 d af1 Babd,
  have := A4mod1 a c f1 e af1 Bace,linarith,
  },
  use f,
  have key: length a d = length a e,
  {
    have := DS1 a b d Babd,
    have := DS1 a c e Bace,linarith,
  },
  rw M2 f d at eqtri , rw M2 f e at eqtri,
  have ang:= (sss a d f a e f key (eqtri.2.2.1) rfl).2.1,

  have := A4mod1 a b f d h Babd,
  have := A4mod1 a c f e h Bace,linarith,
end



lemma tripleorder (a b c : ℝ ) : a ≤  b ∧ b ≤ c ∨ a ≤ c ∧ c ≤ b ∨ b ≤ a ∧ a ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b ∨ c ≤ b ∧ b ≤ a :=
begin
  cases le_total a b;cases le_total a c; cases le_total b c;finish,
end

theorem tan1 (a b c: point) (hab: a≠ b) (hbc: b≠ c): ∃ (α β : circle), ∃ ( d: point), center a α ∧ center d β ∧ oncircle b α
  ∧ oncircle b β ∧ B a b d ∧ length  d b= length c b:=
begin
  rcases LC2 hab with ⟨α, cena, ona ⟩ ,
  use α ,
  rcases excor a b c hab hbc with ⟨ b1, Babb1, len⟩ ,
  rcases LC2 (ne.symm (B1 Babb1).2.2.2.1) with ⟨β, b1circ, bcirc⟩ ,
  use β, use b1,
  split, exact cena,split,exact b1circ,split,exact ona,split,exact bcirc,split,exact Babb1,rw M2 b1 b,assumption,
end

theorem Blem (a b c : point) : B a b c → length a b < length a c ∧ length b c < length a c :=
begin
  intro Babc,have := DS1 a b c Babc,rw ← this,split,
  linarith [(ne.symm (not_imp_not.2 (M1 b c).1 (B1 Babc).2.2.2.1)).le_iff_lt.mp (M5 b c)],
  linarith [(ne.symm (not_imp_not.2 (M1 a b).1 (B1 Babc).2.1)).le_iff_lt.mp (M5 a b)],
end

theorem Blem1 (a b c d : point) : c≠ d → B a b c → B a b d → B b c d ∨ B b d c:=
begin
  intros hcd Babc Babd,
  have := B7 a b c d Babc Babd,
  rcases LC1 (B1 Babc).2.1 with ⟨L, aL, bL⟩,
  have := B6 b c d L bL (B2 Babc aL bL) (B2 Babd aL bL) (B1 Babc).2.2.2.1 (B1 Babd).2.2.2.1 hcd,
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

/-
theorem junk (a b c : point): :=
  begin
  let C: ℝ := length a d,have  Chyp :C= length a d,exact rfl,
  let A:= length d c',
  let B:= length a c',
  wlog h : (A ≤ B ∧ B≤ C) using [A B C, A C B , B A C, B C A, C A B, C B A], exact tripleorder A B C,

  end
-/


/-
  let A:= length d c',
  let B:= length a c',
  let C:= length a d,
  have := tripleorder  (length d c') (length a c') (length a d) ,
  wlog h : (length d c' ≤ length a c' ∧ length a c'≤ length a d) using [A B C, A C B , B A C, B C A, C A B, C B A], --exact tripleorder (length d c') (length a c') (length a d),
  -/

theorem tan2 (a d c' : point)(had: a≠ d) (hdc: d≠ c')(hac: a≠ c'):
  ∃ (α β γ : circle),∃ (a1 b1 c1 d1 e1 f1 : point),center a1 α ∧ center b1 β
  ∧ center c1 γ ∧ oncircle d1 α ∧ oncircle d1 β ∧ oncircle e1 α
  ∧ oncircle e1 γ ∧ oncircle f1 β ∧ oncircle f1 γ ∧ B a1 d1 b1 ∧ B a1 e1 c1
  ∧ B b1 f1 c1 ∧ length a1 d1 = length a d ∧ length b1 d1 = length d c'
  ∧ length c1 e1 = length a c' :=
  begin

    rcases tan1 a d c' had hdc with ⟨α,β,b,acen,bcen,dona,donb,Badb,len⟩ ,

    rcases excor2 (ne.symm had) had (ne.symm had) with ⟨e,Bdae,len2 ⟩,
    rcases excor2 (B1 Bdae).2.2.2.1 (ne.symm (B1 Bdae).2.2.2.1) hac with ⟨f,Baef,len3⟩,
    rcases excor2 (B1 Badb).2.2.2.1 (ne.symm (B1 Badb).2.2.2.1) (B1 Badb).2.2.2.1 with ⟨g,Bdbg,len4 ⟩,
    rcases excor2 (B1 Bdbg).2.2.2.1 (B1 (B5 g b d a (B1 Bdbg).1 (B1 Badb).1)).2.2.1 hac with ⟨h,Bbgh,len5⟩ ,
    rcases LC2 (B1 Baef).2.2.1 with ⟨δ,acen2,fcirc⟩,
    rcases LC2 (B1 Bbgh).2.2.1 with ⟨ε,bcen2,hcirc⟩,
    rcases excor2 had (ne.symm had) hac with ⟨l,Badl,len6 ⟩,
    have or : inside f δ ∨ oncircle f δ, right, assumption,
    have key: ¬ inside f ε,
    {
      intro infe,
      have key:= (DS4 bcen2 hcirc).2 infe,
      rw ← (DS1 Bbgh) at key, rw len4 at key,rw M2 d b at key, rw len at key,rw len5 at key, rw M2 b f at key,
      rw←  DS1 (B5 f a d b ((B1 (B5 d a e f Bdae Baef)).1) Badb) at key, rw M2 f a at key,
      rw ← DS1 Baef at key, rw len2 at key,rw len3 at key,rw ←  DS1 Badb at key, rw M2 at key, rw M2 d b at key,
      rw len at key,linarith [nonzerolen had],
    },
    have key2: intercirclecircle δ ε,
    {
      by_cases hbl: b=l,
      {
        have lol:= DS1 Badb, rw hbl at lol , rw len6 at lol,rw M2 a d at lol,
        have := DS1 Baef,rw len3 at this,rw len2 at this,rw lol at this,rw hbl at bcen2,
        exact Int4 l f δ ε ((DS3 acen2 fcirc).1 (eq.symm this)) or (G3  bcen2) key,
      },
      have lol:= DS1 Badl,rw len6 at lol,
      have := DS1 Baef,rw len2 at this, rw len3 at this,rw M2 at this, rw this at lol,
      have key2:= Blem1 a d b l hbl Badb Badl,
      cases key2,
      {
        have := DS1 key2,rw M2 d b at this,rw len at this,rw len6 at this,
        have lol2:=(DS1 Bbgh),rw len4 at lol2,rw M2 d b at lol2, rw len at lol2,rw len5 at lol2, rw ← this at lol2,
        have : length b l < length b h := by linarith [nonzerolen (ne.symm hdc)],
        exact Int4 l f δ ε ((DS3 acen2 fcirc).1 lol) or ((DS4 bcen2 hcirc).1 this) key,
      },
      {
        have := DS1 key2,rw M2 d b at this,rw len at this,rw len6 at this,
        have lol2:=(DS1 Bbgh),rw len4 at lol2,rw M2 d b at lol2, rw len at lol2,rw len5 at lol2, rw ← this at lol2,
        have : length l b < length b h := by linarith [nonzerolen hac], rw M2 l b at this,
        exact Int4 l f δ ε ((DS3 acen2 fcirc).1 lol) or ((DS4 bcen2 hcirc).1 this) key,
      },
    },
    rcases I6 key2 with ⟨c,cdel,cep ⟩,
    have hac1 : a ≠ c,
    {
      intro hac, rw hac at acen2,
      exact (G4 c δ (G3 acen2)) cdel,
    },
    rcases LC1 hac1 with ⟨L,aL, cL ⟩ ,
    have := Int3  (G3  acen) aL,

    have := (DS3 acen2 cdel).2 fcirc,rw ← DS1 Baef at this, rw len2 at this, rw len3 at this,
    have : length a c > length d a := by linarith [nonzerolen hac],
    have key5:= (DS5 a d c α acen dona).1, rw M2 a d at key5,

    rcases I4 a c L α  (G3  acen) aL (key5 this).2 (key5 this).1 cL with ⟨j,jcirc,jL,Bajc ⟩ ,
    rcases LC2 (ne.symm  (B1 Bajc).2.2.2.1) with ⟨γ, ccen, jcirc2 ⟩ ,
      have hbc : b ≠ c,
    {
      intro hbc, rw hbc at bcen2,
      exact (G4 c ε  (G3  bcen2)) cep,
    },
    rcases LC1 hbc with ⟨M,bM, cM ⟩ ,
    have := Int3   (G3 bcen) bM,

    have := (DS3  bcen2 cep).2 hcirc,rw ← DS1 Bbgh at this, rw len4 at this, rw len5 at this,
    have : length b c > length d b := by linarith [nonzerolen hac],
    have key5:= (DS5 b d c β bcen donb).1, rw M2 b d at key5,

    rcases I4 b c M β   (G3  bcen) bM (key5 this).2 (key5 this).1 cM with ⟨k,kcirc,kM,Bbkc ⟩ ,
    rcases LC2 (ne.symm  (B1 Bbkc).2.2.2.1) with ⟨γ1 , ccen1, kcirc1 ⟩ ,

    have := DS1 Bajc, rw (DS3  acen jcirc).2 dona at this, rw (DS3 acen2 cdel).2 fcirc at this,
    rw ← DS1 Baef at this, rw len2 at this, rw len3 at this,rw M2 a d at this,
    have key3: length j c = length a c' := by linarith,

    have := DS1 Bbkc, rw (DS3 bcen kcirc).2 donb at this, rw (DS3 bcen2 cep).2 hcirc at this,
    rw ← DS1 Bbgh at this, rw len at this, rw len4 at this,rw len5 at this, rw M2 d b at this, rw len at this,
    have key4: length j c = length k c := by linarith,rw M2 at key4, rw M2 k c at key4,

    have := DS2 ccen ccen1 jcirc2 kcirc1 key4, rw ← this at kcirc1,

    use α,
    use β,use γ,use a,use b,use c,use d,use j, use k,
    split, exact acen,split, exact bcen,split, exact ccen,split, exact dona,split, exact donb,
    split, exact jcirc,split, exact jcirc2,split, exact kcirc,split, exact kcirc1,split, exact Badb,
    split, exact Bajc,split, exact Bbkc, split, refl, rw M2 d c', split, exact len,rw M2 c j,exact key3,
  end

--------------------------------------------------------------------------------------------------------------------

def getpointcirc (α : circle) : point :=
begin
    have := P7 α ,
    cases this,
end

def getcenter (α : circle) : point :=
begin
  sorry,
end

lemma getcenteriscenter (α : circle) (a : point) : center a α→ a = getcenter α :=
begin

end

def getradius1 (α :circle) : ℝ := length (getcenter α ) (getpointcirc α )

def getradius : circle →  ℝ  := λ (α : circle), length (getcenter α ) (getpointcirc α)

def double : ℕ → ℕ := λ x, x + x

lemma doublelem : ∀ (x : ℕ ), double x = 2*x :=
begin
  intros x,
  dsimp only [double],
  ring,
end

lemma toy (α : circle):   ∀ (p : point), oncircle p α → length p (getcenter α) = getradius α  :=
begin
  intros p pcirc,
  dsimp [getradius],
end


def aretangent (α β : circle) : Prop := ∃ (d : point), oncircle d α ∧ oncircle d β ∧ B (getcenter α ) d (getcenter β )
-- how to use λ calculus with def.
lemma tan3pre11 (α β γ : circle) :
aretangent α β → aretangent β γ → aretangent γ α → getradius α =   getradius β →
getradius γ = getradius α  → ∃ (ζ : circle), aretangent α ζ ∧ aretangent β ζ ∧ aretangent γ ζ  :=
begin
have := getradius α ,

end

--lemma getangentpoint (α β : circle) (tan : aretangent α β ) : (point, Prop)

def istangentpoint (p: point)(α β  : circle) (tan : aretangent α β ) : Prop :=
begin
  sorry,
end

--lemma uniquetangent (p: point) (α β :circle)(tan : aretangent α β )(pona : oncircle p α )(ponb : oncircle p β ):
--p=

lemma tan3pre1 (a' b' a b c d e f: point)(α β γ : circle) : a'≠ b'
→ center a α → center b β → center c γ → oncircle d α → oncircle d β → oncircle e α → oncircle e γ
→ oncircle f β → oncircle f γ → B a d b → B a e c→ B b f c
→ length a d = length a' b' → length b d = length a' b' → length c e = length a' b'
→ ∃ (z g h i: point),∃ (ζ : circle), center z ζ ∧ oncircle g α ∧ oncircle g ζ ∧ oncircle h β  ∧ oncircle h ζ
∧ oncircle i γ ∧ oncircle i ζ ∧ B a g z ∧ B b h z ∧ B c i z :=
begin
intros hab1 acen bcen ccen dcirca dcircb ecirca ecircc fcircb fcircc Badb Baec Bbfc len1 len2 len3,
rcases LC1 b e _ with ⟨L,bL,eL ⟩ ,
rcases LC1 a f _ with ⟨M,aM,fM⟩,
rcases LC1 c d _ with ⟨N,cN,dN⟩,
have int: interlineline L M := _,
have int2: interlinecircle L β:=by exact Int3 b L β (G3 b β bcen) bL ,
have int3: interlinecircle M α:=by exact Int3 a M α (G3 a α acen) aM,
have int4: interlinecircle N γ:=by exact Int3 c N γ (G3 c γ ccen) cN,
rcases I1 L M int with ⟨z,zL,zM ⟩,
rcases I4 a f M α (G3 a α acen) aM _ _ fM with ⟨k,kcirc,kM,Bakf ⟩,
rcases I4 b e L β (G3 b β bcen) bL _ _ eL with ⟨j,jcirc,jL,Bbje ⟩,
rcases I4 c d N γ (G3 c γ ccen) cN _ _ dN with ⟨l,lcirc,lN,Bcld ⟩,

rcases LC2 z k _ with ⟨ζ ,zcen,kcirc ⟩ ,

use z,use k,use j,use l,use ζ ,
split,assumption,split,assumption,split,assumption,split,assumption,
split,
{
  sorry,
},
split, assumption,
split,
{
  sorry,
},

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
rcases LC1 a c (B1 a e c Baec).2.2.1 with ⟨M, aM, cM ⟩,

by_cases int: interlineline L M,
{
  rcases I1 L M int with ⟨g,gL,gM ⟩,
  rcases LC2 g e _ with ⟨ε,gcen,ecirc ⟩ ,
},

end

/-
theorem bisang {a b c : point} (ab : a≠ b)(ac: a≠ c) : ∃(f : point), angle b a f = angle c a f ∧ f≠ a:=
begin--Euclid I.9
  rcases excor2 ab ab.symm ac with ⟨d, Babd, bdac⟩,
  rcases excor2 ac ac.symm ab with ⟨e, Bace, ceab⟩,
  by_cases d=e,
  { rw h at Babd,rcases Beasy3 Babd with ⟨L,aL,bL,eL,ab,be,ea⟩,
    refine ⟨ e, by linarith[(A1 ab ea.symm aL bL).1 ⟨eL, (B1 Babd).2.2.2.2⟩,
      (A1 (B1 Bace).2.1 ea.symm aL (B3 Bace aL eL)).1 ⟨eL, (B1 Bace).2.2.2.2⟩],ea⟩ ,
  },rcases makeeqtri1 h with ⟨f, f1,eqtri,eqtri1,ff1⟩, by_cases a=f,
  {have af1: a≠ f1 :=λ hyp, ff1 ((rfl.congr hyp).mp (eq.symm h)),
  refine ⟨f1, by linarith [A4mod1 af1 Babd,A4mod1 af1 Bace,(sss ((by linarith [DS1 Babd,DS1 Bace]:
    length a d = length a e))(flipboth eqtri1.2.2.1) rfl).2.1],af1.symm⟩ ,
  },
  refine ⟨f, by linarith[A4mod1 h Babd,A4mod1 h Bace,
    (sss (by linarith [DS1 Babd,DS1 Bace]:length a d = length a e)(flipboth eqtri.2.2.1) rfl).2.1],ne.symm h⟩,
end
-/

/- is this even provable?
theorem bisangext {a b c : point} (ab : a≠ b)(ac: a≠ c) : ∃ (m n : point), angle b a m = angle c a m
  ∧ angle b a n = angle c a n ∧ B m a n :=--the true Euclid I.9
begin
  rcases excor2 ab ab.symm ac with ⟨d, Babd, bdac⟩,
  rcases excor2 ac ac.symm ab with ⟨e, Bace, ceab⟩,
  by_cases d=e,
  { rw h at Babd,rcases Beasy3 Babd with ⟨L,aL,bL,eL,ab,be,ea⟩,sorry,
    --refine ⟨ e, by linarith[(A1 ab ea.symm aL bL).1 ⟨eL, (B1 Babd).2.2.2.2⟩,
    --  (A1 (B1 Bace).2.1 ea.symm aL (B3 Bace aL eL)).1 ⟨eL, (B1 Bace).2.2.2.2⟩],ea⟩ ,
  },rcases makeeqtri2 h with ⟨m, n,M,eqtrim,eqtrin,dM,eM,nssmn⟩, by_cases an: a=n,sorry,by_cases am: a=m,sorry,
have : B m a n,
{

},

end
-/

/-
theorem perpline {a b c : point} (Babc: B a b c) : ∃ (d : point), --Euclid I.11
  angle d b a = rightangle ∧ angle d b c = rightangle :=
begin
  wlog h : (length b a ≤ length b c) using [a c, c a], exact le_total (length b a) (length b c),
  {
    rcases bisline (B1 Babc).2.1 with ⟨e,Baeb,len ⟩,
    rcases excor (B1 Baeb).2.2.2.1 (B1 Baeb).2.2.2.1.symm with ⟨f,Bebf,len1 ⟩,
    rcases makeeqtri (B1 Bebf).2.2.1 with ⟨d,len2,len3,len4, ef, fd, de⟩,
    have :=(sss (flip2 len1) (flipboth len4).symm rfl).2.1,
    have bd : b≠ d,
    {
      intro bd,
      rw bd at Bebf,
      have := DS1 Bebf,
      have := nonzerolen fd.symm,
      linarith,
    },
    have key:= A4mod1 bd (B1 Baeb).1,

      rcases Beasy3 Baeb with ⟨ L,aL,eL,bL,nq⟩ ,
      rcases Beasy3 Bebf with ⟨ M,eM,bM,fM,nq1⟩ ,
      rcases Beasy3 Babc with ⟨ N,aN,bN,cN,nq2⟩,
      have := G1 nq1.1 eM bM eL bL,
      rw this at fM,
      have := G1 nq.2.2.symm aL bL aN bN,
      rw this.symm at cN,

    have Bbfc : B b f c,
    {
      have fc : f≠ c,
      {
        intro fc,
        rw fc at len1,
        have := DS1 Babc,
        have := DS1 Baeb,
        linarith[M2 b a,nonzerolen nq2.2.1],
      },
      cases B6 bL fM cN nq1.2.1 nq2.2.1 fc,
      {
        assumption,
      },
      cases h_1,
      {
        exfalso,
        have af: a≠ f,
        {
          intro af,
          rw af.symm at Bebf,
          exact Beasy4 (B1 Bebf).2.2.2.2 Baeb,
        },
        cases Beasy5  af (B1 Babc).1 (B1 h_1).1,
        {
          have := DS1 h_2,
          have := DS1 Baeb,
          linarith[nonzerolen nq.2.2,nonzerolen af, M2 a b],
        },
        {
          have := DS1 h_2,
          have := DS1 Baeb,
          have :=DS1 (B5 Baeb Bebf),
          have := DS1 Bebf,
          linarith[M2 a b,M2 a f,nonzerolen ef],
        },
      },
      {
        exfalso,
        have := DS1 h_1,
        linarith[DS1 Baeb, M2 a b, nonzerolen nq1.1,nonzerolen fc.symm],
      },
    },
    have dL: ¬ online d L,
    {
      intro dL,
      cases B6 eL dL fM de.symm ef fd.symm,
      {
        have := DS1 h_1,
        linarith [nonzerolen de.symm,flipboth len3],
      },
      cases h_1,
      {
        have := DS1 h_1,
        linarith [nonzerolen ef],
      },
      {
        have := DS1 h_1,
        linarith [nonzerolen fd],
      },
    },

    have key1:= A4mod1 bd Bbfc,
    have ad : a≠ d,
    {
      intro ad,
      rw ad.symm at dL,
      exact dL aL,
    },
    have cd : c≠ d,
    {
      intro cd,
      rw cd.symm at dL,
      exact dL cN,
    },
    have := aflip2 nq.2.2.symm ad key,
    have := aflip2 nq2.2.1.symm cd key1,

    have := (A3 aL cN Babc dL).1 (by linarith),
    use d,
    split,linarith,linarith,
  },
  rcases this (B1 Babc).1 with ⟨d,ang1,ang2⟩,
  use d,
  split,
  exact ang2,exact ang1,
end

-/

  /-
  rcases perpline Babc with ⟨d,ang1,ang2 ⟩,


    wlog h : (length b a ≤ length b c) using [a c, c a], exact le_total (length b a) (length b c),
  {
    rcases bisline (B1 Babc).2.1 with ⟨e,Baeb,len ⟩,
    rcases excor (B1 Baeb).2.2.2.1 (B1 Baeb).2.2.2.1.symm with ⟨f,Bebf,len1 ⟩,
    rcases makeeqtri3 (B1 Bebf).2.2.1 with ⟨d, d1,P,⟨ len2,len3,len4, ef, fd, de⟩,⟨len5,len6,len7, ef, fd1, d1e⟩,eP,fP,dP,d1P,nss⟩,
    have :=(sss (flip2 len1) (flipboth len4).symm rfl).2.1,
    have bd : b≠ d,
    {
      intro bd,
      rw bd at Bebf,
      have := DS1 Bebf,
      have := nonzerolen fd.symm,
      linarith,
    },
    have key:= A4mod1 bd (B1 Baeb).1,

      rcases Beasy3 Baeb with ⟨ L,aL,eL,bL,nq⟩ ,
      rcases Beasy3 Bebf with ⟨ M,eM,bM,fM,nq1⟩ ,
      rcases Beasy3 Babc with ⟨ N,aN,bN,cN,nq2⟩,
      have := G1 nq1.1 eM bM eL bL,
      rw this at fM,
      have := G1 nq.2.2.symm aL bL aN bN,
      rw this.symm at cN,

    have Bbfc : B b f c,
    {
      have fc : f≠ c,
      {
        intro fc,
        rw fc at len1,
        have := DS1 Babc,
        have := DS1 Baeb,
        linarith[M2 b a,nonzerolen nq2.2.1],
      },
      cases B6 bL fM cN nq1.2.1 nq2.2.1 fc,
      {
        assumption,
      },
      cases h_1,
      {
        exfalso,
        have af: a≠ f,
        {
          intro af,
          rw af.symm at Bebf,
          exact Beasy4 (B1 Bebf).2.2.2.2 Baeb,
        },
        cases Beasy5  af (B1 Babc).1 (B1 h_1).1,
        {
          have := DS1 h_2,
          have := DS1 Baeb,
          linarith[nonzerolen nq.2.2,nonzerolen af, M2 a b],
        },
        {
          have := DS1 h_2,
          have := DS1 Baeb,
          have :=DS1 (B5 Baeb Bebf),
          have := DS1 Bebf,
          linarith[M2 a b,M2 a f,nonzerolen ef],
        },
      },
      {
        exfalso,
        have := DS1 h_1,
        linarith[DS1 Baeb, M2 a b, nonzerolen nq1.1,nonzerolen fc.symm],
      },
    },
    have dL: ¬ online d L,
    {
      intro dL,
      cases B6 eL dL fM de.symm ef fd.symm,
      {
        have := DS1 h_1,
        linarith [nonzerolen de.symm,flipboth len3],
      },
      cases h_1,
      {
        have := DS1 h_1,
        linarith [nonzerolen ef],
      },
      {
        have := DS1 h_1,
        linarith [nonzerolen fd],
      },
    },

    have key1:= A4mod1 bd Bbfc,
    have ad : a≠ d,
    {
      intro ad,
      rw ad.symm at dL,
      exact dL aL,
    },
    have cd : c≠ d,
    {
      intro cd,
      rw cd.symm at dL,
      exact dL cN,
    },
    have := aflip2 nq.2.2.symm ad key,
    have := aflip2 nq2.2.1.symm cd key1,

    have := (A3 aL cN Babc dL).1 (by linarith),
    have OL: O=L,
    {
      exact G1 nq2.2.2 cO aO cN aL,
    },
    by_cases ¬ diffside d p L,
    {
      use d,
      split,linarith,split,linarith,
      unfold diffside at h,push_neg at h,rw←  OL at h,rw← OL at dL,
      exact h dL pO,
    },

  },
  rcases this (B1 Babc).1 with ⟨d,ang1,ang2⟩,
  use d,
  split,
  exact ang2,exact ang1,
  -/

/-
theorem bisline {a b : point} (ab : a≠ b): ∃ (d : point), B a d b ∧ length a d = length d b :=
begin--Euclid I.10
  rcases makeeqtri2 ab with ⟨c,e,L,⟨labac,lbcba,lcacb,ab,bc,ca ⟩,⟨labae,lbeba,lcaeb,ab,be,ea ⟩,aL, bL,nss,ce⟩,
  rcases LC1 ce with ⟨M,cM,eM⟩,
  rcases I1 L M (Int1 c e L M nss cM eM) with ⟨d, dL, dM⟩,
  have bis:=aflipboth ca.symm ea.symm bc be (sss (by linarith: length c a = length c b) (by linarith[M2 a e, M2 b e]: length a e = length b e) rfl).2.1,
  have Bet:= Pa4 _ ce cM dM eM dL _ _ nss,
  have := (A4mod1 ca Bet),
  have := A4mod1 bc.symm Bet,
  have := flip1 (sas (rfl : length c d = length c d) (by linarith : length c a = length c b) (by linarith)).1,
  use d,split,
  {
    have := B6 aL bL dL ab _ _,
    cases this,
    {
      exfalso,
      have := DS1 this_1,
      linarith[M2 b d,nonzerolen ab],
    },
    {
      cases this_1,
      {
        exfalso,
        have := DS1 this_1,
        linarith[M2 b d,nonzerolen ab.symm],
      },
      assumption,
    },
    {
      intro ad,rw ← ad at this,have := M1.mpr (rfl: a=a),linarith[nonzerolen ab],
    },
    {
      intro ad,rw ← ad at this,have := M1.mpr (rfl: b=b),linarith[nonzerolen ab],
    },
  },
  assumption,
  {
    intro LM,rw← LM at cM,
    cases B6 aL bL cM ab ca.symm bc,
    have := DS1 h,linarith[flipboth lcacb, flip2 lbcba,nonzerolen ab],
    cases h,
    have := DS1 h,linarith[nonzerolen ca.symm],
    have := DS1 h,linarith[nonzerolen bc.symm],
  },
  {
    intro cd,
    rw← cd at dL,
    cases B6 aL bL dL ab ca.symm bc,
    have := DS1 h,linarith[flipboth lcacb, flip2 lbcba,nonzerolen ab],
    cases h,
    have := DS1 h,linarith[nonzerolen ca.symm],
    have := DS1 h,linarith[nonzerolen bc.symm],
  },
    intro ed,rw ← ed at dL,
    cases B6 aL bL dL ab ea.symm be,
    have := DS1 h,linarith[flipboth lcacb, flip2 lbcba,nonzerolen ab],
    cases h,
    have := DS1 h,linarith[nonzerolen ca.symm],
    have := DS1 h,linarith[nonzerolen be.symm],
end

theorem bisangiso {a b c : point} {L M : line} (ab : a≠ b) (ac: a≠ c) (LM: L≠ M) (aL: online a L) (bL : online b L)
  (aM: online a M) (cM: online c M) (abeqac: length a b = length a c): ∃ (d: point), angle b a d = angle c a d ∧ sameside d b M ∧ sameside d c L ∧ B b d c :=
begin
  have bc : b≠ c,
  {
    intro bc,rw← bc at cM,
    exact LM (G1 ab aL bL aM cM),
  },
  rcases bisline bc with ⟨d,Bbdc,len ⟩ ,
  have := (sss abeqac (flip2 len) rfl).2.1,
  have:= Pa2 Bbdc bL _,
  have:= Pa2 (B1 Bbdc).1 cM _,
  use d,split, assumption,split,assumption,split, assumption,assumption,
  {
    intro dM,
    rcases Beasy3 Bbdc with ⟨ N,bN,dN,cN,bd,dc,cb⟩,
    have := G1 dc.symm cN dN cM dM,rw this at bN,
    exact LM (G1 ab aL bL aM bN),
  },
    intro dM,
    rcases Beasy3 Bbdc with ⟨ N,bN,dN,cN,bd,dc,cb⟩,
    have := G1 bd bN dN bL dM,rw this at cN,
    exact LM (G1 ac aL cN aM cM),
end

theorem bisang {a b c : point} {L M : line} (ab : a≠ b) (ac: a≠ c) (LM: L≠ M) (aL: online a L) (bL : online b L) --Euclid I.9
  (aM: online a M) (cM: online c M) : ∃ (d: point), angle b a d = angle c a d ∧ sameside d b M ∧ sameside d c L :=
begin

  rcases excor2 ab ab.symm ac with ⟨d, Babd, bdac⟩,
  rcases excor2 ac ac.symm ab with ⟨e, Bace, ceab⟩,
  have len : length a d = length a e,
  {
    have := DS1 Babd,
    have := DS1 Bace,
    linarith,
  },

  have key := bisangiso (B1 Babd).2.2.1 (B1 Bace).2.2.1 LM aL (B2 Babd aL bL) aM (B2 Bace aM cM) len,
  rcases key with ⟨f,ang,ss1,ss2,Bdfe⟩,
  use f,

  split,
  {
    have af: a≠ f,
    {
      intro af,
      rcases Beasy3 Bdfe with ⟨N,dN,fN,eN,df,fe,ed⟩,
      rw ← af at fN,
      have key:= G1 (B1 Babd).2.2.1 aL (B2 Babd aL bL) fN dN,
      have key1:= G1 (B1 Bace).2.2.1 aM (B2 Bace aM cM) fN eN,
      rw← key at key1,
      exact LM key1.symm,
    },
    have := A4mod1 af Babd,
    have := A4mod1 af Bace,
    linarith,

  },
  split,
  {
  have := Pa2 Babd aM _,

  exact  S4 (S2 ss1) (S2 this),

  intro bM,
  have := G1 ab aL bL aM bM,
  exact LM this,
  },

  have := Pa2 Bace aL _,
  exact  S4 (S2 ss2) (S2 this),

  intro cL,
  have := G1 ac aL cL aM cM,
  exact LM this,
end

theorem perplinemodmod {a b c : point} (Babc: B a b c) : ∃ (d : point), --Euclid I.11
  angle a b d = rightangle ∧ angle c b d = rightangle :=
begin
  rcases excor2 (B1 Babc).2.1.symm (B1 Babc).2.1 (B1 Babc).2.2.2.1 with ⟨e,Bbae,len1 ⟩,
  rcases excor2 (B1 Babc).2.2.2.1 (B1 Babc).2.2.2.1.symm (B1 Babc).2.1.symm with ⟨f,Bbcf,len2⟩,
  have ef := (B1 (B5 (B1 Bbae).1 (B5 Babc Bbcf))).2.2.1,
  rcases makeeqtri3 ef with ⟨d,d1,L,⟨ len1,len2,len3,nq⟩ ,other,eL,fL,dL,d1L,nss ⟩,
  have : length e b = length f b,
  { have := DS1 Bbae,
    have := DS1 Bbcf,apply flipboth,linarith,
  },
  have ang:= (sss len3 this rfl).2.2,
  have bd :=(Leasy (B2 (B1 Bbae).1 eL (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL)) dL),
  have a1:= A4mod1 bd Bbae,
  have a2:= A4mod1 bd Bbcf,
  have := aflip2 (B1 Bbcf).2.2.1.symm nq.2.1 a2,
  have := aflip2 (B1 Bbae).2.2.1.symm nq.2.2.symm a1,
  have := aflip1 (B1 Babc).2.2.2.1.symm (Leasy (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL) dL) a2,
  have := (A3 (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL) (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL) Babc dL).1 (by linarith),
  use d,split, exact this,linarith,
end

theorem perplinecor {a b c p: point} {O: line} (aO: online a O) (cO: online c O) (pO: ¬ online p O) (Babc: B a b c)  : ∃ (d : point), angle a b d = rightangle ∧ angle c b d = rightangle ∧ sameside d p O:= --Euclid I.11
begin
  rcases excor2 (B1 Babc).2.1.symm (B1 Babc).2.1 (B1 Babc).2.2.2.1 with ⟨e,Bbae,len1 ⟩,
  rcases excor2 (B1 Babc).2.2.2.1 (B1 Babc).2.2.2.1.symm (B1 Babc).2.1.symm with ⟨f,Bbcf,len2⟩,
  have ef := (B1 (B5 (B1 Bbae).1 (B5 Babc Bbcf))).2.2.1,
  rcases makeeqtri3 ef with ⟨d,d1,L,⟨ len1,len2,len3,nq⟩ ,⟨len4,len5,len6,nq1 ⟩,eL,fL,ds ⟩,
  have : length e b = length f b,
  { have := DS1 Bbae,
    have := DS1 Bbcf,apply flipboth,linarith,
  },
  by_cases sameside d p O,
  {
  have ang:= (sss len3 this rfl).2.2,
  have bd :=(Leasy (B2 (B1 Bbae).1 eL (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL)) ds.1),
  have a1:= A4mod1 bd Bbae,
  have a2:= A4mod1 bd Bbcf,
  have := aflip2 (B1 Bbcf).2.2.1.symm nq.2.1 a2,
  have := aflip2 (B1 Bbae).2.2.1.symm nq.2.2.symm a1,
  have := aflip1 (B1 Babc).2.2.2.1.symm (Leasy (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL) ds.1) a2,
  have := (A3 (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL) (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL) Babc ds.1).1 (by linarith),
  use d,split, exact this,split, linarith, exact h,
  },
  have OL:= G1 (B1 Babc).2.2.1 aO cO (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL) (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL),
  rw OL at h,rw OL at pO,
  have h:= difdifsame ds ⟨ds.1,pO,h ⟩,rw OL,
  have ang:= (sss len6 this rfl).2.2,
  have bd :=(Leasy (B2 (B1 Bbae).1 eL (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL)) ds.2.1),
  have a1:= A4mod1 bd Bbae,
  have a2:= A4mod1 bd Bbcf,
  have := aflip2 (B1 Bbcf).2.2.1.symm nq1.2.1 a2,
  have := aflip2 (B1 Bbae).2.2.1.symm nq1.2.2.symm a1,
  have := aflip1 (B1 Babc).2.2.2.1.symm (Leasy (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL) ds.2.1) a2,
  have := (A3 (B3 (B5 (B1 Bbae).1 (B5 Babc Bbcf)) eL fL) (B3 (B5 (B1 Bbcf).1 (B5 (B1 Babc).1 Bbae)) fL eL) Babc ds.2.1).1 (by linarith),
  use d1,split, exact this,split, linarith, exact h,
end

theorem flatsumright {a b c d : point} {L: line} (dL: online d L) (cL: online c L) --Euclid I.13
(aL: ¬ online a L) (Bdbc: B d b c) : angle a b c + angle a b d = 2*rightangle :=
begin
  by_cases (angle a b c = angle a b d),
  {
    have := (aflip2 (Leasy (B3 Bdbc dL cL) aL).symm (Leasy dL aL).symm h).symm,
    have := (A3 dL cL Bdbc aL).mp this, linarith,
  },
  have eperp : ∃ (e : point), angle e b c = angle e b d ∧ sameside e a L,
  {
    rcases perplinecor cL dL aL (B1 Bdbc).1 with ⟨e,a1,a2,ss ⟩,
    use e,split,
    have := M3 (B1 Bdbc).2.2.2.1.symm (Leasy cL (S3  ss)),
    have := M3 (B1 Bdbc).2.1 (Leasy dL (S3  ss)),
    linarith,exact ss,
  },
  rcases eperp with ⟨e,ra,eaL⟩,
  have eb := (Leasy (B3 Bdbc dL cL) (S3  eaL)).symm,
  rcases LC1 eb with ⟨M, eM, bM ⟩,
  have aM: ¬ online a M,
    {
      intro aM,
      by_cases ae: a=e,
      {
        rw ae at h, exact h ra,
      },
      cases B6 aM bM eM (Leasy (B3 Bdbc dL cL) aL).symm ae eb.symm,
      {
        have := Pa3 h_1 (B3 Bdbc dL cL), exact this (S2 eaL),
      },
      cases h_1,
      have ang:= A4mod1 (B1 Bdbc).2.1.symm h_1,
      have := A4mod1 (B1 Bdbc).2.2.2.1 h_1, rw this at h, rw ang at h, exact h ra,
      have ang:= A4mod1 (B1 Bdbc).2.1.symm (B1 h_1).1,
      have := A4mod1 (B1 Bdbc).2.2.2.1 (B1 h_1).1, rw←  this at h, rw←  ang at h, exact h ra,
    },
  wlog acM : (sameside a c M) using [c d, d c],
  {
    by_cases h1 :sameside a c M,
    left,assumption,right,
    have cM: ¬ online c M,
    {
      intro cM,
      have := G1 (B1 Bdbc).2.2.2.1 bM cM (B3 Bdbc dL cL) cL,
      have eL:= S3 eaL, rw this at eM, exact eL eM,
    },
    have dM: ¬ online d M,
    {
      intro dM,
      have := (B1 Bdbc).2.1.symm,
      have := G1 (B1 Bdbc).2.1.symm bM dM (B3 Bdbc dL cL) dL,
      have eL:= S3 eaL, rw this at eM, exact eL eM,
    },
    have := Pa3 Bdbc bM,
    exact difdifsame ⟨cM,aM,difsym h1 ⟩ ⟨cM, dM, difsym this⟩,
  },
  {
    have splitcbe:= (A2 (B3 Bdbc dL cL) cL bM eM (B1 Bdbc).2.2.2.1 eb.symm aM aL _).mpr _,
    have ab : a≠ b,
    {
      exact (Leasy bM aM).symm,
    },
    rcases LC1 ab with ⟨N,aN,bN ⟩,
    have eNL : ¬ online e N ∧ ¬ online e L,
    {
      split,
      intro eN,
      have := G1 eb eM bM eN bN,rw this at aM,exact aM aN,
      intro eL,
      have := G1 eb eL (B3 Bdbc dL cL) eM bM, exact (S3 eaL) eL,
    },
    have splitabd:= (A2 bN aN (B3 Bdbc dL cL) dL ab.symm (B1 Bdbc).2.1.symm eNL.2 eNL.1 _).mpr _,
    have de := Leasy dL eNL.2,
    have ce := Leasy cL eNL.2,
    have ac : a≠ c :=(Leasy cL aL).symm,
    have flipdbe:= M3 (B1 Bdbc).2.1 de,
    have flipcbe:= M3 (B1 Bdbc).2.2.2.1.symm ce,
    have flipabc:= M3 ab ac,
    have := (A3 dL cL Bdbc eNL.2).mp (by linarith),
    linarith,
    {
      intro NL,
      rw NL at aN,
      exact aL aN,
    },
    {
      split, exact (S2 eaL),
      have ecN:= T1 bM bN (B3 Bdbc dL cL) eM aN cL acM eaL,
      have dcN:= Pa3 Bdbc bN,
      have cN : ¬ online c N,
      {
        intro cN,
        have := G1 (B1 Bdbc).2.2.2.1 bN cN (B3 Bdbc dL cL) cL,rw this at aN, exact aL aN,
      },
      have dN: ¬ online d N,
      {
        intro dN,
        have := G1 (B1 Bdbc).2.1.symm bN dN (B3 Bdbc dL cL) dL,rw this at aN, exact aL aN,
      },
      have := difdifsame ⟨cN,eNL.1, difsym ecN⟩ ⟨cN,dN,difsym dcN ⟩,
      exact S2 this,
    },
    {
      intro LM,
      rw← LM at eM,exact (S3 eaL) eM,
    },
    {
      split, exact S2 acM,exact eaL,
    },
  },
  have := this cL dL (B1 Bdbc).1 _ ra.symm,
  linarith,
  intro hh,
  exact h hh.symm,
end

theorem rightimpflat {a b c d : point} {N: line} (ab : a≠ b) (aN : online a N) (bN: online b N) (cdN: diffside c d N)
  (ang: angle a b c + angle a b d = 2*rightangle) : B c b d:= -- Euclid I.14
begin
  have cd: c≠ d, --API and degenerate cases
  {
    intro cd, rw cd at cdN,exact cdN.2.2 (S1 cdN.1),
  },
  have bc : b≠ c :=Leasy bN cdN.1,
  rcases excor bc.symm bc with ⟨e,Bcbe,len ⟩,
  by_cases ed : e =d,
  {
    rwa ed at Bcbe,
  },
  rcases LC1 bc with ⟨M,bM,cM ⟩,
  have eM := B2 Bcbe cM bM,
  have ceN:= Pa3 Bcbe bN,
  have eN: ¬ online e N,
  {
    intro eN,
    exact cdN.1 (B2 (B1 Bcbe).1 eN bN),
  },
  have edN: sameside e d N,
  {
    by_contra edN,
    exact cdN.2.2 (S2 (difdifsame ⟨eN,cdN.2.1,edN ⟩ ⟨eN, cdN.1, difsym ceN⟩)),
  },
  have bd: b≠ d,
  {
    intro bd,
    rw bd at bN,exact cdN.2.1 bN,
  },
  rcases LC1 bd with ⟨L,bL,dL⟩,
  have LN: L≠ N,
  {
    intro LN,
    rw LN at dL,
    exact cdN.2.1 dL,
  },
  have MN: M≠ N,
  {
    intro MN,
    rw MN at eM,
    exact eN eM,
  },
  by_cases eL: online e L,
  {
    exact Pa4 LN.symm cd (B2 (B1 Bcbe).1 eL bL) bL dL bN bc.symm bd.symm cdN.2.2,
  },
  have aM: ¬ online a M,
  {
    intro aM,
    have NM:= G1 ab aN bN aM bM,rw← NM at cM,exact cdN.1 cM,
  },
  have dM: ¬ online d M,
  {
    intro dM,
    have ML:= G1 bd bM dM bL dL,rw ML at eM, exact eL eM,
  },
  have ae: a≠ e,
  {
    intro ae,rw ae at aN,exact eN aN,
  },
  have ad: a≠ d:= Leasy aN cdN.2.1,
  have abeflip := M3 ab ae,
  have abdflip := M3 ab ad,
  have dbeflip := M3 bd.symm (ne.symm ed),
  have ang1:= flatsumright cM eM aM Bcbe, --beginning of proof
  by_cases eaL: sameside e a L,
  {
    have split := (A2 bL dL bN aN bd ab.symm eN eL LN).mpr ⟨S2 edN, S2 eaL ⟩,
    have dM:= ((A1 (B1 Bcbe).2.2.2.1 bd bM eM).mpr (by linarith)).1,
    exact Pa4 MN.symm cd cM bM dM bN (B1 Bcbe).2.1 bd.symm cdN.2.2,
  },
  have adM:= T2 bN bL bM aN dL eM (S2 edN) (difsym eaL) eL ab,
  have split := (A2 bN aN bM eM ab.symm (B1 Bcbe).2.2.2.1 dM (S3 (S2 edN)) MN.symm).mpr ⟨adM,edN ⟩,
  have dM:= ((A1 (B1 Bcbe).2.2.2.1 bd bM eM).mpr (by linarith)).1,
  exact Pa4 MN.symm cd cM bM dM bN (B1 Bcbe).2.1 bd.symm cdN.2.2,
end


theorem rightimpflat {a b c d : point} {N: line} (ab : a≠ b) (aN : online a N) (bN: online b N) (cdN: diffside c d N)
  (ang: angle a b c + angle a b d = 2*rightangle) : B c b d:= -- Euclid I.14
begin
  have cd:=difneq cdN, --API and degenerate cases
  have bc:=Leasy bN cdN.1,
  have bd: b≠ d:= λ bd,cdN.2.1 (by rwa bd at bN),
  rcases excor bc.symm bc with ⟨e,Bcbe,len ⟩,
  rcases LC1 bc with ⟨M,bM,cM ⟩,
  have eM := B2 Bcbe cM bM,
  have ceN:= Pa3 Bcbe bN,
  have eN: ¬ online e N:=λ eN, cdN.1 (B2 (B1 Bcbe).1 eN bN),
  have edN: sameside e d N,--:=λ edN,not_imp_not.mpr (cdN.2.2 (S2 (difdifsame ⟨eN,cdN.2.1,edN ⟩ ⟨eN, cdN.1, difsym ceN⟩))),
  {by_contra edN,exact cdN.2.2 (S2 (difdifsame ⟨eN,cdN.2.1,edN ⟩ ⟨eN, cdN.1, difsym ceN⟩)),},--anything better?
  rcases LC1 bd with ⟨L,bL,dL⟩,
  have LN: L≠ N:=λ LN,cdN.2.1 (by rwa LN at dL),
  have MN: M≠ N:=λ MN,eN (by rwa MN at eM),
  by_cases eL: online e L,
  {exact Pa4 LN.symm cd (B2 (B1 Bcbe).1 eL bL) bL dL bN bc.symm bd.symm cdN.2.2,},
  have aM: ¬ online a M:=λ aM,cdN.1 (by rwa ←  (G1 ab aN bN aM bM) at cM),
  have dM: ¬ online d M:=λ dM, eL (by rwa (G1 bd bM dM bL dL) at eM),
  have ae: a≠ e:= λ ae, eN (by rwa ae at aN),
  have ad: a≠ d:= Leasy aN cdN.2.1,
  by_cases ed : e=d,{rwa ed at Bcbe,},
  have abeflip := M3 ab ae,
  have abdflip := M3 ab ad,
  have dbeflip := M3 bd.symm (ne.symm ed),
  have ang1:= flatsumright cM eM aM Bcbe, --beginning of proof
  by_cases eaL: sameside e a L,
  { have split := (A2 bL dL bN aN bd ab.symm eN eL LN).mpr ⟨S2 edN, S2 eaL ⟩,
    have dM:= ((A1 (B1 Bcbe).2.2.2.1 bd bM eM).mpr (by linarith)).1,
    exact Pa4 MN.symm cd cM bM dM bN (B1 Bcbe).2.1 bd.symm cdN.2.2,
  },
  have adM:= T2 bN bL bM aN dL eM (S2 edN) (difsym eaL) eL ab,
  have split := (A2 bN aN bM eM ab.symm (B1 Bcbe).2.2.2.1 dM (S3 (S2 edN)) MN.symm).mpr ⟨adM,edN ⟩,
  have dM:= ((A1 (B1 Bcbe).2.2.2.1 bd bM eM).mpr (by linarith)).1,
  exact Pa4 MN.symm cd cM bM dM bN (B1 Bcbe).2.1 bd.symm cdN.2.2,
end

theorem vertang {a b c d e : point} {L: line} (cL: online c L) (dL : online d L) (aL: ¬ online a L) (Bced: B c e d) (Baeb: B a e b) :
  angle c e a = angle d e b ∧ angle b e c = angle a e d := --Euclid I .15
begin
  rcases Beasy3 Baeb with ⟨N,aN,eN,bN,nq ⟩,
  have ac :a≠ c := (Leasy cL aL).symm ,
  have ad : a≠ d := (Leasy dL aL).symm ,
  have dN: ¬ online d N:=λ dN, ((by rwa (G1 (B1 Bced).2.2.2.1 (B3 Bced cL dL) dL eN dN) at aL):¬ online a N) aN,
  have bd : b≠ d := (Leasy bN dN),
  have bL: ¬ online b L:= λ bL, (by rwa G1 nq.2.1 (B3 Bced cL dL) bL eN bN at aL : ¬ online a N) aN,
  have flip1:= M3 nq.1 ac,
  have flip2:= M3 nq.1 ad,
  have flip3:= M3 nq.2.1.symm bd ,
  have key2:= flatsumright aN bN dN Baeb,
  refine ⟨by linarith[flatsumright cL dL aL Bced],by linarith[flatsumright cL dL bL Bced] ⟩,
end

theorem extang {a b c d : point} {L: line} (aL: ¬ online a L) (bL: online b L) (dL: online d L) (Bbcd: B b c d) :
  angle b a c < angle a c d:=--Euclid I.16
begin
  have cL:= B3 Bbcd bL dL,have ca:= Leasy cL aL,have ba:= Leasy bL aL,
  rcases bisline ca with ⟨e,Bcea,len⟩,
  have be: b≠ e := λ be,aL (B2 Bcea cL (by rwa be at bL)),
  rcases excor be be.symm with ⟨f,Bbef,len2 ⟩,
  have cf:c≠ f:= λ cf, aL (B2 Bcea cL (B3 Bbef bL (by rwa cf at cL))),
  have afL :=S4 (Pa2 Bcea cL (λ eL, aL ((B2 Bcea) cL eL))) (Pa2 Bbef bL (λ eL, aL ((B2 Bcea) cL eL))),
  rcases Beasy3 Bbef with ⟨M,bM,eM,fM,nq ⟩,
  have cM:¬ online c M:=λ cM,((by rwa ← (G1 (B1 Bbcd).2.1 bM cM bL cL) at aL): ¬ online a M) (B2 Bcea cM eM),
  have ang:= vertang bM fM cM Bbef Bcea,
  have ang2:= (sas (flip2 len2) (flip1 len) (by linarith[M3 be ba])).2.2,
  rcases Beasy3 Bcea with ⟨N,cN,eN,aN,nq1 ⟩,
  have fN: ¬ online f N := λ fN,aL (by rwa (G1 (B1 Bbcd).2.1 (B2 (B1 Bbef).1 fN eN) cN bL cL) at aN),
  have bN: ¬ online b N := λ bN, fN (B2 Bbef bN eN),
  have dfN := S2 (difdifsame ⟨bN,fN,Pa3 Bbef eN⟩ ⟨bN,(λ dN, bN (B2 (B1 Bbcd).1 dN cN)),Pa3 Bbcd cN ⟩),
  have NL: N≠ L := λ NL, bN (by rwa←  NL at bL),--start of pf below, API above
  have splitang:= (A2 cN aN cL dL nq1.2.2.symm (B1 Bbcd).2.2.2.1 (S3 (S2 afL)) (S3 (S2 dfN)) NL).mpr ⟨afL,dfN ⟩,
  rcases LC1 cf with ⟨P,cP,fP ⟩,
  have geq:= lt_of_le_of_ne (M4 f c d).2 (ne_comm.mp (mt (A1 cf (B1 Bbcd).2.2.2.1 cP fP).mpr _)),--better way to deal with or?
  have geq2:= lt_of_le_of_ne (M4 b a c).2 (angeasy ca (B1 Bbcd).2.1.symm (ne_comm.mp (mt (A1 ca.symm ba.symm aN cN).mpr _))),
  linarith[M3 ca (B1 Bbcd).2.1.symm,A4mod1 ba.symm (B1 Bcea).1,A4mod1 cf Bcea],
  exact λ bN, NL (G1 (B1 Bbcd).2.1 bN.1 cN bL cL),
  exact λ dP, S3 (S2 (by rwa←  (G1 (B1 Bbcd).2.2.2.1 cP dP.1 cL dL) at afL)) fP,
end

theorem extangcor {a b c d : point} {L: line} (aL: ¬ online a L) (bL: online b L) (dL: online d L) (Bbcd: B b c d) :
  angle a b c < angle a c d :=--Euclid I.16 (Elliptic geometry fails)
begin
  rcases excor (Leasy (B3 Bbcd bL dL) aL).symm (Leasy (B3 Bbcd bL dL) aL) with ⟨g,Bacg,len3⟩,
  have gb: g≠ b:=λ gb,aL (B2 (B1 Bacg).1 (by rwa ← gb at bL) (B3 Bbcd bL dL)),
  have :=aflipboth (B1 Bacg).2.2.2.1.symm gb (B1 Bbcd).2.2.2.1.symm (Leasy dL aL) (vertang bL dL aL Bbcd Bacg),
  rcases Beasy3 Bacg with ⟨N,aN,cN,gN,nq ⟩,
  linarith[extang (λ bN, aL (by rwa G1 (B1 Bbcd).2.1 bN cN bL (B3 Bbcd bL dL) at aN)) aN gN Bacg],
end

theorem sidebigang {a b c : point} {L : line} (bc:b≠ c) (bL: online b L) (cL: online c L) (aL: ¬ online a L) (len: length a b < length a c):
  angle b c a < angle a b c := --Euclid I.18
begin
  rcases excor3 (Leasy bL aL).symm (Leasy bL aL).symm len with ⟨d,Badc,len2 ⟩,
  rcases Beasy3 Badc with ⟨M,aM,dM,cM,nq ⟩,
  have ang:= extangcor (λ bM, aL (by rwa G1 bc bM cM bL cL at aM)) cM aM (B1 Badc).1,
  have db : d≠ b:= Leasy dM (λ bM, aL (by rwa G1 bc bM cM bL cL at aM)),
  have LM : L≠ M := λ LM, aL (by rwa LM.symm at aM),
  rcases LC1 (Leasy bL aL) with ⟨N,bN,aN ⟩,
  have adL: sameside a d L,{by_contra adL,exact Beasy4 (B1 (B1 Badc).1).2.2.2.2 (Pa4 LM (B1 Badc).2.1 aM cM dM cL nq.2.2.symm nq.2.1 adL),},
  rcases LC1 db with ⟨P,dP,bP ⟩,
  have aP: ¬ online a P := λ aP, LM (G1 bc bL cL (by rwa (G1 nq.1 aP dP aM dM) at bP) cM),
  have cdN:= T2 bL bP bN cL dP aN (S2 adL) (Pa3 (B1 Badc).1 dP) aP bc.symm,
  have splitang:= (A2 bL cL bN aN bc (Leasy bL aL) (S3 (S2 cdN)) (S3 (S2 adL)) (λ LN,aL (by rwa ← LN at aN))).mpr ⟨cdN,adL ⟩,
  have := isoangle (B1 Badc).2.1 db len2,
  linarith[M3 bc.symm nq.2.2,M3 db nq.1.symm,M3 nq.1 (Leasy bL aL).symm,(M4 c b d).2,A4mod1 bc.symm (B1 Badc).1,M3 bc db.symm,M3 bc (Leasy bL aL)],
end

theorem angbigside {a b c : point} {L : line} (bc:b≠ c) (bL: online b L) (cL: online c L) (aL: ¬ online a L) (ang: angle b c a < angle a b c):
  length a b < length a c:= --Euclid I.19 -- Probably can be turned into one line
begin
  by_cases len: length a b = length a c,
  {linarith[M3 bc (Leasy bL aL),isoangle (Leasy bL aL).symm bc len],},
  by_cases len2: length a c < length a b,
  {linarith [sidebigang bc.symm cL bL aL len2,M3 bc.symm (Leasy cL aL),M3 bc (Leasy bL aL)],},
  push_neg at len2,exact (ne.le_iff_lt len).mp len2,
end

theorem triineq {a b c : point} {L : line} (ab:a≠ b) (aL: online a L) (bL: online b L) (cL: ¬ online c L):
  length b c < length a b + length a c:= --Euclid I.20
begin
  have bc:= Leasy bL cL,
  rcases excor ab.symm (Leasy aL cL) with ⟨d,Bbad,len ⟩,
  have dc:= Leasy (B2 Bbad bL aL) cL,
  have ang:= isoangle (B1 Bbad).2.2.2.1 dc (flip2 len),
  rcases LC1 (Leasy bL cL) with ⟨M,bM,cM ⟩,
  rcases LC1 dc with ⟨N,dN,cN ⟩,
  have aN:¬ online a N :=λ aN, cL (by rwa ← (G1 (B1 Bbad).2.2.2.1 aL (B2 Bbad bL aL) aN dN ) at cN),
  have adM := Pa2 Bbad bM (λ aM, cL (by rwa (G1 ab aM bM aL bL) at cM)),
  have abN := Pa2 (B1 Bbad).1 dN aN,
  have angsplit:= A2mprmod dc.symm bc.symm cN dN cM bM (S2 adM) (S2 (Pa2 (B1 Bbad).1 dN aN)),
  have bigside:= angbigside dc.symm cN dN (S3 (S2 abN)) (by linarith[A4mod1 dc (B1 Bbad).1,
    M3 dc (B1 Bbad).2.2.1.symm,M3 dc (B1 Bbad).2.2.2.1.symm,M3 dc.symm bc.symm]),
  linarith [M2 b a, M2 c a,DS1 Bbad],
end

theorem trimake {a1 a2 b1 b2 c1 c2 : point}  (ab: length c1 c2 < length a1 a2 + length b1 b2) (bc: length a1 a2 < length b1 b2 + length c1 c2) (ac: length b1 b2  < length a1 a2 + length c1 c2): ∃ (f g k : point), length f g = length a1 a2 ∧ length g k = length b1 b2 ∧ length f k = length c1 c2 :=
begin --Euclid I.22 --anything better?
  have a1a2: a1≠ a2,
  {intro a1a2,rw a1a2 at ac; rw a1a2 at ab,linarith[M1.mpr (rfl:a2=a2)],},
  have b1b2: b1≠ b2,
  {intro b1b2,rw b1b2 at ab; rw b1b2 at bc,linarith[M1.mpr (rfl:b2=b2)],},
  have c1c2: c1≠ c2,
  {intro c1c2,rw c1c2 at ac; rw c1c2 at bc,linarith[M1.mpr (rfl:c2=c2)],},
  rcases excor2 a1a2 b1b2 with ⟨g,Ba1a2g,lenb ⟩,
  rcases excor2 (B1 Ba1a2g).2.2.2.1 c1c2 with ⟨h,Ba2gh,lena ⟩,
  rcases LC2 a1a2.symm with ⟨α,a2cen,a1circ ⟩,
  rcases LC2 (B1 Ba2gh).2.2.2.1 with ⟨β,gcen,hcirc ⟩,
  rcases Beasy3 Ba2gh with ⟨L,a2L,gL,hL,nq ⟩,
  have inon: ¬ inside a1 β ∧ ¬ oncircle a1 β:= ⟨λ a1bet, by linarith [M2 g a1,(DS4 gcen hcirc).mpr a1bet,DS1 Ba1a2g], λ a1bet, by linarith [M2 g a1,DS1 Ba1a2g,(DS3 gcen hcirc).mpr a1bet]⟩,
  rcases I4 (G3 gcen) gL inon.1 inon.2 (B2 (B1 Ba1a2g).1 gL a2L) with ⟨i,icirc,iL,Bgia1 ⟩,
  have ini : inside i α,
  { by_contra ini,
    have ineq :=mt (DS4 a2cen a1circ).mp ini, push_neg at ineq,
    by_cases a2i: a2=i,{linarith [nonzerolen a1a2.symm,M1.mpr a2i],},
    cases Beasy6 a2i Ba1a2g (B1 Bgia1).1 with Bet,
    linarith [DS1 (Beasy7 Bet (B1 Bgia1).1),M2 a2 a1,flip1 ((DS3 gcen icirc).mpr hcirc)],
    linarith[DS1 h_1,M2 a2 i,M2 a2 a1,nonzerolen (B1 h_1).2.1],
  },
  have inh : ¬ inside h α := λ inh, by linarith [(DS4 a2cen a1circ).mpr inh,DS1 Ba2gh,M2 a1 a2],
  rcases I6 (Int4 icirc (by right;exact hcirc) ini inh) with ⟨k,kbet,kalph ⟩,--this is how to handle ors
  refine ⟨k,a2,g, flipboth ((DS3 a2cen kalph).mpr a1circ),lenb,by linarith[flip1 ((DS3 gcen kbet).mpr hcirc)]⟩,
end


theorem angeqpar {a e f d g: point} {L M N : line} (MN: M≠ N) (eM: online e M) (fN: online f N)  (eL: online e L) (fL: online f L) (Baeg: B a e g) (Bfdg: B f d g) (ang: angle a e f = angle e f d) : ¬ online g M ∨ ¬ online g N :=
begin --Euclid I.27
  by_contra gMgN,push_neg at gMgN,
  have fM: ¬ online f M:=λ fM,MN (G1 (B1 Bfdg).2.2.1 fM gMgN.1 fN gMgN.2),
  have eN: ¬ online e N:=λ eN,MN (G1 (B1 Baeg).2.2.2.1 eM gMgN.1 eN gMgN.2),
  have ang1:= extang fM gMgN.1 (B2 (B1 Baeg).1 gMgN.1 eM) (B1 Baeg).1,
  linarith[A4mod1 (Leasy eM fM).symm Bfdg,M3 (B1 Bfdg).2.1.symm (Leasy (B3 Bfdg fN gMgN.2) eN),
    M3 (Leasy eM fM).symm (Leasy (B2 (B1 Baeg).1 gMgN.1 eM) fM).symm],
end

theorem trimakeext {a1 a2 b1 b2 c1 c2 d f: point}  (ab: length c1 c2 < length a1 a2 + length b1 b2)
  (bc: length a1 a2 < length b1 b2 + length c1 c2) (ac: length b1 b2  < length a1 a2 + length c1 c2)
    (len: length d f = length a1 a2): ∃ (k g : point), length k f = length a1 a2 ∧
    length f g = length b1 b2 ∧ length k g = length c1 c2 ∧ B d f g :=

theorem trimake {a1 a2 b1 b2 c1 c2 : point}  (ab: length c1 c2 < length a1 a2 + length b1 b2) (bc: length a1 a2 < length b1 b2 + length c1 c2) (ac: length b1 b2  < length a1 a2 + length c1 c2): ∃ (f g k : point), length f g = length a1 a2 ∧ length g k = length b1 b2 ∧ length f k = length c1 c2 :=
begin --Euclid I.22 --anything better?
  have a1a2: a1≠ a2,
  {intro a1a2,rw a1a2 at ac; rw a1a2 at ab,linarith[M1.mpr (rfl:a2=a2)],},
  have b1b2: b1≠ b2,
  {intro b1b2,rw b1b2 at ab; rw b1b2 at bc,linarith[M1.mpr (rfl:b2=b2)],},
  have c1c2: c1≠ c2,
  {intro c1c2,rw c1c2 at ac; rw c1c2 at bc,linarith[M1.mpr (rfl:c2=c2)],},
  rcases excor2 a1a2 b1b2 with ⟨g,Ba1a2g,lenb ⟩,
  rcases excor2 (B1 Ba1a2g).2.2.2.1 c1c2 with ⟨h,Ba2gh,lena ⟩,
  rcases LC2 a1a2.symm with ⟨α,a2cen,a1circ ⟩,
  rcases LC2 (B1 Ba2gh).2.2.2.1 with ⟨β,gcen,hcirc ⟩,
  rcases Beasy3 Ba2gh with ⟨L,a2L,gL,hL,nq ⟩,
  have inon: ¬ inside a1 β ∧ ¬ oncircle a1 β:= ⟨λ a1bet, by linarith [M2 g a1,(DS4 gcen hcirc).mpr a1bet,DS1 Ba1a2g], λ a1bet, by linarith [M2 g a1,DS1 Ba1a2g,(DS3 gcen hcirc).mpr a1bet]⟩,
  rcases I4 (G3 gcen) gL inon.1 inon.2 (B2 (B1 Ba1a2g).1 gL a2L) with ⟨i,icirc,iL,Bgia1 ⟩,
  have ini : inside i α,
  { by_contra ini,
    have ineq :=mt (DS4 a2cen a1circ).mp ini, push_neg at ineq,
    by_cases a2i: a2=i,{linarith [nonzerolen a1a2.symm,M1.mpr a2i],},
    cases Beasy6 a2i Ba1a2g (B1 Bgia1).1 with Bet,
    linarith [DS1 (Beasy7 Bet (B1 Bgia1).1),M2 a2 a1,flip1 ((DS3 gcen icirc).mpr hcirc)],
    linarith[DS1 h_1,M2 a2 i,M2 a2 a1,nonzerolen (B1 h_1).2.1],
  },
  have inh : ¬ inside h α := λ inh, by linarith [(DS4 a2cen a1circ).mpr inh,DS1 Ba2gh,M2 a1 a2],
  rcases I6 (Int4 icirc (by right;exact hcirc) ini inh) with ⟨k,kbet,kalph ⟩,--this is how to handle ors
  refine ⟨k,a2,g, flipboth ((DS3 a2cen kalph).mpr a1circ),lenb,by linarith[flip1 ((DS3 gcen kbet).mpr hcirc)]⟩,
end

theorem angeqpar2 {a e f d : point} {L M N: line} (ae: a≠ e) (ef: e≠ f) (fd: f ≠ d) (MN: M≠ N) (aM : online a M) (eM: online e M) (fN: online f N) (dN: online d N) (eL: online e L) (fL: online f L) (ang: angle a e f = angle e f d) (adL: diffside a d L) : para a e f d M N :=
begin
  refine ⟨aM,eM, fN,dN,_ ⟩,intro g,by_contra gMN,push_neg at gMN,
  have ML: M≠ L:= λ ML, adL.1 (by rwa ML at aM),
  have NL: N≠ L:= λ NL, adL.2.1 (by rwa NL at dN),
  have eN: ¬ online e N := λ eN, NL (G1 ef eN fN eL fL),
  have fM: ¬ online f M := λ fM, ML (G1 ef eM fM eL fL),
  have gL: ¬ online g L := λ gL, ML (G1 (Leasy gMN.2 eN) gMN.1 eM gL eL),
  have dg: d≠ g,
  {
    intro dg,rw dg at *,
    have Baeg:= Pa4 ML.symm (difneq adL) aM eM gMN.1 eL ae (Leasy eL gL).symm adL.2.2,
    linarith[M3 ae (Leasy aM fM),M3 ef (Leasy dN eN).symm,extang fM gMN.1 aM (B1 Baeg).1],
  },
  have ag: a≠ g,
  {
    intro ag,rw ag at *,
    have Bdfg:= Pa4 NL.symm dg dN fN gMN.2 fL fd.symm (Leasy fL gL).symm (difsym adL.2.2),
    have := extang eN gMN.2 dN (B1 Bdfg).1,
    linarith,
  },
  cases S5 adL.2.1 adL.1 gL (difsym adL.2.2) with dgL agL,
  {
    by_cases Bfdg : B f d g,
    {
      have Baeg:=Pa4 ML.symm ag aM eM gMN.1 eL ae (Leasy gMN.2 eN) (difsym (difsamedif dgL ⟨adL.2.1,adL.1,difsym adL.2.2 ⟩).2.2),
      have ang1:= extang fM gMN.1 (B2 (B1 Baeg).1 gMN.1 eM) (B1 Baeg).1,
      linarith[A4mod1 (Leasy eM fM).symm Bfdg,M3 (Leasy fL (S3 dgL)).symm (Leasy dN eN),M3 (Leasy eM fM).symm (Leasy (B2 (B1 Baeg).1 gMN.1 eM) fM).symm],
    },
    by_cases Bfgd: B f g d,
    {
    have Baeg:=Pa4 ML.symm ag aM eM gMN.1 eL ae (Leasy gMN.2 eN) (difsym (difsamedif dgL ⟨adL.2.1,adL.1,difsym adL.2.2 ⟩).2.2),
    have ang1:= extang fM gMN.1 (B2 (B1 Baeg).1 gMN.1 eM) (B1 Baeg).1,
      have := M3 ae (Leasy aM fM),
      have := M3 ef (Leasy gMN.2 eN).symm,
      have := A4mod1 ef.symm Bfgd,
      have := M3 fd.symm (Leasy dN eN),
      linarith,
    },
    cases B6 fN dN gMN.2 fd (Leasy fL gL) dg,exact Bfdg h,cases h with Bdfg,
    exact (Pa3 Bdfg fL) dgL,exact Bfgd h,
  },
  by_cases Beag : B e a g,
  {
    have Bdfg: B d f g:=Pa4 NL.symm dg dN fN gMN.2 fL fd.symm (Leasy fL gL).symm (difsym (difsamedif agL adL).2.2),
    have ang1:= extang eN gMN.2 dN (B1 Bdfg).1,
    have := A4mod1 ef Beag,linarith,
  },
  by_cases Bega : B e g a,
  {
    have Bdfg: B d f g:=Pa4 NL.symm dg dN fN gMN.2 fL fd.symm (Leasy fL gL).symm (difsym (difsamedif agL adL).2.2),
    have ang1:= extang eN gMN.2 dN (B1 Bdfg).1,
    have := A4mod1 ef Bega,linarith,
  },
  cases B6 eM aM gMN.1 ae.symm (Leasy eL gL) ag,exact Beag h,cases h with Baeg,
  exact (Pa3 Baeg eL) agL,exact Bega h,
end

theorem angeqpar {a e f d g: point} {L M N : line} (MN: M≠ N) (eM: online e M) (fN: online f N)  (eL: online e L) (fL: online f L) (Baeg: B a e g) (Bfdg: B f d g) (ang: angle a e f = angle e f d) : ¬ online g M ∨ ¬ online g N :=
begin --Euclid I.27
  by_contra gMgN,push_neg at gMgN,
  have fM: ¬ online f M:=λ fM,MN (G1 (B1 Bfdg).2.2.1 fM gMgN.1 fN gMgN.2),
  have eN: ¬ online e N:=λ eN,MN (G1 (B1 Baeg).2.2.2.1 eM gMgN.1 eN gMgN.2),
  have ang1:= extang fM gMgN.1 (B2 (B1 Baeg).1 gMgN.1 eM) (B1 Baeg).1,
  linarith[A4mod1 (Leasy eM fM).symm Bfdg,M3 (B1 Bfdg).2.1.symm (Leasy (B3 Bfdg fN gMgN.2) eN),
    M3 (Leasy eM fM).symm (Leasy (B2 (B1 Baeg).1 gMgN.1 eM) fM).symm],
end

theorem angeqpar1 {a e f d g: point} {L M N : line} (dg: d≠ g) (MN: M≠ N) (eM: online e M) (fN: online f N)  (dN: online d N) (eL: online e L) (fL: online f L) (Baeg: B a e g) (dgL: sameside d g L) (ang: angle a e f = angle e f d) : ¬ online g M ∨ ¬ online g N :=
begin --Euclid I.27
  by_contra gMgN,push_neg at gMgN,
  have fM: ¬ online f M:=λ fM,MN (G1 (Leasy fL (S3 (S2 dgL))) fM gMgN.1 fN gMgN.2),
  have eN: ¬ online e N:=λ eN,MN (G1 (B1 Baeg).2.2.2.1 eM gMgN.1 eN gMgN.2),
  have ang1:= extang fM gMgN.1 (B2 (B1 Baeg).1 gMgN.1 eM) (B1 Baeg).1,
  cases B6 fN dN gMgN.2 (Leasy fL (S3 dgL)) (Leasy fL (S3 (S2 dgL))) dg with Bfdg Bet,
  linarith[A4mod1 (Leasy eM fM).symm Bfdg,M3 (Leasy fL (S3 dgL)).symm (Leasy dN eN),
    M3 (Leasy eM fM).symm (Leasy (B2 (B1 Baeg).1 gMgN.1 eM) fM).symm],
  cases Bet with Bdfg Bfgd, exact (Pa3 Bdfg fL) dgL,
  linarith[A4mod1 (Leasy eM fM).symm Bfgd,M3 (Leasy fL (S3 dgL)).symm (Leasy dN eN),
    M3 (Leasy eM fM).symm (Leasy (B2 (B1 Baeg).1 gMgN.1 eM) fM).symm],
end

theorem drawpar {a b c : point} {L: line} (bc: b≠ c) (bL: online b L) (cL: online c L) (aL: ¬ online a L) : ∃ (e: point), ∃ (N: line), para e a b c N L:=
begin --Euclid I.31
  rcases P3 bL cL bc with ⟨d,dL,Bbdc ⟩,rcases LC1 (Leasy dL aL) with ⟨M,dM,aM ⟩,
  have bM: ¬ online b M := λ bM, (Leasy4 aM aL) (G1 bc bM (B2 Bbdc bM dM) bL cL),
  rcases angcopy (Leasy dL aL).symm (B1 Bbdc).2.2.2.1 dL cL aL aM dM bM with ⟨e,ang,ebM ⟩,
  have ae: a≠ e:= λ ae, (S3 ebM) (by rwa ae at aM),
  rcases LC1 ae with ⟨N,aN,eN ⟩,
  refine ⟨ e,N, paraeasy bL (angeqpar ae.symm (Leasy dL aL).symm (B1 Bbdc).2.2.2.1 (Leasy4 aN aL) eN aN dL cL aM dM (by linarith [M3 ae.symm (Leasy dM (S3 ebM)).symm,M3 (Leasy dL aL).symm (Leasy cL aL).symm]) (difsamedif (S2 ebM) ⟨bM,(λ cM, bM (B2 (B1 Bbdc).1 cM dM)),Pa3 Bbdc dM ⟩))⟩,
end


theorem parallelarea1 {a b c d e f : point} {L M K N O P : line} (par1: para a d b c L M) (par2: para b c e f M L) (par3: para a b d c K N) (par4: para b e c f O P) (Baed: B a e d): area b a d + area d b c = area c f e + area e c b := --Euclid I.35
begin
  have ab:= Leasy par1.1 (paraeasy2 par1).2.2.2.1,
  have ad:= Leasy par3.1 (paraeasy2 par3).2.2.2.1,
  have bc:= Leasy par3.2.1 (paraeasy2 par3).2.2.2.2.1,
  have dc:= Leasy par1.2.1 (paraeasy2 par1).2.2.2.2.1,
  have ef:= Leasy par4.2.1 (paraeasy2 par4).2.2.2.2.1,
  have eP:= (paraeasy2 par4).2.2.1,
  have dfM:= (paraeasy2 (paraeasy par1.2.1 par2)).2.2.2.2.2.2,
  have edM:=S4 (S2 (paraeasy2 par2).2.2.2.2.2.2) (S2 dfM),
  have := parasianar par1 par3,
  have := parasianar par2 par4,
  by_cases af: a=f,
  { rw ← af at *,
    have := quadarea ad bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    have := quadarea ef bc par2.2.2.1 par1.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1 (S2 (paraeasy2 par4).2.2.2.2.2.1),
    have := sss (by linarith :length a d =length e a) (parasianar par3 par1).1.symm (flipboth (parasianar par4 par2).1).symm,
    have := M9 (by linarith :length a d =length e a) (parasianar par3 par1).1.symm  (parasianar par4 par2).1.symm this.1 this.2.1 this.2.2,
    linarith[M8 d c b, M8 d a b, M8 b d a, M8 c b e,M8 c b a, M8 c d a,M8 a c d, M8 a e b, M8 a b e],
  },
  by_cases ed: e=d,{ rw ed at *,linarith,},
  by_cases df: d=f,
  {rw ← df at *,
    have NP:= G1 dc par3.2.2.1 par3.2.2.2.1 par4.2.2.2.1 par4.2.2.1, rw ← NP at *,
    by_cases ae: a≠ e,
    {
      exfalso,
      cases B6 par1.1 par2.2.2.1 par1.2.1 ae ad ed,
      have :=DS1 h, have := nonzerolen ae,linarith,cases h,
      have := DS1 h, have := nonzerolen ae.symm, linarith,
      have aeN:= Pa3 h par3.2.2.1,
      have abN:= (paraeasy2 par3).2.2.2.2.2.1,
      exact (difsamedif abN ⟨S3 abN,(paraeasy2 par4).2.2.1,aeN ⟩).2.2 (paraeasy2 par4).2.2.2.2.2.1,
    },
    push_neg at ae,
    rw ae at *,
    have := quadarea ad bc par2.2.2.1 par2.2.2.2.1 par2.1 par2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    linarith[M8 c b e, M8 d c b, M8 b d e, M8 d e b],
  },
  by_cases ae: a=e,
  { exfalso, rw ← ae at *,
    have OK:= G1 ab par4.2.1 par4.1 par3.1 par3.2.1, rw OK at *,
    cases B6 par1.1 par1.2.1 par2.2.2.2.1 ad af df,
    have := DS1 h, linarith [nonzerolen df], cases h,
    have fdK:=difsym (Pa3 h par3.1),
    have fcK:=S2 (paraeasy2 par4).2.2.2.2.2.2,
    exact (difsamedif fcK ⟨(paraeasy2 par4).2.2.2.2.1,(paraeasy2 par3).2.2.2.1,fdK ⟩).2.2 (S2 (paraeasy2 par3).2.2.2.2.2.2),
    have := DS1 h, linarith [nonzerolen df, M2 d f],
  },
  have Bedf: B e d f,
  {
    cases B6 par2.2.2.1 par1.2.1 par2.2.2.2.1 ed (Leasy par4.2.2.2.1 eP).symm df, exact h,exfalso,
    cases h with Bdef Befd,
    {
      cases or.swap (Beasy5 af (B1 Baed).1 Bdef) with Befa Beaf,
      have := DS1 Befa, have := DS1 Baed,linarith[M2 e a, nonzerolen af, M2 a f, nonzerolen ed],
      have dP: ¬ online d P:=λ dP,eP (B3 (B1 Bdef).1 par4.2.2.2.1 dP),
      by_cases bfN: sameside b f N,
      {
        have dbP:=difsym (T1 par1.2.2.2.1 par4.2.2.1 par3.2.2.2.1 par2.1  par4.2.2.2.1 par3.2.2.1 (S2 dfM) bfN),
        have deP:=S2 (Pa2 (B1 Bdef).1 par4.2.2.2.1 eP),
        exact (difsamedif deP ⟨dP,(paraeasy2 par4).2.1,dbP ⟩).2.2 (S2 (paraeasy2 par4).2.2.2.2.2.1),
      },
      have Bfad:= B5 (B1 Beaf).1 Baed,
      have afN:=Pa2 (B1 Bfad).1 par3.2.2.1 (paraeasy2 par3).2.1,
      exact bfN (S2 (S4 afN (paraeasy2 par3).2.2.2.2.2.1)),
    },
    linarith[DS1 Befd,DS1 Baed,nonzerolen ae,nonzerolen df,M2 d f],
  },
  have := DA2mpmod par1.1 par1.2.1 par2.2.2.1 (paraeasy2 par1).2.2.2.1 Baed,
  have eN: ¬ online e N:=λ eN,(paraeasy2 par3).2.1 (B2 (B1 Baed).1 par3.2.2.1 eN),
  have ebN:=S4 (S2 (Pa2 (B1 Baed).1 par3.2.2.1 eN)) (paraeasy2 par3).2.2.2.2.2.1,
  have := quadarea ed bc par2.2.2.1 par1.2.1 par2.1 par2.2.1 par3.2.2.1 par3.2.2.2.1 edM (paraeasy2 par2).2.2.2.2.2.1 ebN,
  have := parasianar par3 par1,
  have := DS1 Baed, have := DS1 Bedf,
  have := sss (by linarith : length a e = length d f).symm (flipboth (parasianar par4 par2).1).symm (parasianar par3 par1).1.symm,
  have := M9 (by linarith : length a e = length d f).symm  (flipboth (parasianar par4 par2).1.symm) (flipboth (parasianar par3 par1).1).symm this.1 this.2.1 this.2.2,
  have := DA2mpmod par2.2.2.1 par2.2.2.2.1 par1.2.1 (paraeasy2 par1).2.2.2.2.1 Bedf,
  linarith [M8 b a d, M8 b d a, M8 d c b, M8 d e b, M8 b d e, M8 e d c , M8 c e d, M8 d f c, M8 c f e, M8 c b e],
end

theorem parallelarea1 {a b c d e f : point} {L M K N O P : line} (par1: para a d b c L M) (par2: para b c e f M L) (par3: para a b d c K N) (par4: para b e c f O P) (Baed: B a e d): area b a d + area d b c = area c f e + area e c b := --Euclid I.35
begin
  have ab:= Leasy par1.1 (paraeasy2 par1).2.2.2.1,
  have ad:= Leasy par3.1 (paraeasy2 par3).2.2.2.1,
  have bc:= Leasy par3.2.1 (paraeasy2 par3).2.2.2.2.1,
  have dc:= Leasy par1.2.1 (paraeasy2 par1).2.2.2.2.1,
  have ef:= Leasy par4.2.1 (paraeasy2 par4).2.2.2.2.1,
  have eP:= (paraeasy2 par4).2.2.1,
  have dfM:= (paraeasy2 (paraeasy par1.2.1 par2)).2.2.2.2.2.2,
  have edM:=S4 (S2 (paraeasy2 par2).2.2.2.2.2.2) (S2 dfM),
  have := parasianar par1 par3,
  have := parasianar par2 par4,
  by_cases af: a=f,
  { rw ← af at *,
    have := quadarea ad bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    have := quadarea ef bc par2.2.2.1 par1.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1 (S2 (paraeasy2 par4).2.2.2.2.2.1),
    have := sss (by linarith :length a d =length e a) (parasianar par3 par1).1.symm (flipboth (parasianar par4 par2).1).symm,
    have := M9 (by linarith :length a d =length e a) (parasianar par3 par1).1.symm  (parasianar par4 par2).1.symm this.1 this.2.1 this.2.2,
    linarith[M8 d c b, M8 d a b, M8 b d a, M8 c b e,M8 c b a, M8 c d a,M8 a c d, M8 a e b, M8 a b e],
  },
  by_cases ed: e=d,{ rw ed at *,linarith,},
  by_cases df: d=f,
  {rw ← df at *,
    have NP:= G1 dc par3.2.2.1 par3.2.2.2.1 par4.2.2.2.1 par4.2.2.1, rw ← NP at *,
    by_cases ae: a≠ e,
    {
      exfalso,
      cases B6 par1.1 par2.2.2.1 par1.2.1 ae ad ed,
      have :=DS1 h, have := nonzerolen ae,linarith,cases h,
      have := DS1 h, have := nonzerolen ae.symm, linarith,
      have aeN:= Pa3 h par3.2.2.1,
      have abN:= (paraeasy2 par3).2.2.2.2.2.1,
      exact (difsamedif abN ⟨S3 abN,(paraeasy2 par4).2.2.1,aeN ⟩).2.2 (paraeasy2 par4).2.2.2.2.2.1,
    },
    push_neg at ae,
    rw ae at *,
    have := quadarea ad bc par2.2.2.1 par2.2.2.2.1 par2.1 par2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    linarith[M8 c b e, M8 d c b, M8 b d e, M8 d e b],
  },
  by_cases ae: a=e,
  { exfalso, rw ← ae at *,
    have OK:= G1 ab par4.2.1 par4.1 par3.1 par3.2.1, rw OK at *,
    cases B6 par1.1 par1.2.1 par2.2.2.2.1 ad af df,
    have := DS1 h, linarith [nonzerolen df], cases h,
    have fdK:=difsym (Pa3 h par3.1),
    have fcK:=S2 (paraeasy2 par4).2.2.2.2.2.2,
    exact (difsamedif fcK ⟨(paraeasy2 par4).2.2.2.2.1,(paraeasy2 par3).2.2.2.1,fdK ⟩).2.2 (S2 (paraeasy2 par3).2.2.2.2.2.2),
    have := DS1 h, linarith [nonzerolen df, M2 d f],
  },
  have Bedf: B e d f,
  {
    cases B6 par2.2.2.1 par1.2.1 par2.2.2.2.1 ed (Leasy par4.2.2.2.1 eP).symm df, exact h,exfalso,
    cases h with Bdef Befd,
    {
      cases or.swap (Beasy5 af (B1 Baed).1 Bdef) with Befa Beaf,
      have := DS1 Befa, have := DS1 Baed,linarith[M2 e a, nonzerolen af, M2 a f, nonzerolen ed],
      have dP: ¬ online d P:=λ dP,eP (B3 (B1 Bdef).1 par4.2.2.2.1 dP),
      by_cases bfN: sameside b f N,
      {
        have dbP:=difsym (T1 par1.2.2.2.1 par4.2.2.1 par3.2.2.2.1 par2.1  par4.2.2.2.1 par3.2.2.1 (S2 dfM) bfN),
        have deP:=S2 (Pa2 (B1 Bdef).1 par4.2.2.2.1 eP),
        exact (difsamedif deP ⟨dP,(paraeasy2 par4).2.1,dbP ⟩).2.2 (S2 (paraeasy2 par4).2.2.2.2.2.1),
      },
      have Bfad:= B5 (B1 Beaf).1 Baed,
      have afN:=Pa2 (B1 Bfad).1 par3.2.2.1 (paraeasy2 par3).2.1,
      exact bfN (S2 (S4 afN (paraeasy2 par3).2.2.2.2.2.1)),
    },
    linarith[DS1 Befd,DS1 Baed,nonzerolen ae,nonzerolen df,M2 d f],
  },
  have := DA2mpmod par1.1 par1.2.1 par2.2.2.1 (paraeasy2 par1).2.2.2.1 Baed,
  have eN: ¬ online e N:=λ eN,(paraeasy2 par3).2.1 (B2 (B1 Baed).1 par3.2.2.1 eN),
  have ebN:=S4 (S2 (Pa2 (B1 Baed).1 par3.2.2.1 eN)) (paraeasy2 par3).2.2.2.2.2.1,
  have := quadarea ed bc par2.2.2.1 par1.2.1 par2.1 par2.2.1 par3.2.2.1 par3.2.2.2.1 edM (paraeasy2 par2).2.2.2.2.2.1 ebN,
  have := parasianar par3 par1,
  have := DS1 Baed, have := DS1 Bedf,
  have := sss (by linarith : length a e = length d f).symm (flipboth (parasianar par4 par2).1).symm (parasianar par3 par1).1.symm,
  have := M9 (by linarith : length a e = length d f).symm  (flipboth (parasianar par4 par2).1.symm) (flipboth (parasianar par3 par1).1).symm this.1 this.2.1 this.2.2,
  have := DA2mpmod par2.2.2.1 par2.2.2.2.1 par1.2.1 (paraeasy2 par1).2.2.2.2.1 Bedf,
  linarith [M8 b a d, M8 b d a, M8 d c b, M8 d e b, M8 b d e, M8 e d c , M8 c e d, M8 d f c, M8 c f e, M8 c b e],
end

theorem parallelarea2 {a b c d e f : point} {L M K N O P : line} (par1: para a d b c L M) (par2: para b c e f M L) (par3: para a b d c K N) (par4: para b e c f O P) (Bade: B a d e): area b a d + area d b c = area c f e + area e c b := --Euclid I.35
begin
  have ab:= Leasy par1.1 (paraeasy2 par1).2.2.2.1,
  have ad:= Leasy par3.1 (paraeasy2 par3).2.2.2.1,
  have bc:= Leasy par3.2.1 (paraeasy2 par3).2.2.2.2.1,
  have dc:= Leasy par1.2.1 (paraeasy2 par1).2.2.2.2.1,
  have ef:= Leasy par4.2.1 (paraeasy2 par4).2.2.2.2.1,
  have eP:= (paraeasy2 par4).2.2.1,
  have dfM:= (paraeasy2 (paraeasy par1.2.1 par2)).2.2.2.2.2.2,
  have edM:=S4 (S2 (paraeasy2 par2).2.2.2.2.2.2) (S2 dfM),
  have := parasianar par1 par3,
  have := parasianar par2 par4,
  by_cases af: a=f,
  { rw ← af at *,
    have := quadarea ad bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    have := quadarea ef bc par2.2.2.1 par1.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1 (S2 (paraeasy2 par4).2.2.2.2.2.1),
    have := sss (by linarith :length a d =length e a) (parasianar par3 par1).1.symm (flipboth (parasianar par4 par2).1).symm,
    have := M9 (by linarith :length a d =length e a) (parasianar par3 par1).1.symm  (parasianar par4 par2).1.symm this.1 this.2.1 this.2.2,
    linarith[M8 d c b, M8 d a b, M8 b d a, M8 c b e,M8 c b a, M8 c d a,M8 a c d, M8 a e b, M8 a b e],
  },
  by_cases df: d=f,
  {rw ← df at *,
    have NP:= G1 dc par3.2.2.1 par3.2.2.2.1 par4.2.2.2.1 par4.2.2.1, rw ← NP at *,

    {
      exfalso,
      cases B6 par1.1 par2.2.2.1 par1.2.1 (B1 Bade).2.2.1 ad (B1 Bade).2.2.2.1.symm,
      have :=DS1 h, have := nonzerolen (B1 Bade).2.2.1,linarith,cases h,
      have := DS1 h, have := nonzerolen (B1 Bade).2.2.1.symm, linarith,
      have aeN:= Pa3 h par3.2.2.1,
      have abN:= (paraeasy2 par3).2.2.2.2.2.1,
      exact (difsamedif abN ⟨S3 abN,(paraeasy2 par4).2.2.1,aeN ⟩).2.2 (paraeasy2 par4).2.2.2.2.2.1,
    },

  },
  have Bdef: B d e f,
  {
    cases B6 par1.2.1 par2.2.2.1 par2.2.2.2.1 (B1 Bade).2.2.2.1 df ef, exact h, exfalso, cases h with Bedf Bdfe,
    {
      by_cases bfN:sameside b f N,
      {
        have dP: ¬ online d P:=λ dP,eP (B2 (B1 Bedf).1 par4.2.2.2.1 dP),
        have dbP:=difsym (T1 par1.2.2.2.1 par4.2.2.1 par3.2.2.2.1 par2.1  par4.2.2.2.1 par3.2.2.1 (S2 dfM) bfN),
        have deP:= (Pa2 (B1 Bedf).1 par4.2.2.2.1 dP),
        exact (difsamedif deP ⟨dP,(paraeasy2 par4).2.1,dbP ⟩).2.2 (S2 (paraeasy2 par4).2.2.2.2.2.1),
      },
      cases Beasy5 af  (B1 Bade).1 Bedf with Bdaf Bdfa, have := DS1 Bdaf, have := DS1 Bedf, linarith[nonzerolen (B1 Bade).2.2.2.1.symm, nonzerolen af, M2 a d],
      have fN: ¬ online f N := λ fN,(paraeasy2 par3).2.1 (B2 Bdfa par3.2.2.1 fN),
      exact (difsamedif (S2 (paraeasy2 par3).2.2.2.2.2.1) ⟨(paraeasy2 par3).2.2.1,fN,bfN ⟩).2.2 (S2 (Pa2 Bdfa par3.2.2.1 fN)),
    },
    have Bfda:= Beasy7 (B1 Bdfe).1 (B1 Bade).1,
    by_cases bfN: sameside b f N,
    {
      have afN:=S4 (S2 (paraeasy2 par3).2.2.2.2.2.1) bfN,
      exact (Pa3 Bfda par3.2.2.1) (S2 afN),
    },
    have fN: ¬ online f N := λ fN,(paraeasy2 par3).2.1 (B2 Bfda fN par3.2.2.1),

    have bdP:= T2 par1.2.2.2.1 par3.2.2.2.1 par4.2.2.1 par1.2.2.1 par3.2.2.1 par4.2.2.2.1 dfM bfN fN bc,
    exact (Pa3 Bdfe par4.2.2.2.1) (S4 bdP (paraeasy2 par4).2.2.2.2.2.1),
  },
  have dO: ¬ online d O := λ dO, (paraeasy2 par4).2.2.2.2.1 (B2 Bdef dO par4.2.1),
  have eN: ¬ online e N := λ eN, (paraeasy2 par3).2.1 (B2 (B1 Bade).1 eN par3.2.2.1),
  have cdO:= (difsamedif (S2 (paraeasy2 par4).2.2.2.2.2.2) ⟨(paraeasy2 par4).2.2.2.2.1,dO,difsym (Pa3 Bdef par4.2.1)⟩).2.2,
  have beN:= (difsamedif (paraeasy2 par3).2.2.2.2.2.1 ⟨(paraeasy2 par3).2.1, eN,(Pa3 Bade par3.2.2.1)⟩).2.2,
  rcases I1 (Int1 beN par4.1 par4.2.1) with ⟨g,gN,gO ⟩ ,
  have Bbge:= Pa4 (Leasy4 par4.2.1 eN).symm (Leasy par1.2.2.1 (paraeasy2 par2).2.2.2.1) par4.1 gO par4.2.1 gN (Leasy gN (paraeasy2 par3).2.2.1).symm (Leasy gN eN).symm beN,
  have Bcgd:= Pa4 (Leasy4 par4.2.1 eN) dc.symm par3.2.2.2.1 gN par3.2.2.1 gO (Leasy gO (paraeasy2 par4).2.2.2.1).symm (Leasy gO dO).symm cdO,
  have cO: ¬ online c O := λ cO, dO (B2 Bcgd cO gO),
  have bN: ¬ online b N := λ bN, eN (B2 Bbge bN gN),
  have := parasianar par3 par1,
  have := DS1 Bade, have := DS1 Bdef,
  have := sss (by linarith : length a e = length d f).symm (flipboth (parasianar par4 par2).1).symm (parasianar par3 par1).1.symm,
  have := M9 (by linarith : length a e = length d f).symm  (flipboth (parasianar par4 par2).1.symm) (flipboth (parasianar par3 par1).1).symm this.1 this.2.1 this.2.2,
  have := DA2mpmod par4.1 par4.2.1 gO dO Bbge,
  have := DA2mpmod par4.1 par4.2.1 gO cO Bbge,
  have := DA2mpmod par3.2.2.2.1 par3.2.2.1 gN bN Bcgd,
  have := DA2mpmod par3.2.2.2.1 par3.2.2.1 gN eN Bcgd,
  have := DA2mpmod par1.1 par2.2.2.1 par1.2.1 (paraeasy2 par2).2.1 Bade,
  have := DA2mpmod par1.2.1 par2.2.2.2.1 par2.2.2.1 (paraeasy2 par2).2.2.1 Bdef,
  linarith[M8 d c f, M8 c e f, M8 d e c, M8 c d e, M8 a b e, M8 a d b, M8 e g d, M8 d e g, M8 c b d, M8 d c b, M8 b g c,M8 c b g, M8 e c b, M8 b e c],
end

theorem parallelarea3 {a b c d e f : point} {L M K N O P : line} (par1: para a d b c L M) (par2: para b c e f M L) (par3: para a b d c K N) (par4: para b e c f O P) (Bdae: B d a e): area b a d + area d b c = area c f e + area e c b := --Euclid I.35
begin
  have ab:= Leasy par1.1 (paraeasy2 par1).2.2.2.1,
  have ad:= Leasy par3.1 (paraeasy2 par3).2.2.2.1,
  have bc:= Leasy par3.2.1 (paraeasy2 par3).2.2.2.2.1,
  have dc:= Leasy par1.2.1 (paraeasy2 par1).2.2.2.2.1,
  have ef:= Leasy par4.2.1 (paraeasy2 par4).2.2.2.2.1,
  have eP:= (paraeasy2 par4).2.2.1,
  have dfM:= (paraeasy2 (paraeasy par1.2.1 par2)).2.2.2.2.2.2,
  have edM:=S4 (S2 (paraeasy2 par2).2.2.2.2.2.2) (S2 dfM),
  have := parasianar par1 par3,
  have := parasianar par2 par4,
  by_cases af: a=f,
  { rw ← af at *,
    have := quadarea ad bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    have := quadarea ef bc par2.2.2.1 par1.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1 (S2 (paraeasy2 par4).2.2.2.2.2.1),
    have := sss (by linarith :length a d =length e a) (parasianar par3 par1).1.symm (flipboth (parasianar par4 par2).1).symm,
    have := M9 (by linarith :length a d =length e a) (parasianar par3 par1).1.symm  (parasianar par4 par2).1.symm this.1 this.2.1 this.2.2,
    linarith[M8 d c b, M8 d a b, M8 b d a, M8 c b e,M8 c b a, M8 c d a,M8 a c d, M8 a e b, M8 a b e],
  },
  by_cases df: d=f,
  {rw ← df at *,
    have NP:= G1 dc par3.2.2.1 par3.2.2.2.1 par4.2.2.2.1 par4.2.2.1, rw ← NP at *,

    {
      exfalso,
      cases B6 par1.1 par2.2.2.1 par1.2.1 (B1 Bdae).2.2.2.1 ad (B1 Bdae).2.2.1.symm,
      have :=DS1 h, have := nonzerolen (B1 Bdae).2.2.2.1,linarith,cases h,
      have := DS1 h, have := nonzerolen (B1 Bdae).2.2.2.1.symm, linarith,
      have aeN:= Pa3 h par3.2.2.1,
      have abN:= (paraeasy2 par3).2.2.2.2.2.1,
      exact (difsamedif abN ⟨S3 abN,(paraeasy2 par4).2.2.1,aeN ⟩).2.2 (paraeasy2 par4).2.2.2.2.2.1,
    },

  },
  have key: B d f a ∨ B d a f,
  {
    by_contra key, push_neg at key,
    cases B6 par1.2.1 par2.2.2.2.1 par1.1 df ad.symm (ne.symm af), exact key.1 h, cases h,
    have :=DS1 (B5 h Bdae), have := DS1 Bdae, linarith[M2 a d, M2 e f, nonzerolen  (B1 Bdae).2.2.2.1,nonzerolen (B1 h).2.1], exact key.2 h,
  },
  cases key,
  have := parallelarea1 (paraeasy3 par1) (paraeasy3 par2) (paraeasy4 par3) (paraeasy4 par4) key,
  have := quadarea (B1 key).2.2.1.symm bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.2 (paraeasy2 par3).2.2.2.2.2.1,
  have := quadarea ef bc par2.2.2.1 par2.2.2.2.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par1).2.2.2.2.2.2 (S2 (paraeasy2 par4).2.2.2.2.2.1),
  linarith[M8 b a d, M8 d b a, M8 d b c, M8 c b e, M8 c b a, M8 b e f, M8 f b e, M8 f b c],
  have := parallelarea2 (paraeasy3 par1) (paraeasy3 par2) (paraeasy4 par3) (paraeasy4 par4) key,
  have := quadarea (B1 key).2.1.symm bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.2 (paraeasy2 par3).2.2.2.2.2.1,
  have := quadarea ef bc par2.2.2.1 par2.2.2.2.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par1).2.2.2.2.2.2 (S2 (paraeasy2 par4).2.2.2.2.2.1),
  linarith[M8 b a d, M8 d b a, M8 d b c, M8 c b e, M8 c b a, M8 b e f, M8 f b e, M8 f b c],
end

theorem parallelarea {a b c d e f : point} {L M K N O P : line} (par1: para a d b c L M) (par2: para b c e f M L) (par3: para a b d c K N) (par4: para b e c f O P): area b a d + area d b c = area c f e + area e c b := --Euclid I.35
begin
  have ab:= Leasy par1.1 (paraeasy2 par1).2.2.2.1,
  have ad:= Leasy par3.1 (paraeasy2 par3).2.2.2.1,
  have bc:= Leasy par3.2.1 (paraeasy2 par3).2.2.2.2.1,
  have dc:= Leasy par1.2.1 (paraeasy2 par1).2.2.2.2.1,
  have ef:= Leasy par4.2.1 (paraeasy2 par4).2.2.2.2.1,
  have eP:= (paraeasy2 par4).2.2.1,
  have dfM:= (paraeasy2 (paraeasy par1.2.1 par2)).2.2.2.2.2.2,
  have edM:=S4 (S2 (paraeasy2 par2).2.2.2.2.2.2) (S2 dfM),
  have := parasianar par1 par3,
  have := parasianar par2 par4,
  by_cases af: a=f,
  { rw ← af at *,
    have := quadarea ad bc par1.1 par1.2.1 par1.2.2.1 par1.2.2.2.1 par3.2.2.1 par3.2.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    have := quadarea ef bc par2.2.2.1 par1.1 par1.2.2.1 par1.2.2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par2).2.2.2.2.2.2 (paraeasy2 par2).2.2.2.2.2.1 (S2 (paraeasy2 par4).2.2.2.2.2.1),
    have := sss (by linarith :length a d =length e a) (parasianar par3 par1).1.symm (flipboth (parasianar par4 par2).1).symm,
    have := M9 (by linarith :length a d =length e a) (parasianar par3 par1).1.symm  (parasianar par4 par2).1.symm this.1 this.2.1 this.2.2,
    linarith[M8 d c b, M8 d a b, M8 b d a, M8 c b e,M8 c b a, M8 c d a,M8 a c d, M8 a e b, M8 a b e],
  },
  by_cases ed: e=d,{ rw ed at *,linarith,},
  by_cases df: d=f,
  {rw ← df at *,
    have NP:= G1 dc par3.2.2.1 par3.2.2.2.1 par4.2.2.2.1 par4.2.2.1, rw ← NP at *,
    by_cases ae: a≠ e,
    {
      exfalso,
      cases B6 par1.1 par2.2.2.1 par1.2.1 ae ad ed,
      have :=DS1 h, have := nonzerolen ae,linarith,cases h,
      have := DS1 h, have := nonzerolen ae.symm, linarith,
      have aeN:= Pa3 h par3.2.2.1,
      have abN:= (paraeasy2 par3).2.2.2.2.2.1,
      exact (difsamedif abN ⟨S3 abN,(paraeasy2 par4).2.2.1,aeN ⟩).2.2 (paraeasy2 par4).2.2.2.2.2.1,
    },
    push_neg at ae,
    rw ae at *,
    have := quadarea ad bc par2.2.2.1 par2.2.2.2.1 par2.1 par2.2.1 par4.2.2.2.1 par4.2.2.1 (paraeasy2 par1).2.2.2.2.2.1 (paraeasy2 par2).2.2.2.2.2.1 (paraeasy2 par3).2.2.2.2.2.1,
    linarith[M8 c b e, M8 d c b, M8 b d e, M8 d e b],
  },
  by_cases ae: a=e,
  { exfalso, rw ← ae at *,
    have OK:= G1 ab par4.2.1 par4.1 par3.1 par3.2.1, rw OK at *,
    cases B6 par1.1 par1.2.1 par2.2.2.2.1 ad af df,
    have := DS1 h, linarith [nonzerolen df], cases h,
    have fdK:=difsym (Pa3 h par3.1),
    have fcK:=S2 (paraeasy2 par4).2.2.2.2.2.2,
    exact (difsamedif fcK ⟨(paraeasy2 par4).2.2.2.2.1,(paraeasy2 par3).2.2.2.1,fdK ⟩).2.2 (S2 (paraeasy2 par3).2.2.2.2.2.2),
    have := DS1 h, linarith [nonzerolen df, M2 d f],
  },
  cases B6 par1.1 par2.2.2.1 par1.2.1 ae ad ed, exact parallelarea1 par1 par2 par3 par4 h, cases h, exact parallelarea3 par1 par2 par3 par4 (B1 h).1, exact parallelarea2 par1 par2 par3 par4 h,
end

theorem parallelodraw {a d b c : point} {L M N: line} (ad: a≠ d) (bc: b≠ c) (aN: online a N) (cN: online c N) (par: para a d b c L M) : ∃ (e: point) (O: line), para e b a c O N ∧ para e a b c L M :=
begin

end

theorem parallelodraw {a d b c : point} {L M N: line} (ad: a≠ d) (bc: b≠ c) (aN: online a N) (cN: online c N) (par: para a d b c L M) (bdN: ¬ sameside b d N ): ∃ (e: point) (P: line), para e b a c P N ∧ para e a b c L M ∧ B d a e:=
begin --Lemma for I.37
  rcases LC1 (Leasy par.1 (paraeasy2 par).2.2.2.1) with ⟨O,aO,bO ⟩,
  have bN:=λ bN, (paraeasy2 par).2.1 (by rwa (G1 bc bN cN par.2.2.1 par.2.2.2.1) at aN),
  rcases excor2 ad.symm bc with ⟨e,Bdae,len ⟩,
  have dcO:= T2 par.1 aN aO par.2.1 cN bO (S2 (paraeasy2 par).2.2.2.2.2.2) (difsym bdN) bN ad.symm,
  have deO:= Pa3 Bdae aO,
  have dO:= S3 dcO,
  have ecO:= (difsamedif dcO ⟨dO,λ eO, dO (B2 (B1 Bdae).1 eO aO),deO ⟩),
  have par2:= paraeasy5 (paraeasy (B2 Bdae par.2.1 par.1) (paraeasy5 (paraeasy4 (paraeasy5 par)))),
  have := parapostcor (B1 Bdae).2.2.2.1.symm aO bO (paraeasy5 (paraeasy (B2 Bdae par.2.1 par.1) (paraeasy5 (paraeasy4 (paraeasy5 par))))) ecO,
  have eb:= (Leasy par2.2.2.2.1 (paraeasy2 par2).2.2.1),
  have := sas len (M2 a b) (by linarith[M3 (B1 Bdae).2.2.2.1.symm eb]),
  rcases LC1 eb with ⟨P,eP,bP ⟩,
  have := angeqpar eb (Leasy aN bN).symm (Leasy par.1 (paraeasy2 par).2.2.2.2.1) (Leasy4 bP bN) eP bP aN cN bO aO (by linarith [M3 eb (B1 Bdae).2.2.2.1.symm]) ⟨ecO.2.1,ecO.1,difsym ecO.2.2 ⟩,
  refine ⟨e,P,this,paraeasy1 par2,Bdae ⟩,
end

theorem triarea {a d b c : point} {L M : line} (par: para a d b c L M) : area a b c = area d b c :=
begin --Euclid I.37
  by_cases ad: a=d,rw ad,
  by_cases bc: b=c,rw bc, linarith [M8 a c c, M8 c a c, M8 d c c, M8 c d c, M6 c a, M6 c d],
  rcases LC1 (Leasy par.1 (paraeasy2 par).2.2.2.2.1) with ⟨N,aN,cN ⟩,
  rcases LC1 (Leasy par.2.2.1 (paraeasy2 par).2.2.1) with ⟨Q,bQ,dQ ⟩,
  rcases LC1 (Leasy par.2.1 (paraeasy2 par).2.2.2.2.1) with ⟨K,dK,cK ⟩,
  rcases LC1 (Leasy par.1 (paraeasy2 par).2.2.2.1) with ⟨O,aO,bO ⟩,
  have bN:=λ bN, (paraeasy2 par).2.1 (by rwa (G1 bc bN cN par.2.2.1 par.2.2.2.1) at aN),
  by_cases bdN: ¬ sameside b d N,
  { rcases parallelodraw ad bc aN cN par bdN with ⟨e,P,par1,par2,Bdae ⟩,
    have baK:= T2 par.2.2.2.1 cN cK par.2.2.1 aN dK (paraeasy2 par).2.2.2.2.2.1 bdN (λ dN, (paraeasy2 par1).2.1 (B2 Bdae dN aN)) bc,
    have acQ:= T1 par.2.1 dQ dK par.1 bQ cK (paraeasy2 par).2.2.2.2.2.2 (S2 baK),
    rcases parallelodraw (ne.symm ad) (ne.symm bc) dQ bQ (paraeasy3 par) (difsym acQ) with ⟨f,R,par3,par4,Badf ⟩,
    have := parallelarea par2 (paraeasy1 par4) par1 (paraeasy1 par3),
    have := parasianar par2 par1,
    have := parasianar par4 par3,
    linarith [M8 a c b, M8 d b c],
  },push_neg at bdN,
  have baK:= T1 par.2.2.2.1 cK cN par.2.2.1 dK aN (S2 (paraeasy2 par).2.2.2.2.2.1) bdN,
  have dcO:= T1 par.1 aO aN par.2.1 bO cN (paraeasy2 par).2.2.2.2.2.2 (S2 bdN),
  rcases parallelodraw (ne.symm ad) bc dK cK (paraeasy6 par) baK with ⟨e,P,par1,par2,Bade ⟩,
  rcases parallelodraw ad (ne.symm bc) aO bO (paraeasy5 par) (difsym dcO) with ⟨f,R,par3,par4,Bdaf ⟩,
  have := parallelarea par2 (paraeasy1 par4) par1 (paraeasy1 par3),
  have := parasianar par2 par1,
  have := parasianar par4 par3,
  linarith [M8 a c b, M8 d b c],
end

/-
theorem intercircdif {a b c : point} {α β : circle} (ab: a≠ b ) (acen : center a α) (bcen: center b β ) (calph: oncircle c α ) (cbet: oncircle c β ) : c≠ a ∧ c≠ b :=
begin
  split,intro ca,
  {
    rw ca at calph,
    have := G4 a α (G3 acen),
    exact this calph,
  },
  intro cb,
  rw cb at cbet,
  have := G4 b β (G3 bcen),
  exact this cbet,
end
-/

/- why is this hard?
theorem intercirccirccom {a b : point} {α β : circle} (ab: a≠ b) (acen: center a α) (bcen: center b β) (inter: intercirclecircle α β) : intercirclecircle β α :=
begin
  rcases I7 inter with ⟨c,d,calph,cbet,dalph,dbet,cd ⟩,
  rcases LC1 ab with ⟨L,aL,bL ⟩,
  rcases I3 (Int3 (G3 acen) aL) with ⟨c1,c2,c1L,c2L,c1circ,c2circ,c1c2 ⟩,
  have Bc1ac2:= C1 aL c1L c2L (G3 acen) c1circ c2circ c1c2,
  by_cases acirc: oncircle a β,
  {
    by_cases bcirc: oncircle b α,
    {
      exact Int5 (G3 bcen) acirc (G3 acen) bcirc,
    },

  },
end
-/
-/
