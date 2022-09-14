/-
Copyright (c) 2022 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : André Hernandez-Espiet
-/

import data.real.basic
import data.real.sqrt

/-!
# Synthetic Geometry, Euclid's Elements Book I using Avigad Axioms
In this file we ...
## Main definitions
* `incidence_geometry` : class containing axioms...
## Main results
* `pythagorean_theorem` : The Pythagorean theorem
## Tags
synthetic geometry, Euclid elements
-/


universes u1 u2 u3
class incidence_geometry :=
(point : Type u1)
(line : Type u2)
(circle : Type u3)

(online : point → line → Prop)
(sameside : point → point → line → Prop)
(B : point → point → point → Prop) -- Betweenness
(oncircle : point → circle → Prop)
(inside_circle : point → circle → Prop)
(center_circle : point → circle → Prop)
(line_line_inter : line → line → Prop)
(line_circle_inter : line → circle → Prop)
(circle_circle_inter : circle → circle → Prop)
(dist : point → point → real)
(angle : point → point → point → real)
(rightangle : real)
(area : point → point → point → real)

(more_pts : ∀ (S : set point), S.finite → ∃ (a : point), a ∉ S)
--(P2 : ∀ (L :  line), ∃ (a : point), online a L) -- NEVER USED
(pt_B_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b a c) -- old (P3)
(pt_extension_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b c a)
  -- (P4) not strictly necessary but doesn't cost moves
--(P5 : ∀ (L : line), ∀ (b : point), ¬online b L → ∃ (a : point), a ≠ b ∧ sameside a b L)
  -- (P5) NEVER USED
(opp_side_of_not_online : ∀ {L : line}, ∀ {b : point}, ¬online b L →
  ∃ (a : point), ¬online a L ∧ ¬sameside a b L)
--(P7 : ∀ (α : circle), ∃ (a : point), oncircle a α) -- NEVER USED!!
--(P8 : ∀ (α : circle), ∃ (a : point), inside_circle a α) -- NEVER USED!!
--(P9 : ∀ (α : circle), ∃ (a : point), ¬inside_circle a α ∧ ¬oncircle a α) -- NEVER USED!!

(line_of_ne : ∀ {a b : point}, a ≠ b → ∃ (L :line), online a L ∧ online b L) -- old (LB_of_line_circle_inter)
(circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle), center_circle a α ∧ oncircle b α)
  -- old (Lcircle_convex)

(pt_of_line_line_inter : ∀ {L M : line}, line_line_inter L M →
  ∃ (a : point), online a L ∧ online a M)
--(pt_of_line_circle_inter : ∀ {L : line}, ∀ {α : circle}, line_circle_inter L α →
--  ∃ (a : point), online a L ∧ oncircle a α)
   --pts_of_line_circle_inter Should be proven?
(pts_of_line_circle_inter : ∀ {L : line}, ∀ {α : circle}, line_circle_inter L α →
  ∃ (a b : point), online a L ∧ online b L ∧ oncircle a α ∧ oncircle b α ∧ a ≠ b)
(pt_oncircle_of_inside_outside : ∀ {b c : point}, ∀ {α : circle},
  inside_circle b α → ¬inside_circle c α → ¬oncircle c α →
  ∃ (a : point), oncircle a α ∧ B b a c)
(pt_oncircle_of_inside_ne : ∀ {b c : point}, ∀ {α : circle}, inside_circle b α → c ≠ b →
  ∃ (a : point), oncircle a α ∧ B a b c)
--pt_oncircle_of_inside_ne can be proven?
--(I6 : ∀ {α β : circle}, circle_circle_inter α β → ∃ (a : point), oncircle a α ∧ oncircle a β)
(pts_of_circle_circle_inter : ∀ {α β : circle}, circle_circle_inter α β →
  ∃ (a b : point), oncircle a α ∧ oncircle a β ∧ oncircle b α ∧ oncircle b β ∧ a ≠ b)
(pt_sameside_of_circle_circle_inter : ∀ {b c d : point}, ∀ {α β : circle}, ∀ {L : line},
  circle_circle_inter α β → center_circle c α → center_circle d β → online c L → online d L →
  ¬online b L → ∃ (a : point), oncircle a α ∧ oncircle a β ∧ sameside a b L)
--(I9 : ∀ {b c d : point}, ∀ {α β : circle}, ∀ {L : line}, circle_circle_inter α β → center_circle c α →
--  center_circle d β → online c L → online d L → ¬online b L →
--  ∃ (a : point), oncircle a α ∧ oncircle a β ∧ ¬sameside a b L ∧ ¬online a L) -- NEVER USED!!

(line_unique_of_pts : ∀ {a b : point}, ∀ {L M : line}, a ≠ b → online a L → online b L →
  online a M → online b M → L = M)
(center_circle_unique : ∀ {a b : point}, ∀ {α : circle}, center_circle a α → center_circle b α →
  a = b)
  --center_circle_unique should be proven?
(inside_circle_of_center : ∀ {a : point}, ∀ {α : circle}, center_circle a α → inside_circle a α)
(not_oncircle_of_inside : ∀ {a : point}, ∀ {α : circle}, inside_circle a α → ¬oncircle a α)

--(B1 : ∀ {a b c : point}, B a b c → B c b a ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬B b a c)
(B_symm : ∀ {a b c : point}, B a b c → B c b a )
(ne_12_of_B : ∀ {a b c : point}, B a b c → a ≠ b )
(ne_13_of_B : ∀ {a b c : point}, B a b c → a ≠ c)
(ne_23_of_B : ∀ {a b c : point}, B a b c → b ≠ c )
(not_B_of_B : ∀ {a b c : point}, B a b c → ¬B b a c)
  -- B1 slightly modified, hope no issue?
(online_3_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online b L → online c L)
(online_2_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online c L → online b L)
  -- online_2_of_B can be proven?
(B124_of_B134_B123 : ∀ {a b c d : point}, B a b c → B a d b → B a d c)
(B124_of_B123_B234 : ∀ {a b c d : point}, B a b c → B b c d → B a b d)
(B_of_three_online_ne : ∀ {a b c : point}, ∀ {L : line}, online a L → online b L → online c L → a ≠ b → a ≠ c → b ≠ c
  → B a b c ∨ B b a c ∨ B a c b)
(not_B324_of_B123_B124 : ∀ {a b c d : point}, B a b c → B a b d → ¬B c b d)

(sameside_rfl_of_not_online : ∀ {a : point}, ∀ {L : line}, ¬online a L → sameside a a L)
(sameside_symm : ∀ {a b : point}, ∀ {L : line}, sameside a b L → sameside b a L)
(not_online_of_sameside : ∀ {a b : point}, ∀ {L : line}, sameside a b L → ¬online a L)
(sameside_trans : ∀ {a b c : point}, ∀ {L : line}, sameside a b L → sameside a c L → sameside b c L)
(sameside_or_of_diffside : ∀ {a b c : point}, ∀ {L : line}, ¬online a L → ¬online b L → ¬online c L →
  ¬sameside a b L → sameside a c L ∨ sameside b c L)

(sameside12_of_B123_sameside13 : ∀ {a b c : point}, ∀ {L : line}, B a b c → sameside a c L → sameside a b L)
(sameside23_of_B123_online1_not_online2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → ¬online b L → sameside b c L)
(not_sameside13_of_B123_online2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online b L → ¬sameside a c L)
(B_of_online_inter : ∀ {a b c : point}, ∀ {L M : line}, L ≠ M → a ≠ c → online a M → online b M → online c M →
  online b L → a ≠ b → c ≠ b → ¬sameside a c L → B a b c)

(not_sameside_of_sameside_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, online a L → online a M → online a N → online b L →
  online c M → online d N → sameside c d L → sameside b c N → ¬sameside b d M)
(sameside_of_sameside_not_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, online a L → online a M → online a N → online b L →
  online c M → online d N → sameside c d L → ¬sameside b d M → ¬online d M → b ≠ a →
  sameside b c N)
--(T3 : ∀ (a b c d e : point), ∀ (L M N : line), online a L → online a M → online a N → online b L →
 -- online c M → online d N → sameside c d L → sameside b c N → sameside d e M → sameside c e N →
  --sameside c e L) -- NEVER USED!!

(B_of_line_circle_inter : ∀ {a b c : point}, ∀ {L : line}, ∀ {α : circle }, online a L → online b L → online c L
  → inside_circle a α → oncircle b α → oncircle c α → b ≠ c → B b a c)
(circle_convex : ∀ (a b c : point), ∀ (α : circle), inside_circle a α ∨ oncircle a α → inside_circle b α ∨ oncircle b α →
  B a c b → inside_circle c α)
--(C3 : ∀ (a b c : point), ∀ (α : circle), inside_circle a α ∨ oncircle a α → ¬inside_circle c α → B a c b →
--  ¬inside_circle b α ∧ ¬oncircle b α) -- NEVER USED!!!
(not_sameside_of_circle_inter : ∀ {a b c d : point}, ∀ {α β : circle}, ∀ {L : line}, α ≠ β → c ≠ d→ circle_circle_inter α β →
  oncircle c α → oncircle c β → oncircle d α → oncircle d β → center_circle a α → center_circle b β → online a L
  → online b L → ¬sameside c d L)

(lines_inter_of_not_sameside : ∀ {a b : point}, ∀ {L M : line}, ¬sameside a b L → online a M → online b M →
  line_line_inter L M)
(line_circle_inter_of_not_sameside : ∀ {a b : point}, ∀ {L : line}, ∀ {α : circle}, inside_circle a α ∨ oncircle a α →
  inside_circle b α ∨ oncircle b α → ¬sameside a b L → line_circle_inter L α)
(line_circle_inter_of_inside_online : ∀ {a : point}, ∀ {L : line}, ∀ {α : circle}, inside_circle a α → online a L → line_circle_inter L α)
--(Int4 : ∀ {a b : point}, ∀ {α β : circle}, oncircle a α → inside_circle b α ∨ oncircle b α → inside_circle a β →
--  ¬inside_circle b β → ¬oncircle b β → circle_circle_inter α β) -- NEVER USED!!
(circles_inter_of_inside_oncircle : ∀ {a b : point}, ∀ {α β : circle}, inside_circle a α → oncircle b α → inside_circle b β → oncircle a β →
  circle_circle_inter α β)
(dist_eq_zero_iff : ∀ {a b : point}, dist a b = 0 ↔ a = b)
(dist_symm : ∀ (a b : point), dist a b = dist b a)
(angle_symm : ∀ {a b c : point}, a ≠ b → a ≠ c → angle a b c = angle c b a) -- *** Discuss further ***
  -- Maybe: angle a b c + angle c b a = 4 * rightangle ???


(angle_nonneg : ∀ (a b c : point), 0 ≤ angle a b c)
(dist_nonneg : ∀ (a b : point), 0 ≤ dist a b)
--(degenerate_area : 0 < rightangle) I believe this can be deduced from angle_nonneg together with angle_zero_iff_online (there exist nonzero angles)
(degenerate_area : ∀ (a b : point), area a a b = 0)
--(M7 : ∀ (a b c : point), 0 ≤ area a b c) -- NEVER USED!
(area_invariant : ∀ (a b c : point), area a b c = area c a b ∧ area a b c = area a c b)
(area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, dist a b = dist a1 b1 → dist b c = dist b1 c1 →
  dist c a = dist c1 a1 → area a b c = area a1 b1 c1)

(dist_sum_of_B : ∀ {a b c : point}, B a b c → dist a b + dist b c = dist a c)
--(Dsameside_symm : ∀ {a b c : point}, ∀ {α β : circle}, center_circle a α → center_circle a β → oncircle b α → oncircle c β
 -- → dist a b = dist a c → α = β) -- NEVER USED!
(oncircle_iff_dist_eq : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → oncircle b α →
  (dist a b = dist a c ↔ oncircle c α))
(incircle_iff_dist_lt : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → oncircle b α →
  (dist a c < dist a b ↔ inside_circle c α))

(angle_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → online a L → online b L →
  (online c L ∧ ¬B b a c ↔ angle b a c = 0))--better reformulation?
(angle_add_iff_sameside : ∀ {a b c d : point}, ∀ {L M : line}, online a L → online b L → online a M
  → online c M →
  a ≠ b → a ≠ c → ¬online d M → ¬online d L → L ≠ M →
  (angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L))
(angle_eq_iff_rightangle : ∀ {a b c d : point}, ∀ {L : line}, online a L → online b L → B a c b → ¬online d L →
  (angle a c d = angle d c b ↔ angle a c d = rightangle))
(angle_extension : ∀ {a b c a1 b1 c1 : point}, ∀ {L M : line}, online a L → online b L → online b1 L →
  online a M → online c M → online c1 M → b ≠ a → b1 ≠ a → c ≠ a → c1 ≠ a → ¬B b a b1 →
  ¬B c a c1 → angle b a c = angle b1 a1 c1)
(unparallel_postulate : ∀ {a b c d : point}, ∀ {L M N : line}, online a L → online b L → online b M → online c M →
  online c N → online d N → b ≠ c → sameside a d M → angle a b c + angle b c d < 2 * rightangle →
  ∃ (e : point), online e L ∧ online e N ∧ sameside e a M)

(area_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, online a L → online b L → a ≠ b →
  (area a b c = 0 ↔ online c L))
(area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L → online b L →
  online c L → ¬online d L → (B a c b ↔ area a c d + area d c b = area a d b))

(SAS_iff_SSS : ∀ {a b c d e f : point}, dist a b = dist d e → dist a c = dist d f →
  (angle b a c = angle e d f ↔ dist b c = dist e f)) --Euclid Prop 4,8

open incidence_geometry

----------------------

noncomputable theory

-- instantiation of axioms in ℝ × ℝ

instance incidence_geometry_ℝ_ℝ : incidence_geometry :=
{ point := ℝ × ℝ, -- p = (x, y)
  line := ℝ × ℝ × ℝ, -- a x + b y = c ↔ (a, b, c)
  circle := (ℝ × ℝ) × (ℝ × ℝ), -- center and point on circle
  online := λ p L, L.1 * p.1 + L.2.1 * p.2 = L.2.2,
  sameside := λ p1 p2 L, L.1 * p1.1 + L.2.1 * p1.2 - L.2.2 ≠ 0 ∧
    L.1 * p2.1 + L.2.1 * p2.2 - L.2.2 ≠ 0 ∧ ∃ (μ : ℝ),
    0 < μ ∧ (L.1 * p1.1 + L.2.1 * p1.2 - L.2.2) = μ * (L.1 * p2.1 + L.2.1 * p2.2 - L.2.2),
  B := λ p1 p2 p3, p1 ≠ p2 ∧ p2 ≠ p3 ∧ ∃ (μ : ℝ), 0 < μ ∧ (p3 - p2) = μ • (p2-p1),
  oncircle := λ p ⟨c, b⟩, -- p is a point, c is the center, b is a point on the circle
   (c.1^2 - b.1^2) + (c.2^2 - b.2^2) = (c.1^2 - p.1^2) + (c.2^2 - p.2^2),
  inside_circle := λ p ⟨c, b⟩, -- p is a point, c is the center, b is a point on the circle
   (c.1^2 - p.1^2) + (c.2^2 - p.2^2) < (c.1^2 - b.1^2) + (c.2^2 - b.2^2),
  center_circle := λ p ⟨c, b⟩, p = c,
  line_line_inter := λ L1 L2,
    ¬∃ (μ : ℝ), L1 = μ • L2 ∧ ¬∃ (μ : ℝ), (L1.1, L1.2.1) = μ • (L2.1, L2.2.1),
  line_circle_inter := sorry,
  circle_circle_inter := sorry,
  dist := sorry,
  angle := sorry,
  rightangle := sorry,
  area := sorry,
  more_pts := sorry,
  pt_B_of_ne := begin
    intros p1 p2 p1_ne_p2,
    use ((1:ℝ) / 2) • (p1+p2),
    split,
    { intro h,
      have hh := congr_arg (λ p : ℝ×ℝ, (2:ℝ) • p) h,
      simp only [one_div, smul_inv_smul₀, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff] at hh,
      rw (two_smul ℝ p1) at hh,
      exact p1_ne_p2 ((add_right_inj p1).mp hh), },
    split,
    { sorry, },
    refine ⟨1, by norm_num, _⟩,
    field_simp,
    simp,
    sorry,
  end,
  pt_extension_of_ne := sorry,
  opp_side_of_not_online := sorry,
  line_of_ne := sorry,
  circle_of_ne := sorry,
  pt_of_line_line_inter := sorry,
  pts_of_line_circle_inter := sorry,
  pt_oncircle_of_inside_outside := sorry,
  pt_oncircle_of_inside_ne := sorry,
  pts_of_circle_circle_inter := sorry,
  pt_sameside_of_circle_circle_inter := sorry,
  line_unique_of_pts := sorry,
  center_circle_unique := sorry,
  inside_circle_of_center := sorry,
  not_oncircle_of_inside := sorry,
  B_symm := sorry,
  ne_12_of_B := sorry,
  ne_13_of_B := sorry,
  ne_23_of_B := sorry,
  not_B_of_B := sorry,
  online_3_of_B := sorry,
  online_2_of_B := sorry,
  B124_of_B134_B123 := sorry,
  B124_of_B123_B234 := sorry,
  B_of_three_online_ne := sorry,
  not_B324_of_B123_B124 := sorry,
  sameside_rfl_of_not_online := sorry,
  sameside_symm := sorry,
  not_online_of_sameside := sorry,
  sameside_trans := sorry,
  sameside_or_of_diffside := sorry,
  sameside12_of_B123_sameside13 := sorry,
  sameside23_of_B123_online1_not_online2 := sorry,
  not_sameside13_of_B123_online2 := sorry,
  B_of_online_inter := sorry,
  not_sameside_of_sameside_sameside := sorry,
  sameside_of_sameside_not_sameside := sorry,
  B_of_line_circle_inter := sorry,
  circle_convex := sorry,
  not_sameside_of_circle_inter := sorry,
  lines_inter_of_not_sameside := sorry,
  line_circle_inter_of_not_sameside := sorry,
  line_circle_inter_of_inside_online := sorry,
  circles_inter_of_inside_oncircle := sorry,
  dist_eq_zero_iff := sorry,
  dist_symm := sorry,
  angle_symm := sorry,
  angle_nonneg := sorry,
  dist_nonneg := sorry,
  degenerate_area := sorry,
  area_invariant := sorry,
  area_eq_of_SSS := sorry,
  dist_sum_of_B := sorry,
  oncircle_iff_dist_eq := sorry,
  incircle_iff_dist_lt := sorry,
  angle_zero_iff_online := sorry,
  angle_add_iff_sameside := sorry,
  angle_eq_iff_rightangle := sorry,
  angle_extension := sorry,
  unparallel_postulate := sorry,
  area_zero_iff_online := sorry,
  area_add_iff_B := sorry,
  SAS_iff_SSS := sorry }
