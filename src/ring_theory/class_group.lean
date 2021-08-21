/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import group_theory.quotient_group
import ring_theory.dedekind_domain

/-!
# The ideal class group

This file defines the ideal class group `class_group R K` of fractional ideals of `R`
inside `A`'s field of fractions `K`.

## Main definitions
 - `to_principal_ideal` sends an invertible `x : K` to an invertible fractional ideal
 - `class_group` is the quotient of invertible fractional ideals modulo `to_principal_ideal.range`
 - `class_group.mk0` sends a nonzero integral ideal in a Dedekind domain to its class

## Main results
 - `class_group.mk0_eq_mk0_iff` shows the equivalence with the "classical" definition,
   where `I ~ J` iff `x I = y J` for `x y ≠ (0 : R)`
-/

section integral_domain

variables {R K L : Type*} [integral_domain R]
variables [field K] [field L] [decidable_eq L]
variables [algebra R K] [is_fraction_ring R K]
variables [algebra K L] [finite_dimensional K L]
variables [algebra R L] [is_scalar_tower R K L]

open_locale non_zero_divisors

open is_localization is_fraction_ring fractional_ideal units

section

variables (R K)

/-- `to_principal_ideal R K x` sends `x ≠ 0 : K` to the fractional `R`-ideal generated by `x` -/
@[irreducible]
def to_principal_ideal : units K →* units (fractional_ideal R⁰ K) :=
{ to_fun := λ x,
  ⟨span_singleton _ x,
   span_singleton _ x⁻¹,
   by simp only [span_singleton_one, units.mul_inv', span_singleton_mul_span_singleton],
   by simp only [span_singleton_one, units.inv_mul', span_singleton_mul_span_singleton]⟩,
  map_mul' := λ x y, ext
    (by simp only [units.coe_mk, units.coe_mul, span_singleton_mul_span_singleton]),
  map_one' := ext (by simp only [span_singleton_one, units.coe_mk, units.coe_one]) }

local attribute [semireducible] to_principal_ideal

variables {R K}

@[simp] lemma coe_to_principal_ideal (x : units K) :
  (to_principal_ideal R K x : fractional_ideal R⁰ K) = span_singleton _ x :=
rfl

@[simp] lemma to_principal_ideal_eq_iff {I : units (fractional_ideal R⁰ K)} {x : units K} :
  to_principal_ideal R K x = I ↔ span_singleton R⁰ (x : K) = I :=
units.ext_iff

end

instance principal_ideals.normal : (to_principal_ideal R K).range.normal :=
subgroup.normal_of_comm _

section

variables (R K)

/-- The ideal class group of `R` in a field of fractions `K`
is the group of invertible fractional ideals modulo the principal ideals. -/
@[derive(comm_group)]
def class_group := quotient_group.quotient (to_principal_ideal R K).range

instance : inhabited (class_group R K) := ⟨1⟩

variables {R}

/-- Send a nonzero integral ideal to an invertible fractional ideal. -/
@[simps]
noncomputable def fractional_ideal.mk0 [is_dedekind_domain R] :
  (ideal R)⁰ →* units (fractional_ideal R⁰ K) :=
{ to_fun := λ I, units.mk0 I ((fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl R⁰)).mpr
    (mem_non_zero_divisors_iff_ne_zero.mp I.2)),
  map_one' := by simp,
  map_mul' := λ x y, by simp }

/-- Send a nonzero ideal to the corresponding class in the class group. -/
@[simps]
noncomputable def class_group.mk0 [is_dedekind_domain R] :
  (ideal R)⁰ →* class_group R K :=
(quotient_group.mk' _).comp (fractional_ideal.mk0 K)

variables {K}

lemma quotient_group.mk'_eq_mk' {G : Type*} [group G] {N : subgroup G} [hN : N.normal] {x y : G} :
  quotient_group.mk' N x = quotient_group.mk' N y ↔ ∃ z ∈ N, x * z = y :=
(@quotient.eq _ (quotient_group.left_rel _) _ _).trans
  ⟨λ (h : x⁻¹ * y ∈ N), ⟨_, h, by rw [← mul_assoc, mul_right_inv, one_mul]⟩,
   λ ⟨z, z_mem, eq_y⟩,
     by { rw ← eq_y, show x⁻¹ * (x * z) ∈ N, rwa [← mul_assoc, mul_left_inv, one_mul] }⟩

lemma class_group.mk0_eq_mk0_iff_exists_fraction_ring [is_dedekind_domain R] {I J : (ideal R)⁰} :
  class_group.mk0 K I = class_group.mk0 K J ↔
    ∃ (x ≠ (0 : K)), span_singleton R⁰ x * I = J :=
begin
  simp only [class_group.mk0, monoid_hom.comp_apply, quotient_group.mk'_eq_mk'],
  split,
  { rintros ⟨_, ⟨x, rfl⟩, hx⟩,
    refine ⟨x, x.ne_zero, _⟩,
    simpa only [mul_comm, coe_mk0, monoid_hom.to_fun_eq_coe, coe_to_principal_ideal, units.coe_mul]
      using congr_arg (coe : _ → fractional_ideal R⁰ K) hx },
  { rintros ⟨x, hx, eq_J⟩,
    refine ⟨_, ⟨units.mk0 x hx, rfl⟩, units.ext _⟩,
    simpa only [fractional_ideal.mk0_apply, units.coe_mk0, mul_comm, coe_to_principal_ideal,
        coe_coe, units.coe_mul] using eq_J }
end

lemma class_group.mk0_eq_mk0_iff [is_dedekind_domain R] {I J : (ideal R)⁰} :
  class_group.mk0 K I = class_group.mk0 K J ↔
    ∃ (x y : R) (hx : x ≠ 0) (hy : y ≠ 0), ideal.span {x} * (I : ideal R) = ideal.span {y} * J :=
begin
  refine class_group.mk0_eq_mk0_iff_exists_fraction_ring.trans ⟨_, _⟩,
  { rintros ⟨z, hz, h⟩,
    obtain ⟨x, ⟨y, hy⟩, rfl⟩ := is_localization.mk'_surjective R⁰ z,
    refine ⟨x, y, _, mem_non_zero_divisors_iff_ne_zero.mp hy, _⟩,
    { rintro hx, apply hz,
      rw [hx, is_fraction_ring.mk'_eq_div, (algebra_map R K).map_zero, zero_div] },
    { exact (fractional_ideal.mk'_mul_coe_ideal_eq_coe_ideal K hy).mp h } },
  { rintros ⟨x, y, hx, hy, h⟩,
    have hy' : y ∈ R⁰ := mem_non_zero_divisors_iff_ne_zero.mpr hy,
    refine ⟨is_localization.mk' K x ⟨y, hy'⟩, _, _⟩,
    { contrapose! hx,
      rwa [is_localization.mk'_eq_iff_eq_mul, zero_mul, ← (algebra_map R K).map_zero,
           (is_fraction_ring.injective R K).eq_iff] at hx },
    { exact (fractional_ideal.mk'_mul_coe_ideal_eq_coe_ideal K hy').mpr h } },
end

lemma class_group.mk0_surjective [is_dedekind_domain R] :
  function.surjective (class_group.mk0 K : (ideal R)⁰ → class_group R K) :=
begin
  rintros ⟨I⟩,
  obtain ⟨a, a_ne_zero', ha⟩ := I.1.2,
  have a_ne_zero := mem_non_zero_divisors_iff_ne_zero.mp a_ne_zero',
  have fa_ne_zero : (algebra_map R K) a ≠ 0 :=
    is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors a_ne_zero',
  refine ⟨⟨{ carrier := { x | (algebra_map R K a)⁻¹ * algebra_map R K x ∈ I.1 }, .. }, _⟩, _⟩,
  { simp only [ring_hom.map_zero, set.mem_set_of_eq, mul_zero, ring_hom.map_mul],
    exact submodule.zero_mem I },
  { simp only [ring_hom.map_add, set.mem_set_of_eq, mul_zero, ring_hom.map_mul, mul_add],
    exact λ _ _ ha hb, submodule.add_mem I ha hb },
  { intros c _ hb,
    simp only [smul_eq_mul, set.mem_set_of_eq, mul_zero, ring_hom.map_mul, mul_add,
               mul_left_comm ((algebra_map R K) a)⁻¹],
    rw ← algebra.smul_def c,
    exact submodule.smul_mem I c hb },
  { rw [mem_non_zero_divisors_iff_ne_zero, submodule.zero_eq_bot, submodule.ne_bot_iff],
    obtain ⟨x, x_ne, x_mem⟩ := exists_ne_zero_mem_is_integer I.ne_zero,
    refine ⟨a * x, _, mul_ne_zero a_ne_zero x_ne⟩,
    change ((algebra_map R K) a)⁻¹ * (algebra_map R K) (a * x) ∈ I.1,
    rwa [ring_hom.map_mul, ← mul_assoc, inv_mul_cancel fa_ne_zero, one_mul] },
  { symmetry,
    apply quotient.sound,
    refine ⟨units.mk0 (algebra_map R K a) fa_ne_zero, _⟩,
    apply @mul_left_cancel _ _ I,
    rw [← mul_assoc, mul_right_inv, one_mul, eq_comm, mul_comm I],
    apply units.ext,
    simp only [monoid_hom.coe_mk, subtype.coe_mk, ring_hom.map_mul, coe_coe,
               units.coe_mul, coe_to_principal_ideal, coe_mk0,
               fractional_ideal.eq_span_singleton_mul],
    split,
    { intros zJ' hzJ',
      obtain ⟨zJ, hzJ : (algebra_map R K a)⁻¹ * algebra_map R K zJ ∈ ↑I, rfl⟩ :=
        (mem_coe_ideal R⁰).mp hzJ',
      refine ⟨_, hzJ, _⟩,
      rw [← mul_assoc, mul_inv_cancel fa_ne_zero, one_mul] },
    { intros zI' hzI',
      obtain ⟨y, hy⟩ := ha zI' hzI',
      rw [← algebra.smul_def, fractional_ideal.mk0_apply, coe_mk0, coe_coe, mem_coe_ideal],
      refine ⟨y, _, hy⟩,
      show (algebra_map R K a)⁻¹ * algebra_map R K y ∈ (I : fractional_ideal R⁰ K),
      rwa [hy, algebra.smul_def, ← mul_assoc, inv_mul_cancel fa_ne_zero, one_mul] } }
end

end

lemma class_group.mk_eq_one_iff
  {I : units (fractional_ideal R⁰ K)} :
  quotient_group.mk' (to_principal_ideal R K).range I = 1 ↔
    (I : submodule R K).is_principal :=
begin
  rw [← (quotient_group.mk' _).map_one, eq_comm, quotient_group.mk'_eq_mk'],
  simp only [exists_prop, one_mul, exists_eq_right, to_principal_ideal_eq_iff,
             monoid_hom.mem_range, coe_coe],
  refine ⟨λ ⟨x, hx⟩, ⟨⟨x, by rw [← hx, coe_span_singleton]⟩⟩, _⟩,
  unfreezingI { intros hI },
  obtain ⟨x, hx⟩ := @submodule.is_principal.principal _ _ _ _ _ _ hI,
  have hx' : (I : fractional_ideal R⁰ K) = span_singleton R⁰ x,
  { apply subtype.coe_injective, rw [hx, coe_span_singleton] },
  refine ⟨units.mk0 x _, _⟩,
  { intro x_eq, apply units.ne_zero I, simp [hx', x_eq] },
  simp [hx']
end

lemma class_group.mk0_eq_one_iff [is_dedekind_domain R]
  {I : ideal R} (hI : I ∈ (ideal R)⁰) :
  class_group.mk0 K ⟨I, hI⟩ = 1 ↔ I.is_principal :=
class_group.mk_eq_one_iff.trans (coe_submodule_is_principal R K)

/-- The class group of principal ideal domain is finite (in fact a singleton).
TODO: generalize to Dedekind domains -/
instance [is_principal_ideal_ring R] :
  fintype (class_group R K) :=
{ elems := {1},
  complete :=
  begin
    rintros ⟨I⟩,
    rw [finset.mem_singleton],
    exact class_group.mk_eq_one_iff.mpr (I : fractional_ideal R⁰ K).is_principal
  end }

/-- The class number of a principal ideal domain is `1`. -/
lemma card_class_group_eq_one [is_principal_ideal_ring R] :
  fintype.card (class_group R K) = 1 :=
begin
  rw fintype.card_eq_one_iff,
  use 1,
  rintros ⟨I⟩,
  exact class_group.mk_eq_one_iff.mpr (I : fractional_ideal R⁰ K).is_principal
end

/-- The class number is `1` iff the ring of integers is a principal ideal domain. -/
lemma card_class_group_eq_one_iff [is_dedekind_domain R] [fintype (class_group R K)] :
  fintype.card (class_group R K) = 1 ↔ is_principal_ideal_ring R :=
begin
  split, swap, { introsI, convert card_class_group_eq_one, assumption },
  rw fintype.card_eq_one_iff,
  rintros ⟨I, hI⟩,
  have eq_one : ∀ J : class_group R K, J = 1 := λ J, trans (hI J) (hI 1).symm,
  refine ⟨λ I, _⟩,
  by_cases hI : I = ⊥,
  { rw hI, exact bot_is_principal },
  exact (class_group.mk0_eq_one_iff (mem_non_zero_divisors_iff_ne_zero.mpr hI)).mp (eq_one _),
end

end integral_domain