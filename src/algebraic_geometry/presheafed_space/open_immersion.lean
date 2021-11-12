/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.presheafed_space.has_colimits
import category_theory.limits.shapes.binary_products
import algebraic_geometry.stalks
import algebraic_geometry.sheafed_space
import topology.sheaves.functors
import category_theory.limits.preserves.shapes.pullbacks

/-!
# Open immersions of presheafed spaces

We say that a morphism of presheaved spaces `f : X ⟶ Y` is an open immersions if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

## Main definitions

* `algebraic_geometry.PresheafedSpace.is_open_immersion`: the `Prop`-valued typeclass asserting
  that `f` is an open_immersion
* `algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left`: An explicit limit
  cocone of the pullback of `f, g` if `f` is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.lift`: If `f : X ⟶ U ⊆ Z` is an
  open immersion, then for each `Y ⟶ Z` whose image falls in `U`, we may lift it into a unique
  `Y ⟶ X` that commutes with them.

## Main results

* `algebraic_geometry.PresheafedSpace.is_open_immersion.comp`: The composition of two open
  immersions is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso`: An iso is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso`: An epic open immersion is iso.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso`: An epic open immersion is iso.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left`: If `f` is an
  open immersion, then the pullback of `f, g` exists. There is also `has_pullback_of_right`.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left`: Open immersions
  are stable under pullback. There is also `pullback_fst_of_right`.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_one_is_open_immersion`:
  The pullback of two open immersions is an open immersion.


We also proves that the pullback of two presheaved spaces exists, and is also an open immersion.
-/

open topological_space category_theory opposite
open category_theory.limits algebraic_geometry
namespace algebraic_geometry.PresheafedSpace

universes v u

variables {C : Type u} [category.{v} C]

/--
An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class is_open_immersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop :=
(base_open : open_embedding f.base)
(c_iso : ∀ U : opens X, is_iso (f.c.app (op (base_open.is_open_map.functor.obj U))))

attribute [instance] is_open_immersion.c_iso

namespace is_open_immersion

section

variables {X Y : PresheafedSpace C} {f : X ⟶ Y} (H : is_open_immersion f)

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbreviation open_functor := H.base_open.is_open_map.functor

local attribute [-simp] eq_to_hom_map eq_to_iso_map

/-- An open immersion `f : X ⟶ Y` induces an isomorphsm `X ≅ Y|_{f(X)}`. -/
@[simps] noncomputable
def iso_restrict : X ≅ Y.restrict H.base_open :=
PresheafedSpace.iso_of_components (iso.refl _)
begin
  symmetry,
  fapply nat_iso.of_components,
  intro U,
  refine as_iso (f.c.app (op (H.open_functor.obj (unop U)))) ≪≫ X.presheaf.map_iso (eq_to_iso _),
  { induction U using opposite.rec,
    cases U,
    dsimp only [is_open_map.functor, functor.op, opens.map],
    congr' 2,
    erw set.preimage_image_eq _ H.base_open.inj,
    refl },
  { intros U V i,
    simp only [category_theory.eq_to_iso.hom, Top.presheaf.pushforward_obj_map, category.assoc,
      functor.op_map, iso.trans_hom, as_iso_hom, functor.map_iso_hom, ←X.presheaf.map_comp],
    erw [f.c.naturality_assoc, ←X.presheaf.map_comp],
    congr }
end

@[simp] lemma iso_restrict_hom_of_restrict : H.iso_restrict.hom ≫ Y.of_restrict _ = f :=
begin
  ext,
  { simp only [comp_c_app, iso_restrict_hom_c_app, nat_trans.comp_app,
      eq_to_hom_refl, of_restrict_c_app, category.assoc, whisker_right_id'],
    erw [category.comp_id, f.c.naturality_assoc, ←X.presheaf.map_comp],
    transitivity f.c.app x ≫ X.presheaf.map (𝟙 _),
    { congr },
    { erw [X.presheaf.map_id, category.comp_id] } },
  { simp }
end

@[simp] lemma iso_restrict_inv_of_restrict : H.iso_restrict.inv ≫ f = Y.of_restrict _ :=
by { rw iso.inv_comp_eq, simp }

instance mono [H : is_open_immersion f] : mono f :=
by { rw ← H.iso_restrict_hom_of_restrict, apply mono_comp }

/-- The composition of two open immersions is an open immersion. -/
instance comp {Z : PresheafedSpace C} (f : X ⟶ Y) [hf : is_open_immersion f] (g : Y ⟶ Z)
  [hg : is_open_immersion g] :
  is_open_immersion (f ≫ g) :=
{ base_open := hg.base_open.comp hf.base_open,
  c_iso := λ U,
  begin
    generalize_proofs h,
    dsimp only [algebraic_geometry.PresheafedSpace.comp_c_app, unop_op, functor.op, comp_base,
      Top.presheaf.pushforward_obj_obj, opens.map_comp_obj],
    apply_with is_iso.comp_is_iso { instances := ff },
    swap,
    { have : (opens.map g.base).obj (h.functor.obj U) = hf.open_functor.obj U,
      { dsimp only [opens.map, is_open_map.functor, PresheafedSpace.comp_base],
        congr' 1,
        rw [coe_comp, ←set.image_image, set.preimage_image_eq _ hg.base_open.inj] },
      rw this,
      apply_instance },
    { have : h.functor.obj U = hg.open_functor.obj (hf.open_functor.obj U),
      { dsimp only [is_open_map.functor],
        congr' 1,
        rw [comp_base, coe_comp, ←set.image_image],
        congr },
      rw this,
      apply_instance }
  end
}

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable
def inv_app (U : opens X) : X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (H.open_functor.obj U)) :=
X.presheaf.map (eq_to_hom (by simp [opens.map, set.preimage_image_eq _ H.base_open.inj])) ≫
  inv (f.c.app (op (H.open_functor.obj U)))

@[simp, reassoc] lemma inv_naturality {U V : (opens X)ᵒᵖ} (i : U ⟶ V) :
  X.presheaf.map i ≫ H.inv_app (unop V) = H.inv_app (unop U) ≫
    Y.presheaf.map (H.open_functor.op.map i) :=
begin
  simp only [inv_app, ←category.assoc],
  rw [is_iso.comp_inv_eq],
  simp only [category.assoc, f.c.naturality, is_iso.inv_hom_id_assoc, ← X.presheaf.map_comp],
  erw ← X.presheaf.map_comp,
  congr
end

instance (U : opens X) : is_iso (H.inv_app U) := by { delta inv_app, apply_instance }

lemma inv_inv_app (U : opens X) :
  inv (H.inv_app U) = f.c.app (op (H.open_functor.obj U)) ≫
    X.presheaf.map (eq_to_hom (by simp [opens.map, set.preimage_image_eq _ H.base_open.inj])) :=
begin
  rw ← cancel_epi (H.inv_app U),
  rw is_iso.hom_inv_id,
  delta inv_app,
  simp [← functor.map_comp]
end

@[simp, reassoc] lemma inv_app_app (U : opens X) :
  H.inv_app U ≫ f.c.app (op (H.open_functor.obj U)) =
    X.presheaf.map (eq_to_hom (by simp [opens.map, set.preimage_image_eq _ H.base_open.inj])) :=
by rw [inv_app, category.assoc, is_iso.inv_hom_id, category.comp_id]

@[simp, reassoc] lemma app_inv_app (U : opens Y) :
  f.c.app (op U) ≫ H.inv_app ((opens.map f.base).obj U) =
  Y.presheaf.map ((hom_of_le (by exact set.image_preimage_subset f.base U)).op :
    op U ⟶ op (H.open_functor.obj ((opens.map f.base).obj U))) :=
by { erw ← category.assoc, rw [is_iso.comp_inv_eq, f.c.naturality], congr }

end

section

variables {X Y : PresheafedSpace C} {f : X ⟶ Y} (H : is_open_immersion f)

/-- An isomorphism is an open immersion. -/
instance of_iso {X Y : PresheafedSpace C} (H : X ≅ Y) : is_open_immersion H.hom :=
{ base_open := (Top.homeo_of_iso ((forget C).map_iso H)).open_embedding,
  c_iso := λ _, infer_instance }

@[priority 100]
instance of_is_iso {X Y : PresheafedSpace C} (f : X ⟶ Y) [is_iso f] : is_open_immersion f :=
algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso (as_iso f)

instance of_restrict {X : Top} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
  (hf : open_embedding f) : is_open_immersion (Y.of_restrict hf) :=
{ base_open := hf,
  c_iso := λ U,
  begin
    dsimp,
    have : (opens.map f).obj (hf.is_open_map.functor.obj U) = U,
    { cases U,
      dsimp only [opens.map, is_open_map.functor],
      congr' 1,
      rw set.preimage_image_eq _ hf.inj,
      refl },
    convert (show is_iso (Y.presheaf.map (𝟙 _)), from infer_instance),
    { apply subsingleton.helim,
      rw this },
    { rw Y.presheaf.map_id,
      apply_instance }
  end }

/-- This could be used in conjunction with `category_theory.nat_iso.is_iso_of_is_iso_app`. -/
lemma is_iso_of_components (f : X ⟶ Y) [is_iso f.base] [is_iso f.c] : is_iso f :=
begin
  convert is_iso.of_iso (iso_of_components (as_iso f.base) (as_iso f.c).symm),
  ext, { simpa }, { simp },
end

lemma to_iso (f : X ⟶ Y) [h : is_open_immersion f] [h' : epi f.base] : is_iso f :=
begin
  apply_with is_iso_of_components { instances := ff },
  { let : X ≃ₜ Y := (homeomorph.of_embedding _ h.base_open.to_embedding).trans
    { to_fun := subtype.val, inv_fun := λ x, ⟨x,
      by { rw set.range_iff_surjective.mpr ((Top.epi_iff_surjective _).mp h'), trivial }⟩,
      left_inv := λ ⟨_,_⟩, rfl, right_inv := λ _, rfl },
    convert is_iso.of_iso (Top.iso_of_homeo this),
    { ext, refl } },
  { apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
    intro U,
    have : U = op (h.open_functor.obj ((opens.map f.base).obj (unop U))),
    { induction U using opposite.rec,
      cases U,
      dsimp only [functor.op, opens.map],
      congr,
      exact (set.image_preimage_eq _ ((Top.epi_iff_surjective _).mp h')).symm },
    convert @@is_open_immersion.c_iso _ h ((opens.map f.base).obj (unop U)) }
end

instance stalk_iso [has_colimits C] [H : is_open_immersion f] (x : X) : is_iso (stalk_map f x) :=
begin
  rw ← H.iso_restrict_hom_of_restrict,
  rw PresheafedSpace.stalk_map.comp,
  apply_instance
end

end

section pullback
noncomputable theory

open is_open_immersion

variables {X Y Z : PresheafedSpace C} (f : X ⟶ Z) [hf : is_open_immersion f] (g : Y ⟶ Z)

include hf

/--
  (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
def pullback_cone_of_left_fst :
  Y.restrict (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base) ⟶ X :=
{ base := pullback.fst,
  c :=
  { app := λ U, hf.inv_app (unop U) ≫
      g.c.app (op (hf.base_open.is_open_map.functor.obj (unop U))) ≫
      Y.presheaf.map (eq_to_hom
      (begin
        simp only [is_open_map.functor, subtype.mk_eq_mk, unop_op, op_inj_iff, opens.map,
        subtype.coe_mk, functor.op_obj, subtype.val_eq_coe],
        apply has_le.le.antisymm,
          { rintros _ ⟨_, h₁, h₂⟩,
            use (Top.pullback_iso_prod_subtype _ _).inv ⟨⟨_, _⟩, h₂⟩,
            simpa using h₁ },
          { rintros _ ⟨x, h₁, rfl⟩,
            exact ⟨_, h₁, concrete_category.congr_hom pullback.condition x⟩ }
      end)),
    naturality' :=
    begin
      intros U V i,
      induction U using opposite.rec,
      induction V using opposite.rec,
      simp only [quiver.hom.unop_op, Top.presheaf.pushforward_obj_map, category.assoc,
        nat_trans.naturality_assoc, functor.op_map, inv_naturality_assoc, ← Y.presheaf.map_comp],
      erw ← Y.presheaf.map_comp,
      congr
    end } }

/--
We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullback_cone_of_left : pullback_cone f g :=
begin
  fapply pullback_cone.mk,
  { exact Y.restrict (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base) },
  exact pullback_cone_of_left_fst f g,
  { exact Y.of_restrict _ },
  { ext U,
    { induction U using opposite.rec,
      dsimp only [comp_c_app, nat_trans.comp_app, unop_op,
        whisker_right_app, pullback_cone_of_left_fst],
      simp only [quiver.hom.unop_op, Top.presheaf.pushforward_obj_map, app_inv_app_assoc,
        eq_to_hom_app, eq_to_hom_unop, category.assoc, nat_trans.naturality_assoc, functor.op_map],
      erw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp],
      congr },
    { simpa using pullback.condition } }
end

variable (s : pullback_cone f g)

/--
  (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
def pullback_cone_of_left_lift : s.X ⟶ (pullback_cone_of_left f g).X :=
{ base := pullback.lift s.fst.base s.snd.base
  (congr_arg (λ x, PresheafedSpace.hom.base x) s.condition),
  c :=
  { app := λ U, s.snd.c.app _ ≫ s.X.presheaf.map (eq_to_hom (begin
      dsimp only [opens.map, is_open_map.functor, functor.op],
      congr' 2,
      let s' : pullback_cone f.base g.base := pullback_cone.mk s.fst.base s.snd.base _,
      have : _ = s.snd.base := limit.lift_π s' walking_cospan.right,
      conv_lhs { erw ← this, rw coe_comp, erw ← set.preimage_preimage },
      erw set.preimage_image_eq _
        (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base).inj,
      simp,
    end)),
    naturality' := λ U V i,
    begin
      erw s.snd.c.naturality_assoc,
      rw category.assoc,
      erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp],
      congr
    end } }

section end

lemma pullback_cone_of_left_lift_fst :
  pullback_cone_of_left_lift f g s ≫
    (pullback_cone_of_left f g).fst = s.fst :=
begin
  ext x,
  { induction x using opposite.rec,
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _,
    simp_rw [category.assoc],
    erw ← s.X.presheaf.map_comp,
    erw s.snd.c.naturality_assoc,
    have := congr_app s.condition (op (hf.open_functor.obj x)),
    dsimp only [comp_c_app, unop_op] at this,
    rw ← is_iso.comp_inv_eq at this,
    reassoc! this,
    erw [← this, hf.inv_app_app_assoc, s.fst.c.naturality_assoc],
    simpa },
  { change pullback.lift _ _ _ ≫ pullback.fst = _,
    simp }
end

section end

lemma pullback_cone_of_left_lift_snd :
  pullback_cone_of_left_lift f g s ≫
    (pullback_cone_of_left f g).snd = s.snd :=
begin
  ext x,
  { change (_ ≫ _ ≫ _) ≫ _ = _,
    simp_rw category.assoc,
    erw s.snd.c.naturality_assoc,
    erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp],
    transitivity s.snd.c.app x ≫ s.X.presheaf.map (𝟙 _),
    { congr },
    { rw s.X.presheaf.map_id, erw category.comp_id } },
  { change pullback.lift _ _ _ ≫ pullback.snd = _,
    simp }
end

instance pullback_cone_snd_is_open_immersion :
  is_open_immersion (pullback_cone_of_left f g).snd :=
begin
  erw category_theory.limits.pullback_cone.mk_snd,
  apply_instance
end

/-- The constructed pullback cone is indeed the pullback. -/
def pullback_cone_of_left_is_limit :
  is_limit (pullback_cone_of_left f g) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  split,
  swap,
  exact pullback_cone_of_left_lift f g s,
  split,
  apply pullback_cone_of_left_lift_fst,
  split,
  apply pullback_cone_of_left_lift_snd,
  intros m h₁ h₂,
  rw ← cancel_mono (pullback_cone_of_left f g).snd,
  exact (h₂.trans (pullback_cone_of_left_lift_snd f g s).symm)
end

instance has_pullback_of_left :
  has_pullback f g :=
⟨⟨⟨_, pullback_cone_of_left_is_limit f g⟩⟩⟩

instance has_pullback_of_right :
  has_pullback g f := has_pullback_symmetry f g

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left :
  is_open_immersion (pullback.snd : pullback f g ⟶ _) :=
begin
  delta pullback.snd,
  rw ← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right,
  apply_instance
end

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right :
  is_open_immersion (pullback.fst : pullback g f ⟶ _) :=
begin
  rw ← pullback_symmetry_hom_comp_snd,
  apply_instance
end

instance pullback_one_is_open_immersion [is_open_immersion g] :
  is_open_immersion (limit.π (cospan f g) walking_cospan.one) :=
begin
  rw [←limit.w (cospan f g) walking_cospan.hom.inl, cospan_map_inl],
  apply_instance
end

instance forget_preserves_limits_of_left : preserves_limit (cospan f g) (forget C) :=
preserves_limit_of_preserves_limit_cone (pullback_cone_of_left_is_limit f g)
begin
  apply (is_limit.postcompose_hom_equiv (diagram_iso_cospan _) _).to_fun,
  refine (is_limit.equiv_iso_limit _).to_fun (limit.is_limit (cospan f.base g.base)),
  fapply cones.ext,
  exact (iso.refl _),
  change ∀ j, _ = 𝟙 _ ≫ _ ≫ _,
  simp_rw category.id_comp,
  rintros (_|_|_); symmetry,
  { erw category.comp_id,
    exact limit.w (cospan f.base g.base) walking_cospan.hom.inl },
  { exact category.comp_id _ },
  { exact category.comp_id _ },
end

instance forget_preserves_limits_of_right : preserves_limit (cospan g f) (forget C) :=
preserves_pullback_symmetry (forget C) f g

lemma pullback_snd_is_iso_of_range_subset (H : set.range g.base ⊆ set.range f.base) :
  is_iso (pullback.snd : pullback f g ⟶ _) :=
begin
  haveI := Top.snd_iso_of_left_embedding_range_subset hf.base_open.to_embedding g.base H,
  haveI : is_iso (pullback.snd : pullback f g ⟶ _).base,
  { delta pullback.snd,
    rw ← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right,
    change is_iso (_ ≫ pullback.snd),
    apply_instance },
  apply to_iso
end

/--
The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H : set.range g.base ⊆ set.range f.base) : Y ⟶ X :=
begin
  haveI := pullback_snd_is_iso_of_range_subset f g H,
  exact inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst,
end

@[simp, reassoc] lemma lift_fac (H : set.range g.base ⊆ set.range f.base) :
  lift f g H ≫ f = g :=
by { erw category.assoc, rw is_iso.inv_comp_eq, exact pullback.condition }

lemma lift_uniq (H : set.range g.base ⊆ set.range f.base) (l : Y ⟶ X)
  (hl : l ≫ f = g) : l = lift f g H :=
by rw [← cancel_mono f, hl, lift_fac]

end pullback

open category_theory.limits.walking_cospan

section SheafedSpace

variables [has_products C]

section to_SheafedSpace

variables {X : PresheafedSpace C} (Y : SheafedSpace C)

variables (f : X ⟶ Y.to_PresheafedSpace) [H : is_open_immersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def to_SheafedSpace : SheafedSpace C :=
{ is_sheaf :=
  begin
    apply Top.presheaf.is_sheaf_of_iso (sheaf_iso_of_iso H.iso_restrict.symm).symm,
    apply Top.sheaf.pushforward_sheaf_of_sheaf,
    exact (Y.restrict H.base_open).is_sheaf
  end,
to_PresheafedSpace := X }

@[simp] lemma to_SheafedSpace_forget_eq : (to_SheafedSpace Y f).to_PresheafedSpace = X := rfl

/--
If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, we can
upgrade it into a morphism of SheafedSpaces.
-/
def to_SheafedSpace_hom : to_SheafedSpace Y f ⟶ Y := ⟨f.base, f.c⟩

instance to_SheafedSpace_hom_forget_is_open_immersion :
  is_open_immersion (to_SheafedSpace_hom Y f) := ⟨H.base_open, H.c_iso⟩

@[simp] lemma to_SheafedSpace_hom_base_eq : (to_SheafedSpace_hom Y f).base = f.base := rfl

@[simp] lemma to_SheafedSpace_hom_c_eq : (to_SheafedSpace_hom Y f).c = f.c := rfl

omit H

@[simp] lemma to_SheafedSpace_hom_eq {X Y : SheafedSpace C} (f : X ⟶ Y) [is_open_immersion f] :
  to_SheafedSpace Y f = X := by unfreezingI { cases X, refl }

end to_SheafedSpace

section pullback

variables {X Y Z : SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z) [H : is_open_immersion f]

include H

local notation `forget` := SheafedSpace.forget_to_PresheafedSpace
local notation `forget_map` := SheafedSpace.forget_to_PresheafedSpace.map
open category_theory.limits.walking_cospan

instance forget_map_is_open_immersion :
  is_open_immersion (forget_map f) := ⟨H.base_open, H.c_iso⟩

instance has_limit_cospan_forget_of_left : has_limit (cospan f g ⋙ forget) :=
begin
  apply has_limit_of_iso (diagram_iso_cospan _).symm,
  change has_limit (cospan (forget_map f) (forget_map g)),
  apply_instance
end

instance has_limit_cospan_forget_of_left' : has_limit (cospan ((cospan f g ⋙ forget).map hom.inl)
  ((cospan f g ⋙ forget).map hom.inr)) :=
show has_limit (cospan (forget_map f) (forget_map g)), from infer_instance

instance has_limit_cospan_forget_of_right : has_limit (cospan g f ⋙ forget) :=
begin
  apply has_limit_of_iso (diagram_iso_cospan _).symm,
  change has_limit (cospan (forget_map g) (forget_map f)),
  apply_instance
end

instance has_limit_cospan_forget_of_right' : has_limit (cospan ((cospan g f ⋙ forget).map hom.inl)
  ((cospan g f ⋙ forget).map hom.inr)) :=
show has_limit (cospan (forget_map g) (forget_map f)), from infer_instance


instance forget_creates_pullback_of_left : creates_limit (cospan f g) forget :=
creates_limit_of_fully_faithful_of_iso
  (to_SheafedSpace Y (@pullback.snd (PresheafedSpace C) _ _ _ _ f g _))
  (eq_to_iso (show pullback _ _ = pullback _ _, by congr)
    ≪≫ has_limit.iso_of_nat_iso (diagram_iso_cospan _).symm)

instance forget_creates_pullback_of_right : creates_limit (cospan g f) forget :=
creates_limit_of_fully_faithful_of_iso
  (to_SheafedSpace Y (@pullback.fst (PresheafedSpace C) _ _ _ _ g f _))
  (eq_to_iso (show pullback _ _ = pullback _ _, by congr)
    ≪≫ has_limit.iso_of_nat_iso (diagram_iso_cospan _).symm)

instance SheafedSpace_forget_preserves_of_left :
  preserves_limit (cospan f g) (SheafedSpace.forget C) :=
@@limits.comp_preserves_limit _ _ _ _ forget (PresheafedSpace.forget C) _
begin
  apply_with (preserves_limit_of_iso_diagram _ (diagram_iso_cospan _).symm) { instances := tt },
  dsimp,
  apply_instance
end

instance SheafedSpace_forget_preserves_of_right :
  preserves_limit (cospan g f) (SheafedSpace.forget C) :=
preserves_pullback_symmetry _ _ _

instance SheafedSpace_has_pullback_of_left : has_pullback f g :=
  has_limit_of_created (cospan f g) forget

instance SheafedSpace_has_pullback_of_right : has_pullback g f :=
  has_limit_of_created (cospan g f) forget

/-- Open immersions are stable under base-change. -/
instance SheafedSpace_pullback_snd_of_left :
  is_open_immersion (pullback.snd : pullback f g ⟶ _) :=
begin
  delta pullback.snd,
  have : _ = limit.π (cospan f g) right := preserves_limits_iso_hom_π
      forget (cospan f g) right,
  rw ← this,
  have := has_limit.iso_of_nat_iso_hom_π
    (diagram_iso_cospan (cospan f g ⋙ forget))
    right,
  erw category.comp_id at this,
  rw ← this,
  dsimp,
  apply_instance
end

instance SheafedSpace_pullback_fst_of_right :
  is_open_immersion (pullback.fst : pullback g f ⟶ _) :=
begin
  delta pullback.fst,
  have : _ = limit.π (cospan g f) left := preserves_limits_iso_hom_π
      forget (cospan g f) left,
  rw ← this,
  have := has_limit.iso_of_nat_iso_hom_π
    (diagram_iso_cospan (cospan g f ⋙ forget)) left,
  erw category.comp_id at this,
  rw ← this,
  dsimp,
  apply_instance
end

instance SheafedSpace_pullback_one_is_open_immersion [is_open_immersion g] :
  is_open_immersion (limit.π (cospan f g) one : pullback f g ⟶ Z) :=
begin
  rw [←limit.w (cospan f g) hom.inl, cospan_map_inl],
  apply_instance
end

end pullback

end SheafedSpace

end is_open_immersion

end algebraic_geometry.PresheafedSpace