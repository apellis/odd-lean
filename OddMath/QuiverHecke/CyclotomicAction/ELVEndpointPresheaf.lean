/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategory

/-! # Ordinary endpoint actions of the old ELV category

The two old-only quotients are additive presheaves on the old cyclotomic
category. The prepend action retains an arbitrary total-parity twist, while
the append action is unchanged. All old word-to-word arrows act, not only
endomorphisms of a fixed word.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem insert_comp_relations (i : I) {u v w : List I}
    (c : hom D Sc cutoff u v) {h : hom D Sc cutoff (i :: v) w}
    (hh : h ∈ relations D Sc cutoff i v w) :
    insert D Sc cutoff i u v c ≫ h ∈ relations D Sc cutoff i u w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, ← insert_comp]
    exact Submodule.subset_span ⟨t, c ≫ r, comp_ideal D Sc cutoff c hr, f, rfl⟩
  | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul a b _ hb => rw [Linear.comp_smul]; exact Submodule.smul_mem _ a hb

/-- Twisted old precomposition, descended in both arguments. -/
def sourcePull (p : ZMod 2) (i : I) (u v w : List I) :
    Old D Sc cutoff u v →ₗ[k]
      Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i u w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun c =>
        (projection D Sc cutoff i u w).comp
          (Linear.leftComp k _ (insert D Sc cutoff i u v (twist k p c)))
       map_add' := by intros; ext h; simp [map_add, Preadditive.add_comp]
       map_smul' := by intros; ext h; simp [map_smul, Linear.smul_comp] } :
       hom D Sc cutoff u v →ₗ[k]
         hom D Sc cutoff (i :: v) w →ₗ[k] Target D Sc cutoff i u w)
    (by
      intro c hc
      ext h
      exact projection_old_ideal D Sc cutoff i (twist_ideal D Sc cutoff p hc) h)
    (by
      intro h hh
      ext c
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (insert_comp_relations D Sc cutoff i (twist k p c) hh))

@[simp] theorem sourcePull_mk (p : ZMod 2) (i : I) {u v w : List I}
    (c : hom D Sc cutoff u v) (h : hom D Sc cutoff (i :: v) w) :
    sourcePull D Sc cutoff p i u v w ((ideal D Sc cutoff u v).mkQ c)
      (projection D Sc cutoff i v w h) =
    projection D Sc cutoff i u w (insert D Sc cutoff i u v (twist k p c) ≫ h) := rfl

theorem sourcePull_comp (p : ZMod 2) (i : I) {a b c w : List I}
    (f : Old D Sc cutoff a b) (g : Old D Sc cutoff b c)
    (z : Target D Sc cutoff i c w) :
    sourcePull D Sc cutoff p i a c w (oldComp D Sc cutoff a b c f g) z =
      sourcePull D Sc cutoff p i a b w f (sourcePull D Sc cutoff p i b c w g z) := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff a b).mkQ_surjective f
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff b c).mkQ_surjective g
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i c w z
  change projection D Sc cutoff i a w (insert D Sc cutoff i a c (twist k p (f ≫ g)) ≫ h) =
    projection D Sc cutoff i a w (insert D Sc cutoff i a b (twist k p f) ≫ (insert D Sc cutoff i b c (twist k p g) ≫ h))
  rw [twist_comp, insert_comp, Category.assoc]

/-- The source quotient with its twisted ordinary old action. -/
def sourcePresheaf (p : ZMod 2) (i : I) (w : List I) :
    (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (Target D Sc cutoff i v.unop.word w)
  map f := ModuleCat.ofHom (sourcePull D Sc cutoff p i _ _ w f.unop)
  map_id v := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v.unop.word w z
    change projection D Sc cutoff i _ w (insert D Sc cutoff i _ _ (twist k p (𝟙 _)) ≫ h) = _
    simp
  map_comp {a b c} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact sourcePull_comp D Sc cutoff p i g.unop f.unop z

instance sourcePresheaf_additive (p : ZMod 2) (i : I) (w : List I) :
    (sourcePresheaf D Sc cutoff p i w).Additive where
  map_add := by
    intro a b f g
    apply ModuleCat.hom_ext
    exact (sourcePull D Sc cutoff p i _ _ w).map_add f.unop g.unop

/-- Untwisted append precomposition, descended in both arguments. -/
def appendPull (i : I) (u v w : List I) :
    Old D Sc cutoff u v →ₗ[k]
      AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i u w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun c =>
        (appendProjection D Sc cutoff i u w).comp
          (Linear.leftComp k _ (rightContext D Sc cutoff [i] u v c))
       map_add' := by intros; ext h; simp [map_add, Preadditive.add_comp]
       map_smul' := by intros; ext h; simp [map_smul, Linear.smul_comp] } :
       hom D Sc cutoff u v →ₗ[k]
         hom D Sc cutoff (v ++ [i]) w →ₗ[k] AppendTarget D Sc cutoff i u w)
    (by
      intro c hc
      ext h
      exact appendProjection_old_ideal D Sc cutoff i hc h)
    (by
      intro h hh
      ext c
      exact (Submodule.Quotient.mk_eq_zero _).mpr (comp_appendRelations D Sc cutoff i c hh))

@[simp] theorem appendPull_mk (i : I) {u v w : List I}
    (c : hom D Sc cutoff u v) (h : hom D Sc cutoff (v ++ [i]) w) :
    appendPull D Sc cutoff i u v w ((ideal D Sc cutoff u v).mkQ c)
      (appendProjection D Sc cutoff i v w h) =
    appendProjection D Sc cutoff i u w (rightContext D Sc cutoff [i] u v c ≫ h) := rfl

private theorem appendContext_id (i : I) (v : List I) :
    rightContext D Sc cutoff [i] v v (𝟙 _) = 𝟙 _ := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    (𝟙 ((pres D Sc).obj (ob D v)) ▷ (pres D Sc).obj (ob D [i])) = _
  exact congrArg (fun f => (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)
    (MonoidalSupercategory.id_whiskerRight (R := k)
      ((pres D Sc).obj (ob D v)) ((pres D Sc).obj (ob D [i])))

theorem appendPull_comp (i : I) {a b c w : List I}
    (f : Old D Sc cutoff a b) (g : Old D Sc cutoff b c)
    (z : AppendTarget D Sc cutoff i c w) :
    appendPull D Sc cutoff i a c w (oldComp D Sc cutoff a b c f g) z =
      appendPull D Sc cutoff i a b w f (appendPull D Sc cutoff i b c w g z) := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff a b).mkQ_surjective f
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff b c).mkQ_surjective g
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i c w z
  change appendProjection D Sc cutoff i a w (rightContext D Sc cutoff [i] a c (f ≫ g) ≫ h) =
    appendProjection D Sc cutoff i a w (rightContext D Sc cutoff [i] a b f ≫ (rightContext D Sc cutoff [i] b c g ≫ h))
  rw [rightContext_comp, Category.assoc]

/-- The append quotient with its unchanged ordinary old action. -/
def appendPresheaf (i : I) (w : List I) :
    (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (AppendTarget D Sc cutoff i v.unop.word w)
  map f := ModuleCat.ofHom (appendPull D Sc cutoff i _ _ w f.unop)
  map_id v := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v.unop.word w z
    change appendProjection D Sc cutoff i _ w (rightContext D Sc cutoff [i] _ _ (𝟙 _) ≫ h) = _
    rw [appendContext_id, Category.id_comp]
    rfl
  map_comp {a b c} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact appendPull_comp D Sc cutoff i g.unop f.unop z

instance appendPresheaf_additive (i : I) (w : List I) :
    (appendPresheaf D Sc cutoff i w).Additive where
  map_add := by
    intro a b f g
    apply ModuleCat.hom_ext
    exact (appendPull D Sc cutoff i _ _ w).map_add f.unop g.unop

end OddMath.QuiverHecke.ELVOld
