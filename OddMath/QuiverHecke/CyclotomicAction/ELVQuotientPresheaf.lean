/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModule
import OddMath.QuiverHecke.CyclotomicAction.ELVCokernel

/-! # Enlarged cyclotomic quotient presheaves

The enlarged-word cyclotomic quotient in the ELV cokernel construction carries
precomposition by every old quotient arrow. Its moving dot/square action is
natural, and the canonical map from the append quotient respects both actions.
All words, including the empty old word, and arbitrary cutoffs are retained.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Old precomposition on the enlarged cyclotomic quotient, descended in both arguments. -/
def quotientPull (i : I) (u v w : List I) :
    Old D Sc cutoff u v →ₗ[k]
      Old D Sc cutoff (v ++ [i]) w →ₗ[k] Old D Sc cutoff (u ++ [i]) w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun c =>
        (ideal D Sc cutoff (u ++ [i]) w).mkQ.comp
          (Linear.leftComp k _ (rightContext D Sc cutoff [i] u v c))
       map_add' := by intros; ext h; simp [map_add, Preadditive.add_comp]
       map_smul' := by intros; ext h; simp [map_smul, Linear.smul_comp] } :
       hom D Sc cutoff u v →ₗ[k]
         hom D Sc cutoff (v ++ [i]) w →ₗ[k] Old D Sc cutoff (u ++ [i]) w)
    (by
      intro c hc
      ext h
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (ideal_comp D Sc cutoff (ideal_rightContext D Sc cutoff [i] hc) h))
    (by
      intro h hh
      ext c
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (comp_ideal D Sc cutoff (rightContext D Sc cutoff [i] u v c) hh))

@[simp] theorem quotientPull_mk (i : I) {u v w : List I}
    (c : hom D Sc cutoff u v) (h : hom D Sc cutoff (v ++ [i]) w) :
    quotientPull D Sc cutoff i u v w ((ideal D Sc cutoff u v).mkQ c)
      ((ideal D Sc cutoff (v ++ [i]) w).mkQ h) =
    (ideal D Sc cutoff (u ++ [i]) w).mkQ
      (rightContext D Sc cutoff [i] u v c ≫ h) := rfl

private theorem quotientContext_id (i : I) (v : List I) :
    rightContext D Sc cutoff [i] v v (𝟙 _) = 𝟙 _ := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    (𝟙 ((pres D Sc).obj (ob D v)) ▷ (pres D Sc).obj (ob D [i])) = _
  exact congrArg (fun f => (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)
    (MonoidalSupercategory.id_whiskerRight (R := k)
      ((pres D Sc).obj (ob D v)) ((pres D Sc).obj (ob D [i])))

theorem quotientPull_comp (i : I) {a b c w : List I}
    (f : Old D Sc cutoff a b) (g : Old D Sc cutoff b c)
    (z : Old D Sc cutoff (c ++ [i]) w) :
    quotientPull D Sc cutoff i a c w (oldComp D Sc cutoff a b c f g) z =
      quotientPull D Sc cutoff i a b w f (quotientPull D Sc cutoff i b c w g z) := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff a b).mkQ_surjective f
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff b c).mkQ_surjective g
  obtain ⟨h, rfl⟩ := (ideal D Sc cutoff (c ++ [i]) w).mkQ_surjective z
  change (ideal D Sc cutoff (a ++ [i]) w).mkQ
    (rightContext D Sc cutoff [i] a c (f ≫ g) ≫ h) =
    (ideal D Sc cutoff (a ++ [i]) w).mkQ
      (rightContext D Sc cutoff [i] a b f ≫ (rightContext D Sc cutoff [i] b c g ≫ h))
  rw [rightContext_comp, Category.assoc]

/-- The enlarged cyclotomic quotient as a presheaf of all old source words. -/
def quotientPresheaf (i : I) (w : List I) :
    (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (Old D Sc cutoff (v.unop.word ++ [i]) w)
  map f := ModuleCat.ofHom (quotientPull D Sc cutoff i _ _ w f.unop)
  map_id v := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨h, rfl⟩ := (ideal D Sc cutoff (v.unop.word ++ [i]) w).mkQ_surjective z
    change (ideal D Sc cutoff _ w).mkQ (rightContext D Sc cutoff [i] _ _ (𝟙 _) ≫ h) = _
    rw [quotientContext_id, Category.id_comp]
    rfl
  map_comp {a b c} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact quotientPull_comp D Sc cutoff i g.unop f.unop z

instance quotientPresheaf_additive (i : I) (w : List I) :
    (quotientPresheaf D Sc cutoff i w).Additive where
  map_add := by
    intro a b f g
    apply ModuleCat.hom_ext
    exact (quotientPull D Sc cutoff i _ _ w).map_add f.unop g.unop

/-- Moving dot at even colour and moving square at odd colour on the full quotient. -/
def quotientCentral (i : I) (v w : List I) :
    Old D Sc cutoff (v ++ [i]) w →ₗ[k] Old D Sc cutoff (v ++ [i]) w :=
  (ideal D Sc cutoff (v ++ [i]) w).mapQ (ideal D Sc cutoff (v ++ [i]) w)
    (Linear.leftComp k _ (appendMovingPower D Sc cutoff i v (centralDegree D i)))
    (by intro h hh; exact comp_ideal D Sc cutoff _ hh)

@[simp] theorem quotientCentral_mk (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    quotientCentral D Sc cutoff i v w ((ideal D Sc cutoff (v ++ [i]) w).mkQ h) =
      (ideal D Sc cutoff (v ++ [i]) w).mkQ
        (appendMovingPower D Sc cutoff i v (centralDegree D i) ≫ h) := rfl

theorem quotientPull_central (i : I) {u v w : List I}
    (c : Old D Sc cutoff u v) (z : Old D Sc cutoff (v ++ [i]) w) :
    quotientCentral D Sc cutoff i u w (quotientPull D Sc cutoff i u v w c z) =
      quotientPull D Sc cutoff i u v w c (quotientCentral D Sc cutoff i v w z) := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff u v).mkQ_surjective c
  obtain ⟨h, rfl⟩ := (ideal D Sc cutoff (v ++ [i]) w).mkQ_surjective z
  simp only [quotientPull_mk, quotientCentral_mk]
  rw [← Category.assoc,
    appendMovingPower_rightContext_cross D Sc cutoff i _ (centralDegree_even D i), Category.assoc]

/-- The moving central action is natural in every old word-to-word arrow. -/
def quotientCentralNat (i : I) (w : List I) :
    quotientPresheaf D Sc cutoff i w ⟶ quotientPresheaf D Sc cutoff i w where
  app v := ModuleCat.ofHom (quotientCentral D Sc cutoff i v.unop.word w)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact quotientPull_central D Sc cutoff i f.unop z

theorem canonicalAppendTarget_pull (i : I) {u v w : List I}
    (c : Old D Sc cutoff u v) (z : AppendTarget D Sc cutoff i v w) :
    canonicalAppendTarget D Sc cutoff i u w (appendPull D Sc cutoff i u v w c z) =
      quotientPull D Sc cutoff i u v w c (canonicalAppendTarget D Sc cutoff i v w z) := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff u v).mkQ_surjective c
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  rfl

/-- The canonical enlarged quotient is natural for all old arrows. -/
def canonicalAppendNat (i : I) (w : List I) :
    appendPresheaf D Sc cutoff i w ⟶ quotientPresheaf D Sc cutoff i w where
  app v := ModuleCat.ofHom (canonicalAppendTarget D Sc cutoff i v.unop.word w)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact canonicalAppendTarget_pull D Sc cutoff i f.unop z

theorem canonicalAppendTarget_central (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w) :
    canonicalAppendTarget D Sc cutoff i v w (centralAppend D Sc cutoff i v w z) =
      quotientCentral D Sc cutoff i v w (canonicalAppendTarget D Sc cutoff i v w z) := by
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  rfl

end OddMath.QuiverHecke.ELVOld
