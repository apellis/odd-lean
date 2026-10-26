/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRestriction

/-!
# Induction on the cyclotomic weight spaces

Ports `globalE` of `Categorification/KLR/CyclotomicAction/Global.lean`. The
even file sums induction over the blocks `β` of weight `x` with
`{i} + β = δ`; there is at most one such block (`blockSucc_injective`). Here
the component at `δ` is `globalContentInduction` of the component at that
block when it exists, and the zero supermodule (the empty biproduct)
otherwise. Every component is a superfunctor, so the weight-space functor
keeps odd module morphisms. The adjunction with `globalF` on weight spaces
needs the vacuum unit and counit, which are not constructed here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-- The zero supermodule over the algebra of height `n`. -/
def zeroSupermodule (n : ℕ) : HeightModules D Sc a ha n where
  toSVec := { carrier := PUnit.{u + 1}, odd := 0, odd_comp_odd := LinearMap.ext fun _ => rfl }
  lact := 0
  ract := 0
  lact_one := SVec.hom_ext fun _ => rfl
  lact_mul _ _ := SVec.hom_ext fun _ => rfl
  ract_one := SVec.hom_ext fun _ => rfl
  ract_mul _ _ := SVec.hom_ext fun _ => rfl
  lact_ract _ _ := SVec.hom_ext fun _ => rfl
  lact_mem _ _ _ := by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
  ract_mem _ _ _ := by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

/-- The zero supermodule satisfies the content condition of every content of its height. -/
theorem zeroSupermodule_supported (n : ℕ) (δ : Multiset I) (hδ : δ.card = n) :
    heightContentSupported D Sc a ha n δ (zeroSupermodule D Sc a ha n) := by
  cases n with
  | zero => exact Multiset.card_eq_zero.mp hδ
  | succ n => intro _; rfl

/-- The zero object of a global content supercategory. -/
def globalZero (δ : Multiset I) : GlobalContentModules D Sc a ha δ :=
  ⟨zeroSupermodule D Sc a ha δ.card, zeroSupermodule_supported D Sc a ha δ.card δ rfl⟩

theorem globalZero_isZero (δ : Multiset I) : Limits.IsZero (globalZero D Sc a ha δ) :=
  (Limits.IsZero.iff_id_eq_zero _).mpr
    (InducedCategory.hom_ext (SuperBimodule.hom_ext (SVec.hom_ext fun _ => rfl)))

section ZeroFunctor
variable {C : Type*} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  (δ : Multiset I)

/-- The constant functor at the zero supermodule. -/
def zeroFunctor : C ⥤ GlobalContentModules D Sc a ha δ :=
  (Functor.const C).obj (globalZero D Sc a ha δ)

instance : (zeroFunctor D Sc a ha (C := C) δ).Additive where
  map_add := (globalZero_isZero D Sc a ha δ).eq_of_src _ _

instance : (zeroFunctor D Sc a ha (C := C) δ).Linear k where
  map_smul _ _ := (globalZero_isZero D Sc a ha δ).eq_of_src _ _

instance : IsSuperfunctor k (zeroFunctor D Sc a ha (C := C) δ) where
  map_mem {_ _ _ f} _ := by
    rw [(globalZero_isZero D Sc a ha δ).eq_of_src ((zeroFunctor D Sc a ha δ).map f) 0]
    exact Submodule.zero_mem _

end ZeroFunctor

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The product of the content supercategories of weight `x`. -/
abbrev WeightProduct (x : X) :=
  ∀ β : WeightBlocks D Λ x, GlobalContentModules D Sc a ha β.1

/-- Evaluation at one content block, as a superfunctor. -/
def blockEval (β : WeightBlocks D Λ x) :
    Superfunctor k (WeightProduct D Sc a ha Λ x) (GlobalContentModules D Sc a ha β.1) :=
  ⟨Pi.eval (fun β : WeightBlocks D Λ x => GlobalContentModules D Sc a ha β.1) β⟩

open scoped Classical in
/-- The component of induction at a block `δ` of weight `y`: induction from its unique
predecessor block when it exists, and zero otherwise. -/
def inductionComponent (δ : WeightBlocks D Λ y) :
    Superfunctor k (WeightProduct D Sc a ha Λ x) (GlobalContentModules D Sc a ha δ.1) :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    (blockEval D Sc a ha Λ hδ.choose).comp
      (globalContentInduction D Sc i a ha (blockSucc_eq D Λ i hδ.choose_spec))
  else ⟨zeroFunctor D Sc a ha δ.1⟩

private theorem inductionComponent_choice (β c : WeightBlocks D Λ x)
    (hc : blockSucc D Λ i h c = blockSucc D Λ i h β) :
    (blockEval D Sc a ha Λ c).comp (globalContentInduction D Sc i a ha (blockSucc_eq D Λ i hc)) =
      (blockEval D Sc a ha Λ β).comp
        (globalContentInduction D Sc i a ha (blockSucc_val D Λ i h β).symm) := by
  obtain rfl := blockSucc_injective D Λ i h hc
  rfl

/-- At a successor block the component is induction from the predecessor. -/
theorem inductionComponent_blockSucc (β : WeightBlocks D Λ x) :
    inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β) =
      (blockEval D Sc a ha Λ β).comp
        (globalContentInduction D Sc i a ha (blockSucc_val D Λ i h β).symm) := by
  have hδ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β := ⟨β, rfl⟩
  unfold inductionComponent
  split
  · rename_i hc
    exact inductionComponent_choice D Sc a ha i Λ h β _ hc.choose_spec
  · exact absurd hδ ‹_›

/-- Without a predecessor block the component is zero. -/
theorem inductionComponent_isZero (δ : WeightBlocks D Λ y)
    (hδ : ¬ ∃ β, blockSucc D Λ i h β = δ) (M : WeightProduct D Sc a ha Λ x) :
    Limits.IsZero ((inductionComponent D Sc a ha i Λ h δ).obj M) := by
  unfold inductionComponent
  split
  · exact absurd ‹_› hδ
  · exact globalZero_isZero D Sc a ha δ.1

/-- The underlying functor of induction on weight spaces. -/
def globalEFunctor : WeightProduct D Sc a ha Λ x ⥤ WeightProduct D Sc a ha Λ y :=
  Functor.pi' fun δ => (inductionComponent D Sc a ha i Λ h δ).toFunctor

instance : (globalEFunctor D Sc a ha i Λ h).Additive where
  map_add := funext fun δ => (inductionComponent D Sc a ha i Λ h δ).toFunctor.map_add

instance : (globalEFunctor D Sc a ha i Λ h).Linear k where
  map_smul f r := funext fun δ => (inductionComponent D Sc a ha i Λ h δ).toFunctor.map_smul r f

instance : IsSuperfunctor k (globalEFunctor D Sc a ha i Λ h) where
  map_mem hf δ := IsSuperfunctor.map_mem (F := (inductionComponent D Sc a ha i Λ h δ).toFunctor) hf

/-- **Induction on weight spaces** `x ⟶ y` for `x + α_i = y`. -/
def globalE : globalWeightSpace D Sc a ha Λ x ⟶ globalWeightSpace D Sc a ha Λ y :=
  ⟨globalEFunctor D Sc a ha i Λ h⟩

@[simp] theorem globalE_obj (M : WeightProduct D Sc a ha Λ x) (δ : WeightBlocks D Λ y) :
    (globalE D Sc a ha i Λ h).obj M δ = (inductionComponent D Sc a ha i Λ h δ).obj M := rfl

end Weight

end OddMath.QuiverHecke.CyclotomicAction
