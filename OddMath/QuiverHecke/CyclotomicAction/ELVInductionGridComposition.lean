import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp

/-! # Composition of coend comparisons across a six-category grid

The two-letter comparison in DeformedActionAssembly §§5–6 must agree
with the selected single-letter comparisons and the canonical induction
flattenings. The coefficient calculation retains the intermediate object
transports, before the generic coend calculation is specialized to the
changing fixed-content scalar quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

section Squares
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} D₀] [Category.{u} D₁] [Category.{u} D₂]
  (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂)
  (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
  (T : D₀ ⥤ D₁) (S : D₁ ⥤ D₂)
  (hJ : J ⋙ Q₁ = Q₀ ⋙ T) (hK : K ⋙ Q₂ = Q₁ ⋙ S)

include hJ hK in
/-- The composite of the two commuting append squares. -/
theorem coendGrid_comp_eq : (J ⋙ K) ⋙ Q₂ = Q₀ ⋙ (T ⋙ S) := by
  calc
    (J ⋙ K) ⋙ Q₂ = J ⋙ (K ⋙ Q₂) := rfl
    _ = J ⋙ (Q₁ ⋙ S) := congrArg (fun F => J ⋙ F) hK
    _ = (J ⋙ Q₁) ⋙ S := rfl
    _ = (Q₀ ⋙ T) ⋙ S := congrArg (fun F => F ⋙ S) hJ
    _ = Q₀ ⋙ (T ⋙ S) := rfl

/-- The composite object equality has the same endpoint map as the two
single-letter equalities in their prescribed order. -/
theorem coendGrid_comp_endpoint (v : C₀) :
    eqToHom (congrArg (fun F : C₀ ⥤ D₂ => F.obj v)
      (coendGrid_comp_eq J K Q₀ Q₁ Q₂ T S hJ hK)).symm =
    S.map (eqToHom (congrArg (fun F : C₀ ⥤ D₁ => F.obj v) hJ).symm) ≫
      eqToHom (congrArg (fun F : C₁ ⥤ D₂ => F.obj (J.obj v)) hK).symm := by
  rw [eqToHom_map, eqToHom_trans]

end Squares

section Coefficients
variable {k : Type u} [CommRing k]
  {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} D₀] [Category.{u} D₁] [Category.{u} D₂]
  [Preadditive C₁] [Linear k C₁] [Preadditive C₂] [Linear k C₂]
  [Preadditive D₁] [Linear k D₁] [Preadditive D₂] [Linear k D₂]
  (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂) (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) [Q₁.Additive] [Q₁.Linear k]
  (Q₂ : C₂ ⥤ D₂) [Q₂.Additive] [Q₂.Linear k]
  (T : D₀ ⥤ D₁) (S : D₁ ⥤ D₂) (hJ : J ⋙ Q₁ = Q₀ ⋙ T) (hK : K ⋙ Q₂ = Q₁ ⋙ S)

/-- Applying the two quotient coefficient maps then flattening is the
coefficient map for the composite square. No coefficient order is changed. -/
theorem coendGrid_comp_coefficient (s : C₀) (v : C₁) (w : C₂)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) :
    S.map (coendSquareCoefficient (k := k) J Q₁ Q₀ T hJ s v a) ≫
        coendSquareCoefficient (k := k) K Q₂ Q₁ S hK v w g =
      coendSquareCoefficient (k := k) (J ⋙ K) Q₂ Q₀ (T ⋙ S)
        (coendGrid_comp_eq J K Q₀ Q₁ Q₂ T S hJ hK) s w (K.map a ≫ g) := by
  have hn := (eqToHom hK.symm : Q₁ ⋙ S ⟶ K ⋙ Q₂).naturality a
  simp only [eqToHom_app, Functor.comp_map] at hn
  change S.map (eqToHom _ ≫ Q₁.map a) ≫ (eqToHom _ ≫ Q₂.map g) =
    eqToHom _ ≫ Q₂.map (K.map a ≫ g)
  rw [S.map_comp, Q₂.map_comp, coendGrid_comp_endpoint J K Q₀ Q₁ Q₂ T S hJ hK s]
  simpa only [Category.assoc] using congrArg
    (fun z => S.map (eqToHom (congrArg (fun F : C₀ ⥤ D₁ => F.obj s) hJ).symm) ≫ z ≫ Q₂.map g) hn

end Coefficients

section Nested
variable {k : Type u} [CommRing k]
  {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} D₀] [Category.{u} D₁] [Category.{u} D₂]
  [Preadditive C₀] [Linear k C₀]
  [Preadditive C₁] [Linear k C₁] [Preadditive C₂] [Linear k C₂]
  [Supercategory k C₀] [Supercategory k C₁] [Supercategory k C₂]
  [Preadditive D₀] [Linear k D₀]
  [Preadditive D₁] [Linear k D₁] [Preadditive D₂] [Linear k D₂]
  [Supercategory k D₀] [Supercategory k D₁] [Supercategory k D₂]
  (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (Q₀ : C₀ ⥤ D₀) [Q₀.Additive] [Q₀.Linear k] [IsSuperfunctor k Q₀]
  (Q₁ : C₁ ⥤ D₁) [Q₁.Additive] [Q₁.Linear k]
  (Q₂ : C₂ ⥤ D₂) [Q₂.Additive] [Q₂.Linear k]
  (T : D₀ ⥤ D₁) (S : D₁ ⥤ D₂) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  [S.Additive] [S.Linear k] [IsSuperfunctor k S]
  (hJ : J ⋙ Q₁ = Q₀ ⋙ T) (hK : K ⋙ Q₂ = Q₁ ⋙ S)
  (M : Superfunctor k D₀ (SVec k))
private abbrev coendPullback : Superfunctor k C₀ (SVec k) := ⟨Q₀ ⋙ M.toFunctor⟩
local notation "RM" => coendPullback (k := k) Q₀ M

/-- On nested generators the composite raw square map agrees with the
canonical flattening of the two quotient tensors, without a premise about
an inner comparison map. This identifies the two-letter fixed-content
comparison once its literal composite generator formula is supplied. -/
theorem coendGridMap_comp_tensor (s : C₀) (v : C₁) (w : C₂)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj (Q₀.obj s)) :
    coendSquareMap (J ⋙ K) Q₂ Q₀ (T ⋙ S) (coendGrid_comp_eq J K Q₀ Q₁ Q₂ T S hJ hK)
      M.toFunctor w (((inductionComp J K).hom.app RM).total w
        (tensor K (induced J RM).toFunctor v g (tensor J (RM).toFunctor s a b))) =
    ((inductionComp T S).hom.app M).total (Q₂.obj w)
      (tensor S (induced T M).toFunctor (Q₁.obj v)
        (coendSquareCoefficient (k := k) K Q₂ Q₁ S hK v w g)
        (tensor T M.toFunctor (Q₀.obj s)
          (coendSquareCoefficient (k := k) J Q₁ Q₀ T hJ s v a) b)) := by
  have hOld := inductionComp_hom_total_tensor J K RM s v w g a b
  have hRaw := coendSquareMap_tensor (J ⋙ K) Q₂ Q₀ (T ⋙ S)
    (coendGrid_comp_eq J K Q₀ Q₁ Q₂ T S hJ hK) M.toFunctor w s (K.map a ≫ g) b
  have hNew := inductionComp_hom_total_tensor T S M (Q₀.obj s) (Q₁.obj v) (Q₂.obj w)
    (coendSquareCoefficient (k := k) K Q₂ Q₁ S hK v w g)
    (coendSquareCoefficient (k := k) J Q₁ Q₀ T hJ s v a) b
  have hCoeff := coendGrid_comp_coefficient (k := k) J K Q₀ Q₁ Q₂ T S hJ hK s v w a g
  exact (congrArg (coendSquareMap (J ⋙ K) Q₂ Q₀ (T ⋙ S)
    (coendGrid_comp_eq J K Q₀ Q₁ Q₂ T S hJ hK) M.toFunctor w) hOld).trans
      (hRaw.trans ((congrArg (fun z => tensor (T ⋙ S) M.toFunctor (Q₀.obj s) z b)
        hCoeff.symm).trans hNew.symm))

end Nested
end OddMath.QuiverHecke.ELVOld.BalancedInduction
