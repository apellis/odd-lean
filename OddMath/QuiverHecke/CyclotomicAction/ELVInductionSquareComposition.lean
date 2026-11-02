import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp

/-! # Composition of coend square comparisons

The two-letter comparison in DeformedActionAssembly §§5–6 must agree
with the selected single-letter comparisons and the canonical induction
flattenings. The coefficient calculation retains the intermediate object
transports, before the generic coend calculation is specialized to the
weighted quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

section Squares
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  (J K : C ⥤ C) (Q : C ⥤ D) (T S : D ⥤ D)
  (hJ : J ⋙ Q = Q ⋙ T) (hK : K ⋙ Q = Q ⋙ S)

include hJ hK in
/-- The composite of the two commuting append squares. -/
theorem coendSquare_comp_eq : (J ⋙ K) ⋙ Q = Q ⋙ (T ⋙ S) := by
  calc
    (J ⋙ K) ⋙ Q = J ⋙ (K ⋙ Q) := rfl
    _ = J ⋙ (Q ⋙ S) := congrArg (fun F => J ⋙ F) hK
    _ = (J ⋙ Q) ⋙ S := rfl
    _ = (Q ⋙ T) ⋙ S := congrArg (fun F => F ⋙ S) hJ
    _ = Q ⋙ (T ⋙ S) := rfl

/-- The composite object equality has the same endpoint map as the two
single-letter equalities in their prescribed order. -/
theorem coendSquare_comp_endpoint (v : C) :
    eqToHom (congrArg (fun F : C ⥤ D => F.obj v)
      (coendSquare_comp_eq J K Q T S hJ hK)).symm =
    S.map (eqToHom (congrArg (fun F : C ⥤ D => F.obj v) hJ).symm) ≫
      eqToHom (congrArg (fun F : C ⥤ D => F.obj (J.obj v)) hK).symm := by
  rw [eqToHom_map, eqToHom_trans]

end Squares

section Coefficients
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Preadditive D] [Linear k D]
  (J K : C ⥤ C) (Q : C ⥤ D) [Q.Additive] [Q.Linear k]
  (T S : D ⥤ D) (hJ : J ⋙ Q = Q ⋙ T) (hK : K ⋙ Q = Q ⋙ S)

/-- Applying the two quotient coefficient maps then flattening is the
coefficient map for the composite square. No coefficient order is changed. -/
theorem coendSquare_comp_coefficient (s v w : C)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) :
    S.map (coendSquareCoefficient (k := k) J Q Q T hJ s v a) ≫
        coendSquareCoefficient (k := k) K Q Q S hK v w g =
      coendSquareCoefficient (k := k) (J ⋙ K) Q Q (T ⋙ S)
        (coendSquare_comp_eq J K Q T S hJ hK) s w (K.map a ≫ g) := by
  have hn := (eqToHom hK.symm : Q ⋙ S ⟶ K ⋙ Q).naturality a
  simp only [eqToHom_app, Functor.comp_map] at hn
  change S.map (eqToHom _ ≫ Q.map a) ≫ (eqToHom _ ≫ Q.map g) =
    eqToHom _ ≫ Q.map (K.map a ≫ g)
  rw [S.map_comp, Q.map_comp, coendSquare_comp_endpoint J K Q T S hJ hK s]
  simpa only [Category.assoc] using congrArg
    (fun z => S.map (eqToHom (congrArg (fun F : C ⥤ D => F.obj s) hJ).symm) ≫ z ≫ Q.map g) hn

end Coefficients

section Nested
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J K : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T S : D ⥤ D) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  [S.Additive] [S.Linear k] [IsSuperfunctor k S]
  (hJ : J ⋙ Q = Q ⋙ T) (hK : K ⋙ Q = Q ⋙ S)
  (M : Superfunctor k D (SVec k))
private abbrev coendPullback : Superfunctor k C (SVec k) := ⟨Q ⋙ M.toFunctor⟩
local notation "RM" => coendPullback (k := k) Q M

/-- On nested generators the composite raw square map agrees with the
canonical flattening of the two quotient tensors, without a premise about
an inner comparison map. This identifies the two-letter weighted
comparison once its literal composite generator formula is supplied. -/
theorem coendSquareMap_comp_tensor (s v w : C)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj (Q.obj s)) :
    coendSquareMap (J ⋙ K) Q Q (T ⋙ S) (coendSquare_comp_eq J K Q T S hJ hK)
      M.toFunctor w (((inductionComp J K).hom.app RM).total w
        (tensor K (induced J RM).toFunctor v g (tensor J (RM).toFunctor s a b))) =
    ((inductionComp T S).hom.app M).total (Q.obj w)
      (tensor S (induced T M).toFunctor (Q.obj v)
        (coendSquareCoefficient (k := k) K Q Q S hK v w g)
        (tensor T M.toFunctor (Q.obj s)
          (coendSquareCoefficient (k := k) J Q Q T hJ s v a) b)) := by
  have hOld := inductionComp_hom_total_tensor J K RM s v w g a b
  have hRaw := coendSquareMap_tensor (J ⋙ K) Q Q (T ⋙ S)
    (coendSquare_comp_eq J K Q T S hJ hK) M.toFunctor w s (K.map a ≫ g) b
  have hNew := inductionComp_hom_total_tensor T S M (Q.obj s) (Q.obj v) (Q.obj w)
    (coendSquareCoefficient (k := k) K Q Q S hK v w g)
    (coendSquareCoefficient (k := k) J Q Q T hJ s v a) b
  have hCoeff := coendSquare_comp_coefficient (k := k) J K Q T S hJ hK s v w a g
  exact (congrArg (coendSquareMap (J ⋙ K) Q Q (T ⋙ S)
    (coendSquare_comp_eq J K Q T S hJ hK) M.toFunctor w) hOld).trans
      (hRaw.trans ((congrArg (fun z => tensor (T ⋙ S) M.toFunctor (Q.obj s) z b)
        hCoeff.symm).trans hNew.symm))

end Nested
end OddMath.QuiverHecke.ELVOld.BalancedInduction
