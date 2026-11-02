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

section Pair
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (K : C ⥤ C) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (S : D ⥤ D) (hK : K ⋙ Q = Q ⋙ S)
  (L : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (f : L ⟶ (restriction Q).obj N)

/-- Apply the inner even component, then the outer canonical square map.
The inner modules remain abstract while the literal coend types are fixed. -/
def coendSquarePairLinear (w : C) : Obj K L.toFunctor w →ₗ[k] Obj S N.toFunctor (Q.obj w) :=
  coendSquareMap K Q Q S hK N.toFunctor w ∘ₗ mapComponent K f 0 w

/-- The two-letter map keeps the literal coefficient arrow and applies
only the given inner even component to its vector. -/
theorem coendSquarePairLinear_tensor (v w : C) (g : K.obj v ⟶ w) (b : L.obj v) :
    coendSquarePairLinear K Q S hK L N f w (tensor K L.toFunctor v g b) =
    tensor S N.toFunctor (Q.obj v)
      (coendSquareCoefficient (k := k) K Q Q S hK v w g) (f.app 0 v b) := by
  have hm := mapComponent_tensor K f 0 w v g b
  change coendSquareMap K Q Q S hK N.toFunctor w
    (mapComponent K f 0 w (tensor K L.toFunctor v g b)) = _
  rw [hm, twist_zero]
  exact coendSquareMap_tensor K Q Q S hK N.toFunctor w v g (f.app 0 v b)

end Pair

section Inner
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : D ⥤ D) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (M : Superfunctor k D (SVec k))
private abbrev coendPullback : Superfunctor k C (SVec k) := ⟨Q ⋙ M.toFunctor⟩

/-- Expose the inner comparison as a map of literal coends before
specializing the two-letter construction. -/
def coendSquareInnerLinear
    (f : induced J (coendPullback Q M) ⟶ (restriction Q).obj (induced T M)) (v : C) :
    Obj J (Q ⋙ M.toFunctor) v →ₗ[k] Obj T M.toFunctor (Q.obj v) := f.app 0 v

end Inner

section Flatten
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
local notation "RM" => coendPullback Q M
variable (fJ : induced J RM ⟶ (restriction Q).obj (induced T M))
local notation "P" => coendSquarePairLinear K Q S hK (induced J RM) (induced T M) fJ

private def coendInsert (F : C ⥤ SVec k) (w v : C) (g : K.obj v ⟶ w) :
    F.obj v →ₗ[k] Obj K F w :=
  inclusion K F w v ∘ₗ TensorProduct.mk k _ _ g

/-- The chosen inner component's generator formula forces two-letter
compatibility with both canonical flattenings. The premise is supplied by
the checked one-letter weighted comparison, not by a crossing relation. -/
theorem coendSquarePairLinear_flatten
    (hfJ : ∀ (v s : C) (a : J.obj s ⟶ v) (b : M.obj (Q.obj s)),
      coendSquareInnerLinear J Q T M fJ v (tensor J (Q ⋙ M.toFunctor) s a b) =
        tensor T M.toFunctor (Q.obj s)
          (coendSquareCoefficient (k := k) J Q Q T hJ s v a) b)
    (w : C) :
    ((inductionComp T S).hom.app M).total (Q.obj w) ∘ₗ P w =
      coendSquareMap (J ⋙ K) Q Q (T ⋙ S) (coendSquare_comp_eq J K Q T S hJ hK)
        M.toFunctor w ∘ₗ ((inductionComp J K).hom.app RM).total w := by
  apply hom_ext
  intro v g b
  have hb :
      (((inductionComp T S).hom.app M).total (Q.obj w) ∘ₗ P w) ∘ₗ
          coendInsert K (induced J RM).toFunctor w v g =
      (coendSquareMap (J ⋙ K) Q Q (T ⋙ S) (coendSquare_comp_eq J K Q T S hJ hK)
        M.toFunctor w ∘ₗ ((inductionComp J K).hom.app RM).total w) ∘ₗ
          coendInsert K (induced J RM).toFunctor w v g := by
    apply hom_ext
    intro s a m
    change ((inductionComp T S).hom.app M).total (Q.obj w)
        (P w (tensor K (induced J RM).toFunctor v g (tensor J (Q ⋙ M.toFunctor) s a m))) =
      coendSquareMap (J ⋙ K) Q Q (T ⋙ S) (coendSquare_comp_eq J K Q T S hJ hK)
        M.toFunctor w (((inductionComp J K).hom.app RM).total w
          (tensor K (induced J RM).toFunctor v g (tensor J (Q ⋙ M.toFunctor) s a m)))
    rw [coendSquarePairLinear_tensor]
    change ((inductionComp T S).hom.app M).total (Q.obj w)
      (tensor S (induced T M).toFunctor (Q.obj v)
        (coendSquareCoefficient (k := k) K Q Q S hK v w g)
        (coendSquareInnerLinear J Q T M fJ v (tensor J (Q ⋙ M.toFunctor) s a m))) = _
    rw [hfJ, inductionComp_hom_total_tensor,
      inductionComp_hom_total_tensor, coendSquareMap_tensor]
    exact congrArg (fun h => tensor (T ⋙ S) M.toFunctor (Q.obj s) h m)
      (coendSquare_comp_coefficient (k := k) J K Q T S hJ hK s v w a g)
  exact LinearMap.congr_fun hb b

end Flatten
end OddMath.QuiverHecke.ELVOld.BalancedInduction
