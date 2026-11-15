import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalLong
import OddMath.QuiverHecke.CyclotomicAction.OutputTransport
import OddMath.QuiverHecke.CyclotomicAction.AppendSourceRows
import OddMath.QuiverHecke.CyclotomicAction.BoundaryNumerator
import OddMath.Algebra.DegreeShiftRowDivision
import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalInput
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices
import OddMath.QuiverHecke.CyclotomicAction.ChronologicalTails

/-!
# Even boundary recurrence

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The unshifted coefficient module and even moving source
The even-colour source comparison of DeformedMatrixComparison §4 uses
coefficient(0), ordinary restriction, and an even canonical J. Comparisons
are constructed pointwise before induction, keeping the literal coend.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def restrictedRepresentable (i : I) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  (BalancedInduction.restriction (append D Sc cutoff i)).obj
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))

theorem coefficientZero_obj_proj (i : I) (v : List I) (s : OldCategory D Sc cutoff)
    (q : ZMod 2) :
    ((coefficient D Sc cutoff 0 i v).obj s).proj q =
      ((restrictedRepresentable D Sc cutoff i v).obj s).proj q := by
  change (shiftedHom D Sc cutoff 0 v (s.word ++ [i])).proj q =
    (Supercategory.homSVec k (OldCategory D Sc cutoff)
      (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff i).obj s)).proj q
  rw [Supercategory.homSVec_proj]
  have hcat : (Supercategory.proj k q :
      ((⟨v⟩ : OldCategory D Sc cutoff) ⟶ (append D Sc cutoff i).obj s) →ₗ[k]
        ((⟨v⟩ : OldCategory D Sc cutoff) ⟶ (append D Sc cutoff i).obj s)) =
      oldProj D Sc cutoff v (s.word ++ [i]) q :=
    LinearMap.ext (oldCategory_proj D Sc cutoff ⟨v⟩ ((append D Sc cutoff i).obj s) q)
  refine Eq.trans ?_ hcat.symm
  rcases parity_eq_zero_or_one q with rfl | rfl
  · apply LinearMap.ext
    intro b
    change Old D Sc cutoff v (s.word ++ [i]) at b
    change b - oldProj D Sc cutoff v (s.word ++ [i]) (1 + 0) b =
      oldProj D Sc cutoff v (s.word ++ [i]) 0 b
    rw [add_zero]
    obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
    rw [oldProj_mk, oldProj_mk]
    have h := congrArg (ideal D Sc cutoff v (s.word ++ [i])).mkQ (proj_add_proj (R := k) a)
    rw [map_add] at h
    exact (eq_sub_of_add_eq h).symm
  · rfl

theorem coefficientZero_map (i : I) (v : List I) {s t : OldCategory D Sc cutoff}
    (f : s ⟶ t) (b : Old D Sc cutoff v (s.word ++ [i])) :
    (coefficient D Sc cutoff 0 i v).map f b =
      (restrictedRepresentable D Sc cutoff i v).map f b := by
  change (oldRepresentableFunctor D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).map
      ((append D Sc cutoff i).map (oldTwist D Sc cutoff 0 s.word t.word f)) b =
    (oldRepresentableFunctor D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).map
      ((append D Sc cutoff i).map f) b
  rw [← oldCategory_twist D Sc cutoff s t 0 f, twist_zero]

instance coefficientZero_additive (i : I) (v : List I) :
    (coefficient D Sc cutoff 0 i v).Additive where
  map_add {s t} f g := by
    apply LinearMap.ext
    intro b
    change (coefficient D Sc cutoff 0 i v).map (f + g) b =
      (coefficient D Sc cutoff 0 i v).map f b + (coefficient D Sc cutoff 0 i v).map g b
    rw [coefficientZero_map, coefficientZero_map, coefficientZero_map]
    exact congrArg (fun h => h b)
      ((restrictedRepresentable D Sc cutoff i v).toFunctor.map_add (f := f) (g := g))

instance coefficientZero_linear (i : I) (v : List I) :
    (coefficient D Sc cutoff 0 i v).Linear k where
  map_smul {s t} f r := by
    apply LinearMap.ext
    intro b
    change (coefficient D Sc cutoff 0 i v).map (r • f) b =
      r • (coefficient D Sc cutoff 0 i v).map f b
    rw [coefficientZero_map, coefficientZero_map]
    exact congrArg (fun h => h b)
      ((restrictedRepresentable D Sc cutoff i v).toFunctor.map_smul r f)

theorem coefficientZero_obj_part (i : I) (v : List I) (s : OldCategory D Sc cutoff)
    (q : ZMod 2) :
    ((coefficient D Sc cutoff 0 i v).obj s).part q =
      ((restrictedRepresentable D Sc cutoff i v).obj s).part q := by
  ext b
  rw [SVec.mem_part_iff, SVec.mem_part_iff, coefficientZero_obj_proj]
  rfl

instance coefficientZero_super (i : I) (v : List I) :
    IsSuperfunctor k (coefficient D Sc cutoff 0 i v) where
  map_mem := by
    intro s t p f hf
    apply SVec.mem_parityHom_of_apply_mem
    intro q b hb
    change b ∈ ((coefficient D Sc cutoff 0 i v).obj s).part q at hb
    rw [coefficientZero_obj_part] at hb
    change (coefficient D Sc cutoff 0 i v).map f b ∈
      ((coefficient D Sc cutoff 0 i v).obj t).part (q + p)
    rw [coefficientZero_obj_part, coefficientZero_map]
    exact SVec.apply_mem_part
      (map_mem (restrictedRepresentable D Sc cutoff i v).toFunctor hf) hb

def coefficientZeroModule (i : I) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  ⟨coefficient D Sc cutoff 0 i v⟩

def coefficientRestrictionIso (i : I) (v : List I) :
    coefficient D Sc cutoff 0 i v ≅
      (restrictedRepresentable D Sc cutoff i v).toFunctor :=
  NatIso.ofComponents (fun _ =>
    { hom := LinearMap.id
      inv := LinearMap.id
      hom_inv_id := by ext b; rfl
      inv_hom_id := by ext b; rfl }) (by
        intro s t f
        apply LinearMap.ext
        intro b
        exact coefficientZero_map D Sc cutoff i v f b)

def coefficientRestrictionModuleIso (i : I) (v : List I) :
    coefficientZeroModule D Sc cutoff i v ≅ restrictedRepresentable D Sc cutoff i v :=
  moduleIsoOfEvenNatIso _ _ (coefficientRestrictionIso D Sc cutoff i v)
    (by
      intro s q
      change LinearMap.id ∘ₗ ((coefficient D Sc cutoff 0 i v).obj s).proj q =
        ((restrictedRepresentable D Sc cutoff i v).obj s).proj (q+0) ∘ₗ LinearMap.id
      rw [add_zero, LinearMap.id_comp, LinearMap.comp_id, coefficientZero_obj_proj])
    (by
      intro s q
      change LinearMap.id ∘ₗ ((restrictedRepresentable D Sc cutoff i v).obj s).proj q =
        ((coefficient D Sc cutoff 0 i v).obj s).proj (q+0) ∘ₗ LinearMap.id
      rw [add_zero, LinearMap.id_comp, LinearMap.comp_id, coefficientZero_obj_proj])

instance evenMovingCoefficient_additive (i : {i : I // D.parity i = 0}) (v : List I) :
    (coefficient D Sc cutoff (D.parity i.1) i.1 v).Additive := by
  simpa only [i.property] using coefficientZero_additive D Sc cutoff i.1 v
instance evenMovingCoefficient_linear (i : {i : I // D.parity i = 0}) (v : List I) :
    (coefficient D Sc cutoff (D.parity i.1) i.1 v).Linear k := by
  simpa only [i.property] using coefficientZero_linear D Sc cutoff i.1 v
instance evenMovingCoefficient_super (i : {i : I // D.parity i = 0}) (v : List I) :
    IsSuperfunctor k (coefficient D Sc cutoff (D.parity i.1) i.1 v) := by
  simpa only [i.property] using coefficientZero_super D Sc cutoff i.1 v

def evenMovingCoefficientModule (i : {i : I // D.parity i = 0}) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  ⟨coefficient D Sc cutoff (D.parity i.1) i.1 v⟩

def evenMovingCoefficientNatIso (i : {i : I // D.parity i = 0}) (v : List I) :
    (evenMovingCoefficientModule D Sc cutoff i v).toFunctor ≅
      (coefficientZeroModule D Sc cutoff i.1 v).toFunctor :=
  NatIso.ofComponents (fun _ =>
    { hom := LinearMap.id
      inv := LinearMap.id
      hom_inv_id := by ext b; rfl
      inv_hom_id := by ext b; rfl }) (by
        intro s t f
        apply LinearMap.ext
        intro b
        change (coefficient D Sc cutoff (D.parity i.1) i.1 v).map f b =
          (coefficient D Sc cutoff 0 i.1 v).map f b
        rw [i.property])

def evenMovingCoefficientIso (i : {i : I // D.parity i = 0}) (v : List I) :
    evenMovingCoefficientModule D Sc cutoff i v ≅ coefficientZeroModule D Sc cutoff i.1 v :=
  moduleIsoOfEvenNatIso _ _ (evenMovingCoefficientNatIso D Sc cutoff i v)
    (by
      intro s q
      change LinearMap.id ∘ₗ ((coefficient D Sc cutoff (D.parity i.1) i.1 v).obj s).proj q =
        ((coefficient D Sc cutoff 0 i.1 v).obj s).proj (q+0) ∘ₗ LinearMap.id
      rw [add_zero, LinearMap.id_comp, LinearMap.comp_id, i.property])
    (by
      intro s q
      change LinearMap.id ∘ₗ ((coefficient D Sc cutoff 0 i.1 v).obj s).proj q =
        ((coefficient D Sc cutoff (D.parity i.1) i.1 v).obj s).proj (q+0) ∘ₗ LinearMap.id
      rw [add_zero, LinearMap.id_comp, LinearMap.comp_id, i.property])

/-- The comparison is induced from an actual pointwise module iso. -/
def coefficientZeroSourceEquiv (i : {i : I // D.parity i = 0}) (v t : List I) :
    BalancedInduction.Obj (append D Sc cutoff i.1)
      (coefficient D Sc cutoff 0 i.1 v) (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      Source D Sc cutoff i.1 v t :=
  moduleIsoLinearEquiv
    (((BalancedInduction.induction (append D Sc cutoff i.1)).mapIso
      (evenMovingCoefficientIso D Sc cutoff i v)).symm)
    (⟨t⟩ : OldCategory D Sc cutoff)

def unshiftedSourceIso (i : I) (v : List I) :
    (BalancedInduction.restriction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ≅
    (BalancedInduction.induction (append D Sc cutoff i)).obj (coefficientZeroModule D Sc cutoff i v) :=
  (BalancedInduction.induction (append D Sc cutoff i)).mapIso
    (coefficientRestrictionModuleIso D Sc cutoff i v).symm

/-- The even canonical J component, with no chosen source equivalence premise. -/
def evenSourceEquiv (i : {i : I // D.parity i = 0}) (v t : List I) :
    (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
      Source D Sc cutoff i.1 v t :=
  (moduleIsoLinearEquiv (unshiftedSourceIso D Sc cutoff i.1 v)
    (⟨t⟩ : OldCategory D Sc cutoff)).trans
      (coefficientZeroSourceEquiv D Sc cutoff i v t)

@[simp] theorem evenMovingCoefficientIso_inv_app (i : {i : I // D.parity i = 0})
    (v : List I) (p : ZMod 2) (s : OldCategory D Sc cutoff) :
    (evenMovingCoefficientIso D Sc cutoff i v).inv.app p s =
      if p = 0 then LinearMap.id else 0 := rfl

@[simp] theorem coefficientRestrictionModuleIso_inv_app (i : I)
    (v : List I) (p : ZMod 2) (s : OldCategory D Sc cutoff) :
    (coefficientRestrictionModuleIso D Sc cutoff i v).inv.app p s =
      if p = 0 then LinearMap.id else 0 := rfl

theorem coefficientZeroSourceEquiv_tensor (i : {i : I // D.parity i = 0})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [i.1]) t)
    (b : Old D Sc cutoff v (s ++ [i.1])) :
    coefficientZeroSourceEquiv D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i.1)
        (coefficient D Sc cutoff 0 i.1 v) (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      tensor D Sc cutoff i.1 v s t g b := by
  change (BalancedInduction.moduleMap (append D Sc cutoff i.1)
    (evenMovingCoefficientIso D Sc cutoff i v).inv).total _
      (BalancedInduction.tensor _ _ _ g b) = _
  rw [BalancedInduction.moduleMap_total_tensor]
  simp only [evenMovingCoefficientIso_inv_app, ↓reduceIte, one_ne_zero]
  change BalancedInduction.tensor (append D Sc cutoff i.1)
      (coefficient D Sc cutoff (D.parity i.1) i.1 v) (⟨s⟩ : OldCategory D Sc cutoff) g b +
    BalancedInduction.tensor (append D Sc cutoff i.1)
      (coefficient D Sc cutoff (D.parity i.1) i.1 v) (⟨s⟩ : OldCategory D Sc cutoff)
      (twist k 1 (X := (append D Sc cutoff i.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g) 0 = _
  rw [BalancedInduction.tensor_zero_right, add_zero]
  rfl

theorem unshiftedSourceIso_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    moduleIsoLinearEquiv (unshiftedSourceIso D Sc cutoff i v)
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        (restrictedRepresentable D Sc cutoff i v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        (coefficient D Sc cutoff 0 i v) (⟨s⟩ : OldCategory D Sc cutoff) g b := by
  change (BalancedInduction.moduleMap (append D Sc cutoff i)
    (coefficientRestrictionModuleIso D Sc cutoff i v).inv).total _
      (BalancedInduction.tensor _ _ _ g b) = _
  rw [BalancedInduction.moduleMap_total_tensor]
  simp only [coefficientRestrictionModuleIso_inv_app, ↓reduceIte, one_ne_zero]
  change BalancedInduction.tensor (append D Sc cutoff i)
      (coefficient D Sc cutoff 0 i v) (⟨s⟩ : OldCategory D Sc cutoff) g b +
    BalancedInduction.tensor (append D Sc cutoff i)
      (coefficient D Sc cutoff 0 i v) (⟨s⟩ : OldCategory D Sc cutoff)
      (twist k 1 (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g) 0 = _
  rw [BalancedInduction.tensor_zero_right, add_zero]

theorem evenSourceEquiv_tensor (i : {i : I // D.parity i = 0})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [i.1]) t)
    (b : Old D Sc cutoff v (s ++ [i.1])) :
    evenSourceEquiv D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i.1)
        (restrictedRepresentable D Sc cutoff i.1 v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      tensor D Sc cutoff i.1 v s t g b := by
  change coefficientZeroSourceEquiv D Sc cutoff i v t
    (moduleIsoLinearEquiv (unshiftedSourceIso D Sc cutoff i.1 v)
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor _ _ _ g b)) = _
  exact (congrArg (coefficientZeroSourceEquiv D Sc cutoff i v t)
    (unshiftedSourceIso_tensor D Sc cutoff i.1 v s t g b)).trans
      (coefficientZeroSourceEquiv_tensor D Sc cutoff i v s t g b)

theorem unshiftedAdjunctionCounit_total_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    ((BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        (restrictedRepresentable D Sc cutoff i v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      oldComp D Sc cutoff v (s ++ [i]) t b g := by
  change BalancedInduction.counit (append D Sc cutoff i)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).toFunctor
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).toFunctor)
        (⟨s⟩ : OldCategory D Sc cutoff) g b) + 0 = _
  rw [add_zero, BalancedInduction.counit_tensor]
  rfl

/-- A typed component of the chosen ordinary adjunction counit. -/
def unshiftedCounitComponent (i : I) (v t : List I) :
    (((BalancedInduction.restriction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) →ₗ[k] Old D Sc cutoff v t :=
  ((BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
    (⟨t⟩ : OldCategory D Sc cutoff)

theorem unshiftedCounitComponent_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    unshiftedCounitComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        (restrictedRepresentable D Sc cutoff i v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      oldComp D Sc cutoff v (s ++ [i]) t b g :=
  unshiftedAdjunctionCounit_total_tensor D Sc cutoff i v s t g b

private def negativeContraction {A B C : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module k A] [Module k B] [Module k C]
    (f : A →ₗ[k] C) (e : A ≃ₗ[k] B) : B →ₗ[k] C :=
  -f.comp e.symm.toLinearMap

private theorem negativeContraction_apply {A B C : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module k A] [Module k B] [Module k C]
    (f : A →ₗ[k] C) (e : A ≃ₗ[k] B) (z : A) :
    negativeContraction f e (e z) = -f z := by
  simp only [negativeContraction, LinearMap.neg_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The even raw contraction is minus the chosen ordinary adjunction counit.
The constant minus is part of the prescribed raw normalization. -/
def evenSourceInputContraction (i : {i : I // D.parity i = 0}) (v t : List I) :
    Source D Sc cutoff i.1 v t →ₗ[k] Old D Sc cutoff v t :=
  negativeContraction (unshiftedCounitComponent D Sc cutoff i.1 v t)
    (evenSourceEquiv D Sc cutoff i v t)

theorem evenSourceInputContraction_counit (i : {i : I // D.parity i = 0})
    (v t : List I)
    (z : ((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    evenSourceInputContraction D Sc cutoff i v t
      (evenSourceEquiv D Sc cutoff i v t z) =
      -unshiftedCounitComponent D Sc cutoff i.1 v t z := by
  exact negativeContraction_apply (unshiftedCounitComponent D Sc cutoff i.1 v t)
    (evenSourceEquiv D Sc cutoff i v t) z

theorem evenSourceInputContraction_tensor (i : {i : I // D.parity i = 0})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [i.1]) t)
    (b : Old D Sc cutoff v (s ++ [i.1])) :
    evenSourceInputContraction D Sc cutoff i v t
      (tensor D Sc cutoff i.1 v s t g b) =
      -oldComp D Sc cutoff v (s ++ [i.1]) t b g := by
  calc
    _ = evenSourceInputContraction D Sc cutoff i v t
        (evenSourceEquiv D Sc cutoff i v t
          (BalancedInduction.tensor (append D Sc cutoff i.1)
            (restrictedRepresentable D Sc cutoff i.1 v).toFunctor
            (⟨s⟩ : OldCategory D Sc cutoff) g b)) :=
      congrArg (evenSourceInputContraction D Sc cutoff i v t)
        (evenSourceEquiv_tensor D Sc cutoff i v s t g b).symm
    _ = -unshiftedCounitComponent D Sc cutoff i.1 v t
        (BalancedInduction.tensor (append D Sc cutoff i.1)
          (restrictedRepresentable D Sc cutoff i.1 v).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b) :=
      evenSourceInputContraction_counit D Sc cutoff i v t _
    _ = _ := congrArg Neg.neg (unshiftedCounitComponent_tensor D Sc cutoff i.1 v s t g b)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Even moving dots on arbitrary old-Hom long coordinates

The parity-zero specialization of DeformedMackeyBoundary (2)-(3).
The moving dot acts by the ordinary finite coefficient shift, on every
source class and on the specified long section. Full exterior old
coefficients are retained; there is no delta correction at even colour.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Ordinary finite coefficient shift, without a parity involution. -/
def evenLongShift (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.lmapDomain (Old D Sc cutoff v t) k Nat.succ

@[simp] theorem evenLongShift_single (v t : List I) (m : ℕ)
    (b : Old D Sc cutoff v t) :
    evenLongShift D Sc cutoff v t (Finsupp.single m b) = Finsupp.single (m + 1) b := by
  simp only [evenLongShift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private theorem evenOldTwist_zero (v t : List I) (b : Old D Sc cutoff v t) :
    oldTwist D Sc cutoff 0 v t b = b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  change (ideal D Sc cutoff v t).mkQ (twist k 0 b) = _
  rw [twist_zero]

private theorem longHomCoordinate_evenMoving_succ (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) {v t : List I} (y : NFIdx v t) (m : ℕ)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomCoordinate D Sc cutoff p i y (1 + m)
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) =
      longHomCoordinate D Sc cutoff p i y m z := by
  have h := prependOldCoordinate_signedMoving D Sc cutoff p (longHomIndex i y m) 1 z
  change prependOldCoordinate D Sc cutoff p (longHomIndex i y (1 + m))
    (signedMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1 z) =
    oldTwist D Sc cutoff (1 • D.parity i) v (longHomIndex i y m).oldTarget
      (prependOldCoordinate D Sc cutoff p (longHomIndex i y m) z) at h
  simp only [hi, smul_zero, evenOldTwist_zero] at h
  have transport {s : List I} (e : s = t)
      (f g : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
      (a : Target D Sc cutoff i v (t ++ [i])) (h : f a = g z) :
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) f) a =
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) g) z := by
    subst s
    exact h
  unfold longHomCoordinate
  simp only [hi, zero_mul, SKM.zsign_zero, one_pow, one_smul]
  exact transport (longHomIndex_oldTarget i y m) _ _ _ h

private theorem longHomCoordinate_evenMoving_zero (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) {v t : List I} (y : NFIdx v t)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomCoordinate D Sc cutoff p i y 0
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) = 0 := by
  have h : prependOldCoordinate D Sc cutoff p (longHomIndex i y 0)
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) = 0 := by
    obtain ⟨f, rfl⟩ := prependOldReconstruct_surjective D Sc cutoff p i v (t ++ [i]) z
    induction f using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg, add_zero]
    | of q b =>
      change prependOldCoordinate D Sc cutoff p (longHomIndex i y 0)
        (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
          (prependOldReconstruct D Sc cutoff p i v (t ++ [i]) (DirectSum.lof k _ _ q b))) = 0
      rw [prependOldReconstruct, DirectSum.toModule_lof, movingPower_pair_shift]
      apply prependOldCoordinate_pair_off
      intro he
      have hn := congrArg Prod.fst he
      change 0 = 1 + q.representative.1.1 at hn
      omega
  have transport {s : List I} (e : s = t)
      (f : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
      (a : Target D Sc cutoff i v (t ++ [i])) (h : f a = 0) :
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) f) a = 0 := by
    subst s
    exact h
  unfold longHomCoordinate
  simp only [pow_zero, one_smul]
  exact transport (longHomIndex_oldTarget i y 0) _ _ h

theorem longHomExtraction_evenMoving (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    {v t : List I} (y : NFIdx v t) (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomExtraction D Sc cutoff p i y
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) =
      evenLongShift D Sc cutoff v t (longHomExtraction D Sc cutoff p i y z) := by
  apply Finsupp.ext
  intro m
  cases m with
  | zero =>
    rw [longHomExtraction_apply,
      longHomCoordinate_evenMoving_zero D Sc cutoff p i hi y z]
    simp only [evenLongShift, Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
  | succ m =>
    rw [longHomExtraction_apply]
    have h := longHomCoordinate_evenMoving_succ D Sc cutoff p i hi y m z
    rw [Nat.add_comm 1 m] at h
    rw [h]
    simp only [evenLongShift, Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_apply_of_injective Nat.succ_injective]
    rfl

/-- Every arbitrary-endpoint source class satisfies the even first-dot recurrence. -/
theorem offDiagonalLongExtraction_evenMoving (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (z : Target D Sc cutoff i v (t ++ [i])) :
    offDiagonalLongExtraction D Sc cutoff p i v t
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) =
      evenLongShift D Sc cutoff v t (offDiagonalLongExtraction D Sc cutoff p i v t z) := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    simp only [offDiagonalLongExtraction_eq D Sc cutoff p i y]
    exact longHomExtraction_evenMoving D Sc cutoff p i hi y z
  · simp only [offDiagonalLongExtraction, dite_eq_right h, LinearMap.zero_apply, map_zero]

theorem evenMoving_longHomLift (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    {v t : List I} (y : NFIdx v t) (m : ℕ) (b : Old D Sc cutoff v t) :
    movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
      (longHomLift D Sc cutoff p i y m b) = longHomLift D Sc cutoff p i y (m + 1) b := by
  have transport {s : List I} (e : s = t)
      (f g : Old D Sc cutoff v s →ₗ[k] Target D Sc cutoff i v (t ++ [i]))
      (h : ∀ b, movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) (f b) = g b) :
      ∀ b : Old D Sc cutoff v t,
      movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
        ((Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
          Target D Sc cutoff i v (t ++ [i])) e) f) b) =
      (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
        Target D Sc cutoff i v (t ++ [i])) e) g) b := by
    subst s
    exact h
  unfold longHomLift
  simp only [hi, zero_mul, SKM.zsign_zero, one_pow, one_smul]
  apply transport (longHomIndex_oldTarget i y m)
  intro c
  have h := movingPower_pair_shift D Sc cutoff p (longHomIndex i y m) 1 (by simp [hi]) c
  have ht : prependTail D Sc ((longHomIndex i y m).shift 1) =
      prependTail D Sc (longHomIndex i y (m + 1)) :=
    congrArg (fun n : ℕ => (show (pres D Sc).obj (ob D
      (i :: (longHomIndex i y m).oldTarget)) ⟶
        (pres D Sc).obj (ob D (t ++ [i])) from
          prependTail D Sc (longHomIndex i y n))) (Nat.add_comm 1 m)
  rw [ht] at h
  exact h

/-- The prescribed long section intertwines the even moving dot and ordinary shift. -/
theorem evenMoving_offDiagonalLongSection (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
      (offDiagonalLongSection D Sc cutoff p i v t f) =
      offDiagonalLongSection D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    simp only [offDiagonalLongSection_eq D Sc cutoff p i y]
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single m b =>
      simp only [longHomSection, Finsupp.lsum_single, evenLongShift_single]
      exact evenMoving_longHomLift D Sc cutoff p i hi y m b
  · have hf : f = 0 := by
      ext n
      exact old_eq_zero_of_no_normal_form D Sc cutoff h (f n)
    rw [hf]
    simp only [map_zero]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Independent S in the even polynomial boundary

The parity-zero polynomial projection of DeformedMackeyBoundary (5).
The canonical arbitrary-Hom coordinates agree with the established diagonal
coordinates. This permits the independently defined S to be used in the
actual C0P boundary, whose even iterates have the prescribed ordered reverse
numerator. No boundary division or categorical inverse is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem diagonalCastPair (p : ZMod 2) (i : I) {v w s s' : List I}
    (e : s = v) (e' : s' = v)
    (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (i :: s')) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    Eq.mp (congrArg (fun a => Old D Sc cutoff v a →ₗ[k] Target D Sc cutoff i v w) e)
      (pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)) =
    Eq.mp (congrArg (fun a => Old D Sc cutoff v a →ₗ[k] Target D Sc cutoff i v w) e')
      (pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g)) := by
  subst s
  subst s'
  cases h
  rfl

theorem longHomLift_diagonal (p : ZMod 2) (i : I) (v : List I)
    (y : NFIdx v v) (m : ℕ) :
    longHomLift D Sc cutoff p i y m = outputLongLift D Sc cutoff p i v m := by
  have hk : (longHomIndex i y m).tailKey = (longOutputIndex i v m).tailKey :=
    Prod.ext rfl (longHomIndex_shuffle i y m)
  unfold longHomLift outputLongLift
  exact congrArg
    (fun f : Old D Sc cutoff v v →ₗ[k] Target D Sc cutoff i v (v ++ [i]) =>
      (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m • f)
    (diagonalCastPair D Sc cutoff p i
      (longHomIndex_oldTarget i y m) (longOutputIndex_oldTarget i v m) _ _
      (prependTail_heq_of_tailKey_eq D Sc _ _ hk))

/-- Diagonal specialization preserves the prescribed normalized long section. -/
theorem offDiagonalLongSection_diagonal (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    offDiagonalLongSection D Sc cutoff p i v v f = outputLongSection D Sc cutoff p i v f := by
  let y : NFIdx v v :=
    Eq.mp (congrArg (fun t => NFIdx v t) (longOutputIndex_oldTarget i v 0))
      (longOutputIndex i v 0).old
  rw [offDiagonalLongSection_eq D Sc cutoff p i y]
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    simp only [longHomSection, Finsupp.lsum_single, outputLongSection_single,
      longHomLift_diagonal]

/-- The arbitrary-Hom extraction restricts to the established diagonal extraction. -/
theorem offDiagonalLongExtraction_diagonal (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    offDiagonalLongExtraction D Sc cutoff p i v v z = outputLongExtraction D Sc cutoff p i v z := by
  let d := z - outputLongSection D Sc cutoff p i v (outputLongExtraction D Sc cutoff p i v z)
  have hd : d ∈ chronologicalShortSpan D Sc cutoff i v v := by
    rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v,
      LinearMap.mem_ker]
    dsimp only [d]
    rw [map_sub, outputLongExtraction_section, sub_self]
  have he : offDiagonalLongExtraction D Sc cutoff p i v v d = 0 := by
    rw [← LinearMap.mem_ker,
      ker_offDiagonalLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v v]
    exact hd
  dsimp only [d] at he
  rw [map_sub, ← offDiagonalLongSection_diagonal, offDiagonalLongExtraction_section,
    sub_eq_zero] at he
  exact he

/-- Every even iterate extracts to the ordinary finite shift iterate. -/
theorem offDiagonalLongExtraction_evenMoving_iterate (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (d : ℕ)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    offDiagonalLongExtraction D Sc cutoff p i v t
      ((movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]))^[d] z) =
    (evenLongShift D Sc cutoff v t)^[d] (offDiagonalLongExtraction D Sc cutoff p i v t z) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply',
      offDiagonalLongExtraction_evenMoving D Sc cutoff p i hi, ih,
      Function.iterate_succ_apply']

theorem offDiagonalLongExtraction_move_independentS (p : ZMod 2) (i : I) (v : List I) :
    offDiagonalLongExtraction D Sc cutoff p i v v
      (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v)) =
      SKM.zsign k (D.parity i) ^ v.count i • independentOutputS D Sc cutoff i v := by
  rw [offDiagonalLongExtraction_diagonal]
  exact outputLongExtraction_move_independentS D Sc cutoff p i v

/-- The even iterated moving intertwiner extracts to the independent S polynomial. -/
theorem offDiagonalLongExtraction_evenMoving_move (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v : List I) (d : ℕ) :
    offDiagonalLongExtraction D Sc cutoff p i v v
      ((movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]))^[d]
        (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v))) =
      (evenLongShift D Sc cutoff v v)^[d] (independentOutputS D Sc cutoff i v) := by
  rw [offDiagonalLongExtraction_evenMoving_iterate D Sc cutoff p i hi,
    offDiagonalLongExtraction_move_independentS]
  simp only [hi, SKM.zsign_zero, one_pow, one_smul]

/-- Independent S compares with the ordered reverse numerator under actual C0P. -/
theorem offDiagonalPolynomialBoundary_even_independentS (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v : List I) (d : ℕ) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v v
      ((evenLongShift D Sc cutoff v v)^[d] (independentOutputS D Sc cutoff i v)) =
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v)) := by
  have h := appendC0_pMap_offDiagonal D Sc cutoff p i v v
    ((movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]))^[d]
      (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v)))
  have hp := pMap_evenDot_move_iterate D Sc cutoff i hi v (v ++ [i]) d (𝟙 _)
  simp only [Category.comp_id] at hp
  rw [hp, offDiagonalLongExtraction_evenMoving_move D Sc cutoff p i hi] at h
  exact h.symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Even input-dot recurrence for the polynomial boundary

The parity-zero specialization of DeformedBoundaryDivision (8).
On arbitrary old Homs the actual polynomial boundary commutes with ordinary
coefficient shift up to a polynomial-constant defect. Its iterated high
coordinates therefore telescope exactly. Every exterior old coefficient is
retained; no restriction is imposed on the other colours or their support.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem evenBoundary_twist_zero (v t : List I) (b : Old D Sc cutoff v t) :
    oldTwist D Sc cutoff 0 v t b = b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  change (ideal D Sc cutoff v t).mkQ (twist k 0 b) = _
  rw [twist_zero]

/-- At even moving colour the input shift is the ordinary coefficient shift. -/
theorem appendInputShift_eq_evenLongShift (i : I) (hi : D.parity i = 0)
    (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    appendInputShift D Sc cutoff i v t f = evenLongShift D Sc cutoff v t f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    simp only [appendInputShift, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, appendOutputShift, Finsupp.lsum_single, Finsupp.lsingle_apply,
      hi, evenBoundary_twist_zero, evenLongShift_single]

theorem evenLongShift_apply_succ (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) (m : ℕ) :
    evenLongShift D Sc cutoff v t f (m + 1) = f m := by
  exact Finsupp.mapDomain_apply_of_injective Nat.succ_injective f m

/-- The only defect of even input-dot compatibility is polynomial-constant. -/
theorem offDiagonalPolynomialBoundary_even_shift (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) =
      evenLongShift D Sc cutoff v t (offDiagonalPolynomialBoundary D Sc cutoff p i v t f) +
      Finsupp.single 0
        (appendC0InputDefect D Sc cutoff i v t
          (pMap D Sc cutoff i v (t ++ [i]) (offDiagonalLongSection D Sc cutoff p i v t f)) 0) := by
  let z := pMap D Sc cutoff i v (t ++ [i]) (offDiagonalLongSection D Sc cutoff p i v t f)
  have h := appendC0InputDefect_degreeZero D Sc cutoff i v t z
  change appendC0 D Sc cutoff i v t
    (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1 z) -
      appendInputShift D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) = _ at h
  have hp := pMap_movingEvenDot D Sc cutoff i hi v (t ++ [i])
    (offDiagonalLongSection D Sc cutoff p i v t f)
  rw [evenMoving_offDiagonalLongSection D Sc cutoff p i hi] at hp
  rw [← hp] at h
  change offDiagonalPolynomialBoundary D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) -
    appendInputShift D Sc cutoff i v t (offDiagonalPolynomialBoundary D Sc cutoff p i v t f) = _ at h
  rw [appendInputShift_eq_evenLongShift D Sc cutoff i hi] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- Exact high-coordinate telescoping of all even boundary iterates. -/
theorem offDiagonalPolynomialBoundary_even_iterate_high (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (n m : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t
      ((evenLongShift D Sc cutoff v t)^[n] f) (n + m) =
      offDiagonalPolynomialBoundary D Sc cutoff p i v t f m := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, zero_add]
  | succ n ih =>
    rw [Function.iterate_succ_apply',
      offDiagonalPolynomialBoundary_even_shift D Sc cutoff p i hi]
    have he : n + 1 + m = (n + m) + 1 := by omega
    rw [he, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega), add_zero,
      evenLongShift_apply_succ, ih]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Ordered independent-S products at even moving colour

The parity-zero monic-S algebra in DeformedBoundaryDivision (5).
The existing ordered S product acts on full old coefficients. Its top
coefficient detects the input bound, including zero old corners. No
support restriction on exterior coefficients or the other colours is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem evenS_twist_zero (v : List I) (c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff 0 v v c = c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k 0 c) = _
  rw [twist_zero]

theorem independentSRightProduct_even_high (i : I) (hi : D.parity i = 0)
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ)
    (hm : outputSDegree D i v ≤ m) :
    independentSRightProduct D Sc cutoff i v f m =
      ∑ n ∈ (independentOutputS D Sc cutoff i v).support,
        oldComp D Sc cutoff v v v (f (m - n)) (independentOutputS D Sc cutoff i v n) := by
  simp only [independentSRightProduct, LinearMap.sum_apply, LinearMap.comp_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply, LinearMap.flip_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hnm : n ≤ m := by
    have h := independentOutputS_support D Sc cutoff i v hn
    rw [Finset.mem_range] at h
    omega
  have he : m = n + (m - n) := by omega
  rw [he, inputCoefficientShift_apply_add]
  rw [hi, nsmul_zero, evenS_twist_zero]
  simp only [Nat.add_sub_cancel_left]

/-- The leading coefficient of the actual S product is the input coefficient,
with no nonzero-corner hypothesis. -/
theorem independentSRightProduct_even_top (i : I) (hi : D.parity i = 0)
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (M : ℕ)
    (hf : ∀ m, M < m → f m = 0) :
    independentSRightProduct D Sc cutoff i v f (M + outputSDegree D i v) = f M := by
  rw [independentSRightProduct_even_high D Sc cutoff i hi v f _ (by omega)]
  rw [Finset.sum_eq_single (outputSDegree D i v)]
  · rw [Nat.add_sub_cancel, independentOutputS_top]
    obtain ⟨b, hb⟩ := (ideal D Sc cutoff v v).mkQ_surjective (f M)
    rw [← hb, oldComp_mk, Category.comp_id]
  · intro n hn hne
    have h := independentOutputS_support D Sc cutoff i v hn
    rw [Finset.mem_range] at h
    rw [hf _ (by omega), map_zero, LinearMap.zero_apply]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, map_zero]

/-- If the S product vanishes above B, each possible input coefficient above
B-D vanishes, phrased without truncated subtraction or a nonzero hypothesis. -/
theorem independentSRightProduct_even_detect_bound (i : I) (hi : D.parity i = 0)
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (B : ℕ)
    (hf : ∀ m, outputSDegree D i v ≤ m → B < m →
      independentSRightProduct D Sc cutoff i v f m = 0)
    (m : ℕ) (hm : B < m + outputSDegree D i v) : f m = 0 := by
  by_contra h
  have hs : f.support.Nonempty := ⟨m, Finsupp.mem_support_iff.mpr h⟩
  obtain ⟨M, hM, hmax⟩ := f.support.exists_max_image id hs
  have hbound : ∀ n, M < n → f n = 0 := by
    intro n hn
    by_contra hz
    have hh := hmax n (Finsupp.mem_support_iff.mpr hz)
    change n ≤ M at hh
    omega
  have hle := hmax m (Finsupp.mem_support_iff.mpr h)
  change m ≤ M at hle
  have ht := independentSRightProduct_even_top D Sc cutoff i hi v f M hbound
  rw [hf _ (by omega) (by omega)] at ht
  exact (Finsupp.mem_support_iff.mp hM) ht.symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Leading coefficients of the even polynomial boundary

The parity-zero independent-S argument in DeformedBoundaryDivision (5).
The boundary is the specified arbitrary-Hom C0P map. Its diagonal row on the
old identity has the prescribed scalar-unit top coefficient and vanishes
above its bound, including the negative-height case and zero old corners.
This is a diagonal coefficient theorem, not an even categorical inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The canonical diagonal specialization retains full coefficient covariance. -/
theorem offDiagonalPolynomialBoundary_diagonal_rightAction (p : ZMod 2) (i : I)
    (v : List I) (c : Old D Sc cutoff v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v v
      (outputCoefficientRightAction D Sc cutoff i
        (p + D.parity i * wordSumParity D v) v c f) =
    outputCoefficientRightAction D Sc cutoff i 0 v c
      (offDiagonalPolynomialBoundary D Sc cutoff p i v v f) := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  have h0 := appendC0_pMap_offDiagonal D Sc cutoff p i v v
    (outputLongSection D Sc cutoff p i v f)
  rw [offDiagonalLongExtraction_diagonal, outputLongExtraction_section] at h0
  have h := appendC0_pMap_offDiagonal D Sc cutoff p i v v
    (act D Sc cutoff i (appendInsert D Sc cutoff i v v g)
      (outputLongSection D Sc cutoff p i v f))
  rw [offDiagonalLongExtraction_diagonal, outputLongExtraction_rightAction,
    outputLongExtraction_section] at h
  rw [pMap_postcomp, appendC0_postcomp, h0] at h
  exact h.symm

theorem offDiagonalPolynomialBoundary_independentS_postcomp (p : ZMod 2) (i : I)
    (v : List I) (n : ℕ) (f : ℕ →₀ Old D Sc cutoff v v) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v v
      (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
        (independentOutputS D Sc cutoff i v n)) f) =
    Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff i v n))
      (offDiagonalPolynomialBoundary D Sc cutoff p i v v f) := by
  have he (q : ZMod 2) (h : ℕ →₀ Old D Sc cutoff v v) :
      outputCoefficientRightAction D Sc cutoff i q v
        (independentOutputS D Sc cutoff i v n) h =
      Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
        (independentOutputS D Sc cutoff i v n)) h := by
    ext m
    rw [outputCoefficientRightAction_apply, independentOutputS_oldTwist]
    rfl
  have h := offDiagonalPolynomialBoundary_diagonal_rightAction D Sc cutoff p i v
    (independentOutputS D Sc cutoff i v n) f
  simpa only [he] using h

/-- Evaluation of independent S in the ordinary even coefficient shift. -/
def evenSAtShift (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  ∑ n ∈ (independentOutputS D Sc cutoff i v).support,
    (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff i v n))).comp
        ((evenLongShift D Sc cutoff v v) ^ n)

/-- The S boundary defect is confined below the independently proved S bound. -/
theorem offDiagonalPolynomialBoundary_even_S_high (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v : List I) (f : ℕ →₀ Old D Sc cutoff v v)
    (m : ℕ) (hm : outputSDegree D i v ≤ m) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v v (evenSAtShift D Sc cutoff i v f) m =
    independentSRightProduct D Sc cutoff i v
      (offDiagonalPolynomialBoundary D Sc cutoff p i v v f) m := by
  rw [independentSRightProduct_even_high D Sc cutoff i hi v _ m hm]
  simp only [evenSAtShift, LinearMap.sum_apply, LinearMap.comp_apply, Module.End.pow_apply,
    map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [offDiagonalPolynomialBoundary_independentS_postcomp]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, LinearMap.flip_apply]
  have hs := independentOutputS_support D Sc cutoff i v hn
  rw [Finset.mem_range] at hs
  have he : m = n + (m - n) := by omega
  rw [he, offDiagonalPolynomialBoundary_even_iterate_high D Sc cutoff p i hi]
  simp only [Nat.add_sub_cancel_left]

theorem evenLongShift_iterate_single (v t : List I) (n m : ℕ)
    (b : Old D Sc cutoff v t) :
    (evenLongShift D Sc cutoff v t)^[n] (Finsupp.single m b) =
      Finsupp.single (n + m) b := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.zero_add]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, evenLongShift_single]
    congr 1
    omega

private theorem evenPhi_oldComp_id (v : List I) (b : Old D Sc cutoff v v) :
    oldComp D Sc cutoff v v v ((ideal D Sc cutoff v v).mkQ (𝟙 _)) b = b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  rw [oldComp_mk, Category.id_comp]

theorem evenSAtShift_single_id (i : I) (v : List I) (d : ℕ) :
    evenSAtShift D Sc cutoff i v
      (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _))) =
    (evenLongShift D Sc cutoff v v)^[d] (independentOutputS D Sc cutoff i v) := by
  have hs :
      (evenLongShift D Sc cutoff v v)^[d] (independentOutputS D Sc cutoff i v) =
      ∑ n ∈ (independentOutputS D Sc cutoff i v).support,
        Finsupp.single (d + n) (independentOutputS D Sc cutoff i v n) := by
    conv_lhs => rw [← Finsupp.sum_single (independentOutputS D Sc cutoff i v)]
    rw [← Module.End.coe_pow, Finsupp.sum, map_sum]
    simp only [Module.End.pow_apply, evenLongShift_iterate_single]
  rw [hs]
  simp only [evenSAtShift, LinearMap.sum_apply, LinearMap.comp_apply, Module.End.pow_apply,
    evenLongShift_iterate_single, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    LinearMap.flip_apply, evenPhi_oldComp_id]
  apply Finset.sum_congr rfl
  intro n _
  rw [Nat.add_comm n d]

/-- The actual even diagonal row, evaluated on the full old identity class. -/
def evenBoundaryPhi (p : ZMod 2) (i : I) (v : List I) (d : ℕ) :
    ℕ →₀ Old D Sc cutoff v v :=
  offDiagonalPolynomialBoundary D Sc cutoff p i v v
    (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))

/-- High coefficients of S times the actual row are the ordered numerator coefficients. -/
theorem evenBoundaryPhi_S_high (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d m : ℕ) (hm : outputSDegree D i v ≤ m) :
    independentSRightProduct D Sc cutoff i v (evenBoundaryPhi D Sc cutoff p i v d) m =
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v)) m := by
  unfold evenBoundaryPhi
  rw [← offDiagonalPolynomialBoundary_even_S_high D Sc cutoff p i hi v _ m hm,
    evenSAtShift_single_id, offDiagonalPolynomialBoundary_even_independentS D Sc cutoff p i hi]

/-- The actual row vanishes above its prescribed bound, without a nonzero hypothesis. -/
theorem evenBoundaryPhi_above (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d m : ℕ)
    (hm : d + endpointQPDegree D cutoff i v < m + outputSDegree D i v) :
    evenBoundaryPhi D Sc cutoff p i v d m = 0 := by
  apply independentSRightProduct_even_detect_bound D Sc cutoff i hi v _
    (d + endpointQPDegree D cutoff i v) _ m hm
  intro n hn hN
  rw [evenBoundaryPhi_S_high D Sc cutoff p i hi v d n hn]
  exact appendC0_orderedReverseNumerator_above D Sc cutoff i v d n hN

/-- Its coefficient at the nonnegative-height bound is the prescribed scalar unit. -/
theorem evenBoundaryPhi_top (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v : List I) (d : ℕ) (hd : outputSDegree D i v ≤ d + endpointQPDegree D cutoff i v) :
    evenBoundaryPhi D Sc cutoff p i v d
      (d + endpointQPDegree D cutoff i v - outputSDegree D i v) =
    (appendQPProductUnit D Sc i v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  have ht := independentSRightProduct_even_top D Sc cutoff i hi v
    (evenBoundaryPhi D Sc cutoff p i v d)
    (d + endpointQPDegree D cutoff i v - outputSDegree D i v)
    (fun m hm => evenBoundaryPhi_above D Sc cutoff p i hi v d m (by omega))
  have he : d + endpointQPDegree D cutoff i v - outputSDegree D i v +
      outputSDegree D i v = d + endpointQPDegree D cutoff i v := by omega
  rw [he, evenBoundaryPhi_S_high D Sc cutoff p i hi v d _ hd,
    appendC0_orderedReverseNumerator_top] at ht
  exact ht.symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Even polynomial-boundary leading maps on arbitrary old Homs

The parity-zero arbitrary-Hom transport in DeformedBoundaryDivision (5).
Generic bare-long output transport is iterated through the literal moving
dot. Actual C0P factorization and output covariance identify each full old
coefficient row with the independently computed even diagonal Phi row.
The leading map is a scalar unit times balance twist on Old(v,t).
No diagonal-corner sufficiency or even categorical inverse is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenMoving_act (i : I) (hi : D.parity i = 0) (v w t : List I)
    (g : hom D Sc cutoff w t) (z : Target D Sc cutoff i v w) :
    movingPowerTarget D Sc cutoff i v t 1 (by simp [hi]) (act D Sc cutoff i g z) =
      act D Sc cutoff i g (movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]) z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change projection D Sc cutoff i v t (_ ≫ (_ ≫ _)) =
    projection D Sc cutoff i v t ((_ ≫ _) ≫ _)
  rw [Category.assoc]

theorem evenMoving_iterate_act (i : I) (hi : D.parity i = 0) (v w t : List I)
    (g : hom D Sc cutoff w t) (d : ℕ) (z : Target D Sc cutoff i v w) :
    (movingPowerTarget D Sc cutoff i v t 1 (by simp [hi]))^[d] (act D Sc cutoff i g z) =
      act D Sc cutoff i g ((movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]))^[d] z) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih, evenMoving_act D Sc cutoff i hi,
      Function.iterate_succ_apply']

theorem evenMoving_longSection_single_zero_iterate (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (d : ℕ) (c : Old D Sc cutoff v t) :
    (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]))^[d]
      (offDiagonalLongSection D Sc cutoff p i v t (Finsupp.single 0 c)) =
      offDiagonalLongSection D Sc cutoff p i v t (Finsupp.single d c) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih,
      evenMoving_offDiagonalLongSection D Sc cutoff p i hi, evenLongShift_single]

/-- The entire arbitrary-Hom row is the actual diagonal Phi row acting on its full coefficient. -/
theorem offDiagonalBoundary_even_rightAction (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (d : ℕ) (c : Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single d c) =
      offDiagonalCoefficientRightAction D Sc cutoff i 0 v v t
        (oldTwist D Sc cutoff (p + D.parity i * wordSumParity D v) v t c)
        (evenBoundaryPhi D Sc cutoff p i v d) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective c
  let g := twist k (p + D.parity i * wordSumParity D v) r
  let z := offDiagonalLongSection D Sc cutoff p i v v
    (Finsupp.single 0 ((ideal D Sc cutoff v v).mkQ (𝟙 _)))
  have hz : z = projection D Sc cutoff i v (v ++ [i]) (bareUFull D Sc cutoff i v) := by
    dsimp only [z]
    rw [offDiagonalLongSection_single_zero_pair, pair_id]
  have h0 := offDiagonalLongSection_zero_transport D Sc cutoff p i v t r
  rw [← ker_offDiagonalLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v t,
    LinearMap.mem_ker, map_sub, offDiagonalLongExtraction_section, sub_eq_zero] at h0
  have he0 : offDiagonalLongExtraction D Sc cutoff p i v t
      (act D Sc cutoff i (appendInsert D Sc cutoff i v t g) z) =
      Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ r) := by
    rw [hz]
    exact h0
  have he : offDiagonalLongExtraction D Sc cutoff p i v t
      (act D Sc cutoff i (appendInsert D Sc cutoff i v t g)
        (offDiagonalLongSection D Sc cutoff p i v v
          (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))) =
      Finsupp.single d ((ideal D Sc cutoff v t).mkQ r) := by
    rw [← evenMoving_longSection_single_zero_iterate D Sc cutoff p i hi v v d]
    rw [← evenMoving_iterate_act D Sc cutoff i hi,
      offDiagonalLongExtraction_evenMoving_iterate D Sc cutoff p i hi,
      he0, evenLongShift_iterate_single, Nat.add_zero]
  have hrow := congrArg (offDiagonalPolynomialBoundary D Sc cutoff p i v t) he
  have hphi := appendC0_pMap_offDiagonal D Sc cutoff p i v v
    (offDiagonalLongSection D Sc cutoff p i v v
      (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))
  rw [offDiagonalLongExtraction_section] at hphi
  change _ = evenBoundaryPhi D Sc cutoff p i v d at hphi
  have hg : (ideal D Sc cutoff v t).mkQ g =
      oldTwist D Sc cutoff (p + D.parity i * wordSumParity D v) v t
        ((ideal D Sc cutoff v t).mkQ r) := rfl
  have hcov := appendC0_postcomp_general D Sc cutoff i v v t g
    (pMap D Sc cutoff i v (v ++ [i])
      (offDiagonalLongSection D Sc cutoff p i v v
        (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))))
  rw [hg, hphi] at hcov
  calc
    offDiagonalPolynomialBoundary D Sc cutoff p i v t
        (Finsupp.single d ((ideal D Sc cutoff v t).mkQ r)) =
      appendC0 D Sc cutoff i v t
        (pMap D Sc cutoff i v (t ++ [i])
          (act D Sc cutoff i (appendInsert D Sc cutoff i v t g)
            (offDiagonalLongSection D Sc cutoff p i v v
              (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))))) :=
      hrow.symm.trans (appendC0_pMap_offDiagonal D Sc cutoff p i v t _).symm
    _ = _ := by
      rw [pMap_postcomp]
      exact hcov

private theorem evenHom_twist_zero (v t : List I) (c : Old D Sc cutoff v t) :
    oldTwist D Sc cutoff 0 v t c = c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective c
  change (ideal D Sc cutoff v t).mkQ (twist k 0 c) = _
  rw [twist_zero]

/-- Balance parity still twists the old coefficient even though the moving colour is even. -/
theorem offDiagonalBoundary_even_coefficient (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (d n : ℕ) (c : Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single d c) n =
      oldComp D Sc cutoff v v t (evenBoundaryPhi D Sc cutoff p i v d n)
        (oldTwist D Sc cutoff p v t c) := by
  rw [offDiagonalBoundary_even_rightAction D Sc cutoff p i hi,
    offDiagonalCoefficientRightAction_apply]
  simp only [hi, nsmul_zero, zero_mul, add_zero, evenHom_twist_zero]

/-- Scalar-unit balance twist is an equivalence on every old Hom, including empty ones. -/
def evenOffDiagonalBoundaryLeadingEquiv (p : ZMod 2) (i : I) (v t : List I) :
    Old D Sc cutoff v t ≃ₗ[k] Old D Sc cutoff v t :=
  (LinearEquiv.ofInvolutive (oldTwist D Sc cutoff p v t)
    (oldTwist_twice D Sc cutoff p v t)).trans
      (LinearEquiv.smulOfUnit (appendQPProductUnit D Sc i v))

theorem offDiagonalBoundary_even_above (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (d n : ℕ) (c : Old D Sc cutoff v t)
    (hn : d + endpointQPDegree D cutoff i v < n + outputSDegree D i v) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single d c) n = 0 := by
  rw [offDiagonalBoundary_even_coefficient D Sc cutoff p i hi,
    evenBoundaryPhi_above D Sc cutoff p i hi v d n hn, map_zero, LinearMap.zero_apply]

theorem offDiagonalBoundary_even_top (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (d n : ℕ) (c : Old D Sc cutoff v t)
    (hn : n + outputSDegree D i v = d + endpointQPDegree D cutoff i v) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single d c) n =
      evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t c := by
  have hp := evenBoundaryPhi_top D Sc cutoff p i hi v d (by omega)
  have he : d + endpointQPDegree D cutoff i v - outputSDegree D i v = n := by omega
  rw [he] at hp
  rw [offDiagonalBoundary_even_coefficient D Sc cutoff p i hi, hp]
  change oldComp D Sc cutoff v v t
      ((appendQPProductUnit D Sc i v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _))
      (oldTwist D Sc cutoff p v t c) =
    (appendQPProductUnit D Sc i v : k) • oldTwist D Sc cutoff p v t c
  rw [map_smul, LinearMap.smul_apply]
  congr 1
  obtain ⟨b, hb⟩ := (ideal D Sc cutoff v t).mkQ_surjective (oldTwist D Sc cutoff p v t c)
  rw [← hb, oldComp_mk, Category.id_comp]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Even boundary division on arbitrary old Homs

DeformedBoundaryDivision (5), moving parity zero: the existing polynomial
boundary itself has the proved unit leading maps in its ordinary coefficient
coordinates. The module-valued degree-shift division theorem gives exact
kernel support and unique quotient/remainder windows. No corrected-coordinate
basis change or categorical crossing inverse is assumed.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Exact low kernel of the even boundary in ordinary source coordinates. -/
theorem offDiagonalPolynomialBoundary_even_eq_zero_iff (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t f = 0 ↔
      ∀ d ∈ f.support, d + endpointQPDegree D cutoff i v < outputSDegree D i v :=
  OddMath.Algebra.DegreeShiftRow.eq_zero_iff
    (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
    (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)
    (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
    (offDiagonalBoundary_even_top D Sc cutoff p i hi v t) f

/-- Even nonnegative-height polynomial boundary injection. -/
theorem offDiagonalPolynomialBoundary_even_injective (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I)
    (h : outputSDegree D i v ≤ endpointQPDegree D cutoff i v) :
    Function.Injective (offDiagonalPolynomialBoundary D Sc cutoff p i v t) :=
  OddMath.Algebra.DegreeShiftRow.injective
    (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
    (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)
    (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
    (offDiagonalBoundary_even_top D Sc cutoff p i hi v t) h

/-- Even nonpositive-height polynomial boundary surjection. -/
theorem offDiagonalPolynomialBoundary_even_surjective (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I)
    (h : endpointQPDegree D cutoff i v ≤ outputSDegree D i v) :
    Function.Surjective (offDiagonalPolynomialBoundary D Sc cutoff p i v t) :=
  OddMath.Algebra.DegreeShiftRow.surjective
    (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
    (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)
    (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
    (offDiagonalBoundary_even_top D Sc cutoff p i hi v t) h

/-- Allowed quotient coefficients outside the low kernel. -/
abbrev evenBoundaryRowHigh (i : I) (v t : List I) :=
  OddMath.Algebra.DegreeShiftRow.high (k := k) (M := Old D Sc cutoff v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)

/-- Literal output window below the nonnegative height. -/
abbrev evenBoundaryRowWindow (i : I) (v t : List I) :=
  OddMath.Algebra.DegreeShiftRow.window (k := k) (M := Old D Sc cutoff v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)

/-- Unique even boundary-row division on arbitrary old Hom coefficients. -/
def evenBoundaryRowDivisionEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) :
    (evenBoundaryRowHigh D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  OddMath.Algebra.DegreeShiftRow.divisionEquiv
    (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
    (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)
    (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
    (offDiagonalBoundary_even_top D Sc cutoff p i hi v t)

@[simp] theorem evenBoundaryRowDivisionEquiv_apply (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I)
    (x : evenBoundaryRowHigh D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) :
    evenBoundaryRowDivisionEquiv D Sc cutoff p i hi v t x =
      offDiagonalPolynomialBoundary D Sc cutoff p i v t x.1 + x.2 := rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Even crossing height consequences

The parity-zero polynomial division in DeformedBoundaryDivision (5) gives
injectivity or surjectivity of the prescribed balanced crossing in the two
height ranges of DeformedRouquierMatrix, section 4. The same generic snake
comparison identifies its kernel with the even polynomial boundary kernel.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenToCyclotomic_injective_of_nonnegative_height (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : outputSDegree D j v ≤ endpointQPDegree D cutoff j v) :
    Function.Injective (toCyclotomic D Sc cutoff j v t) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j v t z
  have hy : shortCross D Sc cutoff j v t y ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
    rw [LinearMap.mem_ker]
    have he := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t) y
    exact he.trans hz
  rw [ker_canonicalAppendTarget] at hy
  obtain ⟨x, hx⟩ := hy
  have hc : appendC0 D Sc cutoff j v t (shortCross D Sc cutoff j v t y) = 0 := by
    have hm : shortCross D Sc cutoff j v t y ∈
        appendCrossingSpan D Sc cutoff j v t := by
      rw [← ShortCrossCoordinates.range_shortCross]
      exact ⟨y, rfl⟩
    rw [← appendC0_ker, LinearMap.mem_ker] at hm
    exact hm
  have hb : offDiagonalLongExtraction D Sc cutoff p j v t x = 0 := by
    apply offDiagonalPolynomialBoundary_even_injective D Sc cutoff p j hj v t h
    rw [map_zero, ← appendC0_pMap_offDiagonal, hx]
    exact hc
  have hm : x ∈ LinearMap.range (alpha D Sc cutoff j v t) := by
    rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff p j v t,
      LinearMap.mem_ker]
    exact hb
  obtain ⟨a, ha⟩ := hm
  have he : pprime D Sc cutoff j v t a = y := by
    apply ShortCrossCoordinates.shortCross_injective D Sc cutoff j v t
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j v t) a
    simp only [LinearMap.comp_apply] at hs
    exact hs.symm.trans (by rw [ha]; exact hx)
  have hq : pprime D Sc cutoff j v t a ∈ LinearMap.ker (q D Sc cutoff j v t) := by
    rw [← range_pprime_eq_ker_q]
    exact ⟨a, rfl⟩
  rw [LinearMap.mem_ker, he] at hq
  exact hq

theorem evenToCyclotomic_surjective_of_nonpositive_height (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : endpointQPDegree D cutoff j v ≤ outputSDegree D j v) :
    Function.Surjective (toCyclotomic D Sc cutoff j v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff j v (t ++ [j]) n
  obtain ⟨f, hf⟩ := offDiagonalPolynomialBoundary_even_surjective D Sc cutoff p j hj v t h
    (appendC0 D Sc cutoff j v t z)
  let x := offDiagonalSourceLongSection D Sc cutoff p j v t f
  have hc : z - pMap D Sc cutoff j v (t ++ [j]) x ∈
      appendCrossingSpan D Sc cutoff j v t := by
    dsimp only [x]
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, appendC0_pMap_offDiagonal,
      offDiagonalLongExtraction_sourceLongSection, hf]
    exact sub_self _
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨q D Sc cutoff j v t y, ?_⟩
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub]
  have hx : pMap D Sc cutoff j v (t ++ [j]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx, sub_zero]

/-- At height zero the prescribed crossing itself is an equivalence. -/
def evenToCyclotomicEquiv_zero_height (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : endpointQPDegree D cutoff j v = outputSDegree D j v) :
    Source D Sc cutoff j v t ≃ₗ[k] Old D Sc cutoff (v ++ [j]) (t ++ [j]) :=
  LinearEquiv.ofBijective (toCyclotomic D Sc cutoff j v t)
    ⟨evenToCyclotomic_injective_of_nonnegative_height D Sc cutoff p j hj v t h.ge,
      evenToCyclotomic_surjective_of_nonpositive_height D Sc cutoff p j hj v t h.le⟩

@[simp] theorem evenToCyclotomicEquiv_zero_height_apply (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : endpointQPDegree D cutoff j v = outputSDegree D j v)
    (z : Source D Sc cutoff j v t) :
    evenToCyclotomicEquiv_zero_height D Sc cutoff p j hj v t h z =
      toCyclotomic D Sc cutoff j v t z := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # The even low window and the crossing kernel

The negative-height kernel identification in DeformedRouquierMatrix, section4,
uses the ordinary even polynomial coefficients. The actual generic snake map
carries precisely that low window onto the balanced crossing kernel.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The literal even low-source polynomial window. -/
def evenBoundaryKernelWindow (i : I) (v t : List I) : Submodule k (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.supported (Old D Sc cutoff v t) k
    {d | d + endpointQPDegree D cutoff i v < outputSDegree D i v}

/-- Ordinary coefficient inclusion identifies exactly the even boundary kernel. -/
def evenBoundaryKernelEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v t : List I) :
    evenBoundaryKernelWindow D Sc cutoff i v t ≃ₗ[k]
      LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p i v t) :=
  LinearEquiv.ofBijective
    ((evenBoundaryKernelWindow D Sc cutoff i v t).subtype.codRestrict _ (by
      intro f
      exact (offDiagonalPolynomialBoundary_even_eq_zero_iff D Sc cutoff p i hi v t f).mpr
        (fun d hd => f.property hd))) (by
    constructor
    · intro f g hfg
      apply Subtype.ext
      exact congrArg (fun z : LinearMap.ker
        (offDiagonalPolynomialBoundary D Sc cutoff p i v t) => z.val) hfg
    · intro f
      refine ⟨⟨f.val, ?_⟩, Subtype.ext rfl⟩
      intro d hd
      exact (offDiagonalPolynomialBoundary_even_eq_zero_iff D Sc cutoff p i hi v t f.val).mp
        (LinearMap.mem_ker.mp f.property) d hd)

@[simp] theorem evenBoundaryKernelEquiv_apply (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : evenBoundaryKernelWindow D Sc cutoff i v t) :
    (evenBoundaryKernelEquiv D Sc cutoff p i hi v t f).val = f.val := rfl

/-- The low polynomial coordinates are exactly the kernel of the prescribed crossing. -/
def evenCrossingKernelEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v t : List I) :
    evenBoundaryKernelWindow D Sc cutoff i v t ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff i v t) :=
  (evenBoundaryKernelEquiv D Sc cutoff p i hi v t).trans
    (offDiagonalBoundarySnakeKernelEquiv D Sc cutoff p i v t)

@[simp] theorem evenCrossingKernelEquiv_apply (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : evenBoundaryKernelWindow D Sc cutoff i v t) :
    (evenCrossingKernelEquiv D Sc cutoff p i hi v t f).val =
      offDiagonalBoundarySnake D Sc cutoff p i v t
        (evenBoundaryKernelEquiv D Sc cutoff p i hi v t f) := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Even positive-height crossing and polynomial columns

The nonnegative-height branch of DeformedRouquierMatrix, section 4, uses
the prescribed balanced crossing plus literal low polynomial columns.
The actual even degree-shift division and separation prove its inverse on
arbitrary old Hom endpoints, without repeating coefficient elimination.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def evenPositiveCrossingAssembly (i : I) (v t : List I) :
    (Source D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) →ₗ[k]
      Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (toCyclotomic D Sc cutoff i v t).comp (LinearMap.fst k _ _) +
    (canonicalAppendTarget D Sc cutoff i v (t ++ [i])).comp
      ((appendOutputEmbedding D Sc cutoff i v t).comp
        ((evenBoundaryRowWindow D Sc cutoff i v t).subtype.comp (LinearMap.snd k _ _)))

@[simp] theorem evenPositiveCrossingAssembly_apply (i : I)
    (v t : List I) (s : Source D Sc cutoff i v t)
    (r : evenBoundaryRowWindow D Sc cutoff i v t) :
    evenPositiveCrossingAssembly D Sc cutoff i v t (s, r) =
      toCyclotomic D Sc cutoff i v t s +
        canonicalAppendTarget D Sc cutoff i v (t ++ [i])
          (appendOutputEmbedding D Sc cutoff i v t r) := rfl

theorem evenPositiveCrossingAssembly_injective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I)
    (h : outputSDegree D i v ≤ endpointQPDegree D cutoff i v) :
    Function.Injective (evenPositiveCrossingAssembly D Sc cutoff i v t) := by
  suffices hzero : ∀ z, evenPositiveCrossingAssembly D Sc cutoff i v t z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    have hs : evenPositiveCrossingAssembly D Sc cutoff i v t (x - y) = evenPositiveCrossingAssembly D Sc cutoff i v t x - evenPositiveCrossingAssembly D Sc cutoff i v t y :=
      map_sub (evenPositiveCrossingAssembly D Sc cutoff i v t) x y
    exact hs.trans (sub_eq_zero.mpr hxy)
  rintro ⟨s, r⟩ hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff i v t s
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff i v t) y
  simp only [LinearMap.comp_apply] at hs
  have hm : shortCross D Sc cutoff i v t y + appendOutputEmbedding D Sc cutoff i v t r ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [i])) := by
    rw [LinearMap.mem_ker, map_add, hs]
    exact hz
  rw [ker_canonicalAppendTarget] at hm
  obtain ⟨x, hx⟩ := hm
  have hc : appendC0 D Sc cutoff i v t (shortCross D Sc cutoff i v t y) = 0 := by
    apply appendCrossingSpan_le_ker D Sc cutoff i v t
    rw [← ShortCrossCoordinates.range_shortCross]
    exact ⟨y, rfl⟩
  have hb : offDiagonalPolynomialBoundary D Sc cutoff p i v t
      (offDiagonalLongExtraction D Sc cutoff p i v t x) = r := by
    rw [← appendC0_pMap_offDiagonal D Sc cutoff p i v t, hx, map_add, hc, appendC0_embedding, zero_add]
  have hr : r = 0 := by
    have hzrow : offDiagonalPolynomialBoundary D Sc cutoff p i v t
        (offDiagonalLongExtraction D Sc cutoff p i v t x) + -(r.val) = 0 := by
      rw [hb, add_neg_cancel]
    have hh := OddMath.Algebra.DegreeShiftRow.separation
      (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
      (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
      (outputSDegree D i v) (endpointQPDegree D cutoff i v)
      (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
      (offDiagonalBoundary_even_top D Sc cutoff p i hi v t)
      (offDiagonalLongExtraction D Sc cutoff p i v t x) (-r.val)
      (fun d _ => by omega)
      (fun n hn => by
        apply r.property
        change n ∈ r.val.support
        simpa only [Finsupp.support_neg] using hn) hzrow
    exact Subtype.ext (neg_eq_zero.mp hh.2)
  apply Prod.ext
  · change q D Sc cutoff i v t y = 0
    apply evenToCyclotomic_injective_of_nonnegative_height D Sc cutoff p i hi v t h
    have hz' : toCyclotomic D Sc cutoff i v t (q D Sc cutoff i v t y) = 0 := by
      simpa only [evenPositiveCrossingAssembly_apply, hr, ZeroMemClass.coe_zero, map_zero, add_zero] using hz
    exact hz'.trans ((toCyclotomic D Sc cutoff i v t).map_zero.symm)
  · exact hr

theorem evenPositiveCrossingAssembly_surjective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I)
    :
    Function.Surjective (evenPositiveCrossingAssembly D Sc cutoff i v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff i v (t ++ [i]) n
  let row := (evenBoundaryRowDivisionEquiv D Sc cutoff p i hi v t).symm
    (appendC0 D Sc cutoff i v t z)
  let f := row.1.val
  let r := row.2
  have hfr : offDiagonalPolynomialBoundary D Sc cutoff p i v t f + r.val =
      appendC0 D Sc cutoff i v t z := by
    exact (evenBoundaryRowDivisionEquiv D Sc cutoff p i hi v t).apply_symm_apply _
  let x := offDiagonalSourceLongSection D Sc cutoff p i v t f
  have hc : z - pMap D Sc cutoff i v (t ++ [i]) x -
      appendOutputEmbedding D Sc cutoff i v t r ∈ appendCrossingSpan D Sc cutoff i v t := by
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, map_sub, appendC0_pMap_offDiagonal,
      appendC0_embedding]
    dsimp only [x]
    rw [offDiagonalLongExtraction_sourceLongSection, ← hfr]
    abel
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨(q D Sc cutoff i v t y, r), ?_⟩
  rw [evenPositiveCrossingAssembly_apply]
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff i v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub, map_sub]
  have hx : pMap D Sc cutoff i v (t ++ [i]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [i])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx]
  abel

/-- The literal crossing and low polynomial columns form the positive branch. -/
def evenPositiveCrossingEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (h : outputSDegree D i v ≤ endpointQPDegree D cutoff i v) :
    (Source D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  LinearEquiv.ofBijective (evenPositiveCrossingAssembly D Sc cutoff i v t)
    ⟨evenPositiveCrossingAssembly_injective D Sc cutoff p i hi v t h,
      evenPositiveCrossingAssembly_surjective D Sc cutoff p i hi v t⟩

/-- The polynomial complement is literally the coefficient window below the height. -/
theorem evenBoundaryRowWindow_eq_height (i : I) (v t : List I) (a : ℕ)
    (ha : endpointQPDegree D cutoff i v = outputSDegree D i v + a) :
    evenBoundaryRowWindow D Sc cutoff i v t =
      Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio a) := by
  unfold evenBoundaryRowWindow OddMath.Algebra.DegreeShiftRow.window
  congr 1
  ext n
  change (n + outputSDegree D i v < endpointQPDegree D cutoff i v) ↔ n < a
  omega

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Even ordinary-source unit-column inverse
The positive profile of DeformedMatrixComparison §4 uses the canonical
even source, ordinary adjunction unit/dot columns, and signed crossing.
The ordered categorical mate identity remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- For even colours the ordinary columns require no scalar normalization. -/
def evenUnitDotPolynomialMap (i : {i : I // D.parity i = 0}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) :=
  Finsupp.lsum k fun n => inductionUnitDotColumn D Sc cutoff i.1 v t n

@[simp] theorem evenUnitDotPolynomialMap_single (i : {i : I // D.parity i = 0})
    (v t : List I) (n : ℕ) (b : Old D Sc cutoff v t) :
    evenUnitDotPolynomialMap D Sc cutoff i v t (Finsupp.single n b) =
      inductionUnitDotColumn D Sc cutoff i.1 v t n b := by
  rw [evenUnitDotPolynomialMap, Finsupp.lsum_single]

theorem evenUnitDotPolynomialMap_eq (i : {i : I // D.parity i = 0}) (v t : List I) :
    evenUnitDotPolynomialMap D Sc cutoff i v t = unitDotPolynomialMap D Sc cutoff i.1 v t := by
  unfold evenUnitDotPolynomialMap unitDotPolynomialMap
  congr 1
  funext n
  simp only [inductionUnitDotSign, i.property, smul_zero, sign_zero, one_smul]

def evenUnitPositiveMatrixEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (h : outputSDegree D i.1 v ≤ endpointQPDegree D cutoff i.1 v) :
    ((((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)) × evenBoundaryRowWindow D Sc cutoff i.1 v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) :=
  (((evenSourceEquiv D Sc cutoff i v t).trans (LinearEquiv.neg k)).prodCongr
    (LinearEquiv.refl k (evenBoundaryRowWindow D Sc cutoff i.1 v t))).trans
      (evenPositiveCrossingEquiv D Sc cutoff p i.1 i.property v t h)

/-- The positive columns are the literal ordinary unit/dot columns. -/
theorem evenUnitPositiveMatrixEquiv_apply (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (h : outputSDegree D i.1 v ≤ endpointQPDegree D cutoff i.1 v)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)))
    (r : evenBoundaryRowWindow D Sc cutoff i.1 v t) :
    evenUnitPositiveMatrixEquiv D Sc cutoff p i v t h (z, r) =
      -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) +
        evenUnitDotPolynomialMap D Sc cutoff i v t r.val := by
  change toCyclotomic D Sc cutoff i.1 v t (-(evenSourceEquiv D Sc cutoff i v t z)) +
    canonicalAppendTarget D Sc cutoff i.1 v (t ++ [i.1])
      (appendOutputEmbedding D Sc cutoff i.1 v t r.val) = _
  rw [map_neg, evenUnitDotPolynomialMap_eq, unitDotPolynomialMap_eq]
  rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Even shifted unit-family component coordinates
DeformedMatrixComparison (6) and the positive profile of section 4
specialize to identity coefficient units for an even moving colour.
The actual ordered-mate comparison remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.LowPolynomialCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance evenUnitFamilyPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Even ordinary columns require the identity coefficient diagonal. -/
theorem unitCoefficientDiagonal_even (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ) (b : Fin m → Old D Sc cutoff v t) :
    unitCoefficientDiagonal D Sc cutoff (D.parity i.1) v t m b = b := by
  ext r
  simp only [unitCoefficientDiagonal_apply, inductionUnitDotSign, i.property,
    smul_zero, sign_zero, one_smul]

/-- The literal even polynomial window in finite coordinates. -/
def evenUnitWindowVectorEquiv (i : I) (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i v = outputSDegree D i v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] evenBoundaryRowWindow D Sc cutoff i v t :=
  (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).trans
    (LinearEquiv.ofEq _ _ (evenBoundaryRowWindow_eq_height D Sc cutoff i v t m hm).symm)

/-- Canonical parity coordinates and the literal even coefficient window. -/
def evenUnitFamilyComponentCoordinates (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    ((((BalancedInduction.induction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × evenBoundaryRowWindow D Sc cutoff i.1 v t) :=
  (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m).trans
    ((LinearEquiv.refl k _).prodCongr
      (evenUnitWindowVectorEquiv D Sc cutoff i.1 v t m hm))

/-- The even shifted-family component inverse, with unscaled ordinary unit columns. -/
def evenUnitFamilyComponentEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) :=
  (evenUnitFamilyComponentCoordinates D Sc cutoff i v t m hm).trans
    (evenUnitPositiveMatrixEquiv D Sc cutoff p i v t (by omega))

/-- Every even unit slot is the ordinary adjunction-unit/dot column. -/
theorem evenUnitFamilyComponentEquiv_apply (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m)
    (x : (a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    evenUnitFamilyComponentEquiv D Sc cutoff p i v t m hm x =
      -toCyclotomic D Sc cutoff i.1 v t
        (evenSourceEquiv D Sc cutoff i v t
          (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1) +
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff i.1 v t r.val
        ((unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2 r) := by
  rw [evenUnitFamilyComponentEquiv, LinearEquiv.trans_apply]
  rw [show (evenUnitFamilyComponentCoordinates D Sc cutoff i v t m hm x) =
      ((unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1,
        evenUnitWindowVectorEquiv D Sc cutoff i.1 v t m hm
          (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2) from rfl]
  have he := evenUnitPositiveMatrixEquiv_apply D Sc cutoff p i v t (by omega)
    (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1
    (evenUnitWindowVectorEquiv D Sc cutoff i.1 v t m hm
      (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2)
  refine he.trans ?_
  congr 1
  rw [evenUnitDotPolynomialMap_eq]
  change unitDotPolynomialMap D Sc cutoff i.1 v t
    ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m
      (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2).val) = _
  have h := unitDotPolynomialMap_diagonal D Sc cutoff i.1 v t m
    (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2
  rw [unitCoefficientDiagonal_even D Sc cutoff i] at h
  exact h

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Even input contraction and dot on the cyclotomic source

The parity-zero input operators in DeformedMatrixComparison, section 3.
The ordinary moving dot preserves the long-extraction kernel. Consequently
the specified input defect and decoded dot descend through the prescribed
Pprime relations to Source, retaining every old coefficient.
The actual coefficient(0) module/counit attachment is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenInputDefect_pMap_alpha (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff i v t) :
    appendC0InputDefect D Sc cutoff i v t
      (pMap D Sc cutoff i v (t ++ [i])
        (CyclotomicCrossingTensor.alpha D Sc cutoff i v t a)) = 0 := by
  have h0 : appendC0 D Sc cutoff i v t
      (pMap D Sc cutoff i v (t ++ [i])
        (CyclotomicCrossingTensor.alpha D Sc cutoff i v t a)) = 0 := by
    rw [appendC0_pMap_offDiagonal D Sc cutoff p i v t,
      CyclotomicCrossingTensor.offDiagonalLongExtraction_alpha, map_zero]
  have h1 : appendC0 D Sc cutoff i v t
      (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
        (pMap D Sc cutoff i v (t ++ [i])
          (CyclotomicCrossingTensor.alpha D Sc cutoff i v t a))) = 0 := by
    rw [← pMap_movingEvenDot D Sc cutoff i hi,
      appendC0_pMap_offDiagonal D Sc cutoff p i v t,
      offDiagonalLongExtraction_evenMoving D Sc cutoff p i hi,
      CyclotomicCrossingTensor.offDiagonalLongExtraction_alpha, map_zero, map_zero]
  simp only [appendC0InputDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    h0, h1, map_zero, sub_self]

theorem evenInputDefect_shortCross_pprime (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff i v t) :
    appendC0InputDefect D Sc cutoff i v t
      (CyclotomicCrossingTensor.shortCross D Sc cutoff i v t
        (CyclotomicCrossingTensor.pprime D Sc cutoff i v t a)) = 0 := by
  have hs := LinearMap.congr_fun (CyclotomicCrossingTensor.shortColumn_square D Sc cutoff i v t) a
  simp only [LinearMap.comp_apply] at hs
  rw [← hs]
  exact evenInputDefect_pMap_alpha D Sc cutoff p i hi v t a

namespace CyclotomicCrossingTensor

/-- The prescribed polynomial-constant defect on affine short coordinates. -/
def evenInputContractionAffine (i : I) (v t : List I) :
    ShortTarget D Sc cutoff i v t →ₗ[k] Old D Sc cutoff v t where
  toFun z := appendC0InputDefect D Sc cutoff i v t (shortCross D Sc cutoff i v t z) 0
  map_add' a b := by simp only [map_add, Finsupp.add_apply]
  map_smul' a b := by simp only [map_smul, Finsupp.smul_apply, RingHom.id_apply]

theorem evenInputContractionAffine_ker_q (i : I) (hi : D.parity i = 0) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i v t) ≤
      LinearMap.ker (evenInputContractionAffine D Sc cutoff i v t) := by
  rw [← range_pprime_eq_ker_q]
  rintro z ⟨a, rfl⟩
  change appendC0InputDefect D Sc cutoff i v t
    (shortCross D Sc cutoff i v t (pprime D Sc cutoff i v t a)) 0 = 0
  rw [evenInputDefect_shortCross_pprime D Sc cutoff 0 i hi v t, Finsupp.zero_apply]

/-- The raw even cap row on the original source; its representative is minus composition. -/
def evenInputContraction (i : I) (hi : D.parity i = 0) (v t : List I) :
    Source D Sc cutoff i v t →ₗ[k] Old D Sc cutoff v t :=
  ((LinearMap.ker (q D Sc cutoff i v t)).liftQ
    (evenInputContractionAffine D Sc cutoff i v t)
    (evenInputContractionAffine_ker_q D Sc cutoff i hi v t)).comp
      ((q D Sc cutoff i v t).quotKerEquivOfSurjective
        (q_surjective D Sc cutoff i v t)).symm.toLinearMap

@[simp] theorem evenInputContraction_q (i : I) (hi : D.parity i = 0) (v t : List I)
    (z : ShortTarget D Sc cutoff i v t) :
    evenInputContraction D Sc cutoff i hi v t (q D Sc cutoff i v t z) =
      evenInputContractionAffine D Sc cutoff i v t z := by
  simp only [evenInputContraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The input dot is the decoded ordinary append moving dot. -/
def evenCrossingInputDotAffine (i : I) (v t : List I) :
    ShortTarget D Sc cutoff i v t →ₗ[k] ShortTarget D Sc cutoff i v t :=
  ShortCrossCoordinates.decode D Sc cutoff i v t ∘ₗ
    appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1 ∘ₗ
      shortCross D Sc cutoff i v t

theorem evenCrossingInputDotAffine_pprime (i : I) (hi : D.parity i = 0) (v t : List I)
    (a : PprimeDomain D Sc cutoff i v t) :
    evenCrossingInputDotAffine D Sc cutoff i v t (pprime D Sc cutoff i v t a) ∈
      LinearMap.range (pprime D Sc cutoff i v t) := by
  have hz : movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
      (alpha D Sc cutoff i v t a) ∈ LinearMap.range (alpha D Sc cutoff i v t) := by
    rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff 0 i v t,
      LinearMap.mem_ker, offDiagonalLongExtraction_evenMoving D Sc cutoff 0 i hi,
      offDiagonalLongExtraction_alpha, map_zero]
  obtain ⟨a', ha'⟩ := hz
  refine ⟨a', ?_⟩
  change pprime D Sc cutoff i v t a' =
    ShortCrossCoordinates.decode D Sc cutoff i v t
      (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
        (shortCross D Sc cutoff i v t (pprime D Sc cutoff i v t a)))
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff i v t) a
  have hs' := LinearMap.congr_fun (shortColumn_square D Sc cutoff i v t) a'
  simp only [LinearMap.comp_apply] at hs hs'
  rw [← hs, ← pMap_movingEvenDot D Sc cutoff i hi, ← ha', hs',
    ShortCrossCoordinates.decode_shortCross]

theorem evenCrossingInputDotAffine_ker_q (i : I) (hi : D.parity i = 0) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i v t) ≤
      (LinearMap.ker (q D Sc cutoff i v t)).comap
        (evenCrossingInputDotAffine D Sc cutoff i v t) := by
  intro z hz
  rw [← range_pprime_eq_ker_q] at hz
  obtain ⟨a, rfl⟩ := hz
  change evenCrossingInputDotAffine D Sc cutoff i v t (pprime D Sc cutoff i v t a) ∈
    LinearMap.ker (q D Sc cutoff i v t)
  rw [← range_pprime_eq_ker_q]
  exact evenCrossingInputDotAffine_pprime D Sc cutoff i hi v t a

def evenCrossingInputDot (i : I) (hi : D.parity i = 0) (v t : List I) :
    Source D Sc cutoff i v t →ₗ[k] Source D Sc cutoff i v t :=
  let e := (q D Sc cutoff i v t).quotKerEquivOfSurjective (q_surjective D Sc cutoff i v t)
  e.toLinearMap ∘ₗ
    (LinearMap.ker (q D Sc cutoff i v t)).mapQ
      (LinearMap.ker (q D Sc cutoff i v t)) (evenCrossingInputDotAffine D Sc cutoff i v t)
      (evenCrossingInputDotAffine_ker_q D Sc cutoff i hi v t) ∘ₗ e.symm.toLinearMap

@[simp] theorem evenCrossingInputDot_q (i : I) (hi : D.parity i = 0) (v t : List I)
    (z : ShortTarget D Sc cutoff i v t) :
    evenCrossingInputDot D Sc cutoff i hi v t (q D Sc cutoff i v t z) =
      q D Sc cutoff i v t (evenCrossingInputDotAffine D Sc cutoff i v t z) := by
  simp only [evenCrossingInputDot, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.mapQ_apply,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem evenCrossingInputDotAffine_representative (i : I) (hi : D.parity i = 0)
    (v s t : List I) (r : hom D Sc cutoff v (s ++ [i]))
    (g : hom D Sc cutoff (s ++ [i]) t) :
    evenCrossingInputDotAffine D Sc cutoff i v t
      (shortTensor D Sc cutoff i v s t g ((ideal D Sc cutoff v (s ++ [i])).mkQ r)) =
      shortTensor D Sc cutoff i v s t
        (appendMovingPower D Sc cutoff i s 1 ≫ g) ((ideal D Sc cutoff v (s ++ [i])).mkQ r) := by
  change ShortCrossCoordinates.decode D Sc cutoff i v t
    (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (shortCross D Sc cutoff i v t
        (shortTensor D Sc cutoff i v s t g ((ideal D Sc cutoff _ _).mkQ r)))) = _
  rw [ShortCrossCoordinates.column_mk, appendMovingPowerTarget_crossing_one]
  simp only [map_sub, map_smul, ShortCrossCoordinates.decode_embedding, smul_zero, sub_zero]
  rw [← ShortCrossCoordinates.column_mk, ShortCrossCoordinates.decode_shortCross]
  simp only [hi, zero_mul, SKM.zsign_zero, one_smul, twist_zero]

theorem evenCrossingInputDot_iterate_q (i : I) (hi : D.parity i = 0) (v t : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff i v t) :
    (evenCrossingInputDot D Sc cutoff i hi v t)^[r] (q D Sc cutoff i v t z) =
      q D Sc cutoff i v t ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r] z) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, evenCrossingInputDot_q, Function.iterate_succ_apply']

theorem evenInputContraction_iterate_q (i : I) (hi : D.parity i = 0) (v t : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff i v t) :
    evenInputContraction D Sc cutoff i hi v t
      ((evenCrossingInputDot D Sc cutoff i hi v t)^[r] (q D Sc cutoff i v t z)) =
      evenInputContractionAffine D Sc cutoff i v t ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r] z) := by
  rw [evenCrossingInputDot_iterate_q, evenInputContraction_q]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
end

end
