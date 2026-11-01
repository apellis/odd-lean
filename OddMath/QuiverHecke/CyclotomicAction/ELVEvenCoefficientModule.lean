import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVQuotientInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations

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
