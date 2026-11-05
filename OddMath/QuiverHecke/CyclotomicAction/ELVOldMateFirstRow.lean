import OddMath.QuiverHecke.CyclotomicAction.ELVOldMateEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVOldInductionRepresentable
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCapComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVActualCapParity
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedSourceLinearEquiv

/-! # The actual odd mate is the normalized first crossing row

The fixed shiftedSourceParityIso twists the entire first tensor factor.
Co-Yoneda evaluation of the actual signed mate is minus toCyclotomic after
this canonical source isomorphism, on every vector and arbitrary endpoints.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem coend_total_ext
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M N : Superfunctor k C (SVec k)) (f : BalancedInduction.induced A M ⟶ N)
    (t : C) {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (e : N.obj t →ₗ[k] V) (r : W →ₗ[k] V)
    (J : BalancedInduction.Obj A M.toFunctor t →ₗ[k] W)
    (h : ∀ s (g : A.obj s ⟶ t) (b : M.obj s),
      e (f.total t (BalancedInduction.tensor A M.toFunctor s g b)) =
      -r (J (BalancedInduction.tensor A M.toFunctor s g b)))
    (z : BalancedInduction.Obj A M.toFunctor t) : e (f.total t z) = -r (J z) := by
  have hm : e.comp (SVec.toLinearMap (f.total t)) = -(r.comp J) := by
    apply BalancedInduction.hom_ext
    intro s g b
    change e (f.total t (BalancedInduction.tensor A M.toFunctor s g b)) =
      -r (J (BalancedInduction.tensor A M.toFunctor s g b))
    exact h s g b
  exact LinearMap.congr_fun hm z

private theorem parityCoefficientMap_one (i : I) (v : List I)
    (s : OldCategory D Sc cutoff)
    (b : ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj s) :
    (parityCoefficientMap D Sc cutoff i v).app 1 s b = b := by
  rw [parityCoefficientMap, Superfunctor.comp_app]
  simp only [coefficientModuleBackward_app, one_ne_zero, ↓reduceIte,
    SVec.zmod2_one_add_one, CategoryTheory.Limits.comp_zero, zero_add]
  rfl

theorem shiftedSourceParityIso_hom_total_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    (shiftedSourceParityIso D Sc cutoff i v).hom.total
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
    BalancedInduction.tensor (append D Sc cutoff i)
      (coefficientOneModule D Sc cutoff i v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff)
      (twist k 1 (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g) b := by
  rw [shiftedSourceParityIso_hom_eq_induction_map]
  change (BalancedInduction.moduleMap (append D Sc cutoff i)
    (parityCoefficientMap D Sc cutoff i v)).total _ _ = _
  rw [BalancedInduction.moduleMap_total_tensor]
  rw [Superfunctor.app_eq_zero_of_mem (parityCoefficientMap_mem D Sc cutoff i v)
    (show (0 : ZMod 2) ≠ 1 by decide)]
  simp only [SVec.zero_apply]
  rw [BalancedInduction.tensor_zero_right (append D Sc cutoff i)
    (coefficientOneModule D Sc cutoff i v).toFunctor
    (⟨s⟩ : OldCategory D Sc cutoff) g, zero_add,
    parityCoefficientMap_one D Sc cutoff i v (⟨s⟩ : OldCategory D Sc cutoff) b]

theorem shiftedSourceCanonicalEquiv_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    shiftedSourceCanonicalEquiv D Sc cutoff j v t
      (BalancedInduction.tensor (append D Sc cutoff j.1)
        ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
    tensor D Sc cutoff j.1 v s t (oldTwist D Sc cutoff 1 (s ++ [j.1]) t g) b := by
  rw [shiftedSourceCanonicalEquiv_apply, shiftedSourceParityIso_hom_total_tensor,
    coefficientOneSourceEquiv_tensor]
  rw [oldCategory_twist]
  rfl

theorem pairing_eq_append_comp (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    pairing D Sc cutoff i v s t g b =
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) b ≫
      equalCrossComponent D Sc cutoff i (⟨s⟩ : OldCategory D Sc cutoff) ≫
      (append D Sc cutoff i).map (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff (s ++ [i]) t).mkQ_surjective g
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  rfl

theorem oldModuleMate_upper_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff i
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) =
    -((append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) b ≫
      equalCrossComponent D Sc cutoff i (⟨s⟩ : OldCategory D Sc cutoff) ≫
      twist k (D.parity i * D.parity i)
        ((append D Sc cutoff i).map
          (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
          (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g)) := by
  rw [oldModuleMate_total_tensor, map_neg]
  congr 1
  exact OldInductionRepresentable.upperHomEquiv_tensor D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    ((append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) _ b

theorem oldModuleMate_firstRow_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff j.1).app 1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (BalancedInduction.tensor (append D Sc cutoff j.1)
          ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) =
    -toCyclotomic D Sc cutoff j.1 v t
      (shiftedSourceCanonicalEquiv D Sc cutoff j v t
        (BalancedInduction.tensor (append D Sc cutoff j.1)
          ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) := by
  have hp : D.parity j.1 * D.parity j.1 = 1 := by rw [j.property]; decide
  have hc := congrArg (fun q => (oldModuleMate D Sc cutoff j.1).app q
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) hp.symm
  rw [hc, oldModuleMate_upper_tensor, shiftedSourceCanonicalEquiv_tensor,
    toCyclotomic_tensor, pairing_eq_append_comp]
  rw [hp]
  have ht := map_twist (R := k) (append D Sc cutoff j.1) 1
    (X := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
    (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g
  rw [oldCategory_twist] at ht
  have ht' :
      twist k 1 ((append D Sc cutoff j.1).map
        (X := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g) =
      (append D Sc cutoff j.1).map
        (X := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff))
        (oldTwist D Sc cutoff 1 (s ++ [j.1]) t g) := ht.symm
  exact congrArg (fun f => -((append D Sc cutoff j.1).map
    (X := (⟨v⟩ : OldCategory D Sc cutoff))
    (Y := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff)) b ≫
    equalCrossComponent D Sc cutoff j.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ f)) ht' 

/-- The fixed actual odd mate is the already inverted crossing row after canonical J. -/
theorem oldModuleMate_firstRow (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff j.1).app 1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
    -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := by
  exact coend_total_ext (append D Sc cutoff j.1)
    ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))))
    ((oldModuleMate D Sc cutoff j.1).app 1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    (⟨t⟩ : OldCategory D Sc cutoff)
    (OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap
    (toCyclotomic D Sc cutoff j.1 v t)
    (shiftedSourceCanonicalEquiv D Sc cutoff j v t).toLinearMap
    (fun s g b => by
      cases s with
      | mk s => exact oldModuleMate_firstRow_tensor D Sc cutoff j v s t g b) z

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
