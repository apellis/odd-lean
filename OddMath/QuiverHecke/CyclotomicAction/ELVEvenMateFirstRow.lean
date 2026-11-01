import OddMath.QuiverHecke.CyclotomicAction.ELVOldMateFirstRow
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCoefficientModule

/-! # The actual even mate is the canonical first crossing row

The coefficient(0) source comparison has no parity shift or tensor twist.
The fixed signed mate evaluates to minus toCyclotomic after this actual J0.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenModuleMate_firstRow_tensor (i : {i : I // D.parity i = 0})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [i.1]) t)
    (b : Old D Sc cutoff v (s ++ [i.1])) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff i.1).app 0
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (BalancedInduction.tensor (append D Sc cutoff i.1)
          ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) =
    -toCyclotomic D Sc cutoff i.1 v t
      (evenSourceEquiv D Sc cutoff i v t
        (BalancedInduction.tensor (append D Sc cutoff i.1)
          ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) := by
  have hp : D.parity i.1 * D.parity i.1 = 0 := by rw [i.property]; decide
  have hc := congrArg (fun q => (oldModuleMate D Sc cutoff i.1).app q
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) hp.symm
  have hJ := evenSourceEquiv_tensor D Sc cutoff i v s t g b
  dsimp only [restrictedRepresentable] at hJ
  rw [hJ, hc, oldModuleMate_upper_tensor D Sc cutoff i.1 v s t g b,
    toCyclotomic_tensor D Sc cutoff i.1 v s t g b,
    pairing_eq_append_comp D Sc cutoff i.1 v s t g b, hp, twist_zero]

theorem evenModuleMate_firstRow (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : ((BalancedInduction.induction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj (⟨t⟩ : OldCategory D Sc cutoff)) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff i.1).app 0
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
    -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) := by
  exact coend_total_ext (append D Sc cutoff i.1)
    ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.induction (append D Sc cutoff i.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))))
    ((oldModuleMate D Sc cutoff i.1).app 0
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    (⟨t⟩ : OldCategory D Sc cutoff)
    (OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap
    (toCyclotomic D Sc cutoff i.1 v t)
    (evenSourceEquiv D Sc cutoff i v t).toLinearMap
    (fun s g b => by
      cases s with
      | mk s => exact evenModuleMate_firstRow_tensor D Sc cutoff i v s t g b) z

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
