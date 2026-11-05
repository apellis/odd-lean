import OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputMatrix

/-! # Even ordinary dotted-counit inverse
DeformedMatrixComparison §4 transports the even negative-height raw matrix
to the canonical ordinary Ind–Res source and ordinary dotted counit rows.
The first row remains explicitly minus crossing after J; its ordered mate
identification is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def evenCounitMatrixEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m) :
    (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
      (Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) × (Fin m → Old D Sc cutoff v t)) :=
  ((evenSourceEquiv D Sc cutoff i v t).trans
    (evenInputMatrixEquiv D Sc cutoff p i.1 i.property v t m hm)).trans
      (LinearEquiv.neg k)

@[simp] theorem evenCounitMatrixEquiv_fst (p : ZMod 2)
    (i : {i : I // D.parity i = 0}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    (evenCounitMatrixEquiv D Sc cutoff p i v t m hm z).1 =
      -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) := rfl

/-- All remaining rows are the ordinary counit followed by ordinary dot powers. -/
theorem evenCounitMatrixEquiv_cap (p : ZMod 2)
    (i : {i : I // D.parity i = 0}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) (r : Fin m) :
    (evenCounitMatrixEquiv D Sc cutoff p i v t m hm z).2 r =
      unshiftedCounitComponent D Sc cutoff i.1 v t
        ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[r.val] z) := by
  change -evenInputContraction D Sc cutoff i.1 i.property v t
    (((evenCrossingInputDot D Sc cutoff i.1 i.property v t) ^ r.val)
      (evenSourceEquiv D Sc cutoff i v t z)) = _
  rw [← evenSourceInputContraction_eq, ← evenSourceInputDot_eq, Module.End.pow_apply,
    evenCapRow_normalization, neg_neg]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
