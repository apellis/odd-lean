import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensorGrading

/-! # Graded kernel tensor equivalences

The graded kernel transfer in DeformedMatrixComparison §4: an even,
componentwise bijective ordinary-right kernel map gives an even isomorphism
after balanced tensoring with every supermodule. No flatness is assumed.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (K L : Cᵒᵖ ⥤ ModuleCat.{u} k) [K.Additive] [L.Additive]
  (G : CoefficientGrading K) (H : CoefficientGrading L)
  (hK : IsGradedKernel K G) (hL : IsGradedKernel L H)
  (M : C ⥤ SVec k) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
  (e : K ⟶ L) (hb : ∀ v, Function.Bijective (e.app v))

/-- The equivalence on the literal graded quotients has the established
kernel-tensor map as its forward map. -/
def gradedIsoOfBijective : superspace K G M hK ≅ superspace L H M hL where
  hom := map M e
  inv := (equivOfBijective M e hb).symm.toLinearMap
  hom_inv_id := by
    ext x
    exact (equivOfBijective M e hb).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact (equivOfBijective M e hb).apply_symm_apply x

variable (he : ∀ v : C, (e.app (op v)).hom ∈
  parity (R := k) (coefficientSpace G v) (coefficientSpace H v) 0)
include he

/-- Evenness of the forward map only requires even coefficient components. -/
theorem gradedIsoOfBijective_hom_even :
    (gradedIsoOfBijective K L G H hK hL M e hb).hom ∈
      parity (R := k) (superspace K G M hK) (superspace L H M hL) 0 :=
  map_even K G M hK H hL e he

/-- The inverse is even as a consequence, with no separate inverse-grading input. -/
theorem gradedIsoOfBijective_inv_even :
    (gradedIsoOfBijective K L G H hK hL M e hb).inv ∈
      parity (R := k) (superspace L H M hL) (superspace K G M hK) 0 :=
  Supercategory.inv_mem (gradedIsoOfBijective K L G H hK hL M e hb)
    (gradedIsoOfBijective_hom_even K L G H hK hL M e hb he)

omit he in
@[simp] theorem gradedIsoOfBijective_hom_tensor (v : C)
    (x : K.obj (op v)) (m : M.obj v) :
    (gradedIsoOfBijective K L G H hK hL M e hb).hom (tensor K M v x m) =
      tensor L M v (e.app (op v) x) m :=
  map_tensor M e v x m

end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
