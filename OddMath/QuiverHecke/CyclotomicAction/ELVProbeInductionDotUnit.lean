import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

/-! # Signed inverse of the ordinary probe induction dot
The inverse source dot has the same parity. Its induced transform requires
the factor (-1)^(p*p), retaining the signed right-multiplication convention.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} (e : ∀ v, J.obj v ≅ J.obj v)
  (he : IsSupernatural k p (fun v => (e v).hom))

omit [IsSuperfunctor k J] in
include he in
/-- The inverse family retains the same parity and supernatural sign. -/
theorem inverseComponent_supernatural :
    IsSupernatural k p (fun v => (e v).inv) := by
  apply IsSupernatural.of_twist (fun v => Supercategory.inv_mem (e v) (he.mem v))
  intro v w f
  have ht := he.naturality_twist (twist k p f)
  rw [twist_twist] at ht
  apply (cancel_mono (e w).hom).mp
  rw [Category.assoc, (e w).inv_hom_id, Category.comp_id]
  rw [Category.assoc, ht, ← Category.assoc, (e v).inv_hom_id, Category.id_comp]

variable (M : Superfunctor k C (SVec k))

/-- The parity sign is required when composing two induced homogeneous transforms. -/
theorem transformLinear_inverse_right (t : D) :
    (transformLinear he M t).comp
      (sign k (p*p) • transformLinear (inverseComponent_supernatural J e he) M t) = LinearMap.id := by
  apply hom_ext
  intro v g b
  rw [LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
    transformLinear_tensor, transformLinear_tensor, twist_comp,
    twist_of_mem p (Supercategory.inv_mem (e v) (he.mem v)), twist_twist,
    Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    (e v).hom_inv_id, Category.id_comp]
  simp only [tensor, ← TensorProduct.smul_tmul', map_smul, sign_smul_sign_smul]
  rfl

/-- Both inverse products are proved; no finite-dimensionality is used. -/
theorem transformLinear_inverse_left (t : D) :
    (sign k (p*p) • transformLinear (inverseComponent_supernatural J e he) M t).comp
      (transformLinear he M t) = LinearMap.id := by
  apply hom_ext
  intro v g b
  rw [LinearMap.comp_apply, LinearMap.smul_apply,
    transformLinear_tensor, transformLinear_tensor, twist_comp,
    twist_of_mem p (he.mem v), twist_twist,
    Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    (e v).inv_hom_id, Category.id_comp]
  simp only [tensor, ← TensorProduct.smul_tmul', map_smul, sign_smul_sign_smul]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (ν : List I) (i : I)

/-- The literal ordinary appended dot is an isomorphism at each source word. -/
noncomputable def probeOrdinaryAppendDotIso [Fact Sc.PureNilpotent]
    (v : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) :
    (probeOrdinaryAppend D Sc m ν i).obj v ≅ (probeOrdinaryAppend D Sc m ν i).obj v := by
  haveI := (isUnit_iff_isIso (End.of (probeOrdinaryAppendDot D Sc m ν i v))).mp
    (probeOrdinaryAppendDot_isUnit D Sc m ν i v)
  exact asIso (probeOrdinaryAppendDot D Sc m ν i v)

variable (M : Superfunctor k
  (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))

/-- The prescribed signed dot transform has an explicit two-sided inverse
on the actual ordinary append coend. -/
def probeOrdinaryInductionDotUnit [Fact Sc.PureNilpotent]
    (t : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) (i :: ν)) :
    (End (ELVOld.BalancedInduction.superspace (probeOrdinaryAppend D Sc m ν i) M.toFunctor t))ˣ :=
  let J := probeOrdinaryAppend D Sc m ν i
  let e := probeOrdinaryAppendDotIso D Sc m ν i
  let he : IsSupernatural k (D.parity i) (fun v => (e v).hom) :=
    probeOrdinaryAppendDot_supernatural D Sc m ν i
  { val := End.of (ELVOld.BalancedInduction.transformLinear he M t)
    inv := End.of (sign k (D.parity i * D.parity i) •
      ELVOld.BalancedInduction.transformLinear
        (ELVOld.BalancedInduction.inverseComponent_supernatural J e he) M t)
    val_inv := ELVOld.BalancedInduction.transformLinear_inverse_right J e he M t
    inv_val := ELVOld.BalancedInduction.transformLinear_inverse_left J e he M t }

end OddMath.QuiverHecke