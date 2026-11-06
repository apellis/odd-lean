import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

/-! # Signed inverse of the ordinary probe induction dot
The inverse source dot has the same parity. Its induced transform requires
the factor (-1)^(p*p), retaining the signed right-multiplication convention.
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

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (ν : List I) (i : I)

/-- The literal ordinary appended dot is an isomorphism at each source word. -/
noncomputable def probeOrdinaryAppendDotIso
    (v : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) :
    (probeOrdinaryAppend D Sc m ν i).obj v ≅ (probeOrdinaryAppend D Sc m ν i).obj v := by
  haveI := (isUnit_iff_isIso (End.of (probeOrdinaryAppendDot D Sc m ν i v))).mp
    (probeOrdinaryAppendDot_isUnit D Sc m ν i v)
  exact asIso (probeOrdinaryAppendDot D Sc m ν i v)

variable (M : Superfunctor k
  (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))

end OddMath.QuiverHecke