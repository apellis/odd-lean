import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleAction
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace ELVContentModuleActionConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (σ : List I)

example : (contentInclusion D Sc cutoff N β).Full := inferInstance
example : (contentInclusion D Sc cutoff N β).Faithful := inferInstance
example : (contentInduction D Sc cutoff N β σ).Additive := inferInstance
example : (contentInduction D Sc cutoff N β σ).Linear k := inferInstance
example : IsSuperfunctor k (contentInduction D Sc cutoff N β σ) := inferInstance
example : (contentRestriction D Sc cutoff N β σ).Additive := inferInstance
example : (contentRestriction D Sc cutoff N β σ).Linear k := inferInstance
example : IsSuperfunctor k (contentRestriction D Sc cutoff N β σ) := inferInstance

example (v : ContentCategory D Sc cutoff N β) :
    (((contentAppend D Sc cutoff N β σ).obj v).obj.word : Multiset I) =
      β + (σ : Multiset I) :=
  ((contentAppend D Sc cutoff N β σ).obj v).content

example (v w : ContentCategory D Sc cutoff N β) :
    (v ⟶ w) = TruncatedOld D Sc cutoff N v.obj.word w.obj.word := rfl

example (M : ContentModules D Sc cutoff N (β + (σ : Multiset I)))
    (v : ContentCategory D Sc cutoff N β) :
    ((contentRestriction D Sc cutoff N β σ).obj M).obj v =
      M.obj ((contentAppend D Sc cutoff N β σ).obj v) := rfl

example (i : I) :
    (ContentModules D Sc cutoff N β ⥤ ContentModules D Sc cutoff N (β + ({i} : Multiset I))) :=
  contentF D Sc cutoff N β i

example (i : I) :
    (ContentModules D Sc cutoff N (β + ({i} : Multiset I)) ⥤ ContentModules D Sc cutoff N β) :=
  contentE D Sc cutoff N β i

example (i : I) : contentF D Sc cutoff N β i ⊣ contentE D Sc cutoff N β i :=
  contentFEAdjunction D Sc cutoff N β i

example (M : ContentModules D Sc cutoff N β) :
    (contentInduction D Sc cutoff N β σ).map ((contentAdjunction D Sc cutoff N β σ).unit.app M) ≫
      (contentAdjunction D Sc cutoff N β σ).counit.app
        ((contentInduction D Sc cutoff N β σ).obj M) =
      𝟙 ((contentInduction D Sc cutoff N β σ).obj M) :=
  (contentAdjunction D Sc cutoff N β σ).left_triangle_components M

example (M : ContentModules D Sc cutoff N (β + (σ : Multiset I))) :
    (contentAdjunction D Sc cutoff N β σ).unit.app
        ((contentRestriction D Sc cutoff N β σ).obj M) ≫
      (contentRestriction D Sc cutoff N β σ).map
        ((contentAdjunction D Sc cutoff N β σ).counit.app M) =
      𝟙 ((contentRestriction D Sc cutoff N β σ).obj M) :=
  (contentAdjunction D Sc cutoff N β σ).right_triangle_components M

example (M L : ContentModules D Sc cutoff N β) (f : M ⟶ L) :
    f ≫ (contentAdjunction D Sc cutoff N β σ).unit.app L =
      (contentAdjunction D Sc cutoff N β σ).unit.app M ≫
        (contentRestriction D Sc cutoff N β σ).map
          ((contentInduction D Sc cutoff N β σ).map f) :=
  (contentAdjunction D Sc cutoff N β σ).unit.naturality f

example (M : ContentModules D Sc cutoff N β) :
    (contentAdjunction D Sc cutoff N β σ).unit.app M ∈ parity (R := k) _ _ 0 :=
  BalancedInduction.adjunctionUnit_mem (contentAppend D Sc cutoff N β σ) M

example (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) :
    letI := contentGradedSupercategory D Sc cutoff N sy hc β
    letI := contentGradedSupercategory D Sc cutoff N sy hc (β + (σ : Multiset I))
    GradedSuperfunctor k (ContentCategory D Sc cutoff N β)
      (ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :=
  contentAppendGraded D Sc cutoff N sy hc β σ

end ELVContentModuleActionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleAction
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! == owner then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations audited"
  logInfo m!"Audited {count} declarations in {owner}."
