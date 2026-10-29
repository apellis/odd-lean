import OddMath.QuiverHecke.CyclotomicAction.ELVOldGrading
import NonVacuity.ELVHomGrading
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVOldGradingConsumer
open OddMath OddMath.QuiverHecke ELVOld
open ELVCoefficientCategoryConsumer ELVCoefficientGradingConsumer ELVHomGradingConsumer

example (v w : List Unit) :
    DirectSum.IsInternal (oldDegree datum sy scalars homogeneous (fun _ => 2) v w) :=
  oldDegree_internal datum sy scalars homogeneous (fun _ => 2) v w

example (v w : List Unit) :
    DirectSum.IsInternal (oldDegree datum sy scalars homogeneous (fun _ => 3) v w) :=
  oldDegree_internal datum sy scalars homogeneous (fun _ => 3) v w

example (v w : List Unit) :
    DirectSum.IsInternal (oldParity datum scalars (fun _ => 2) v w) :=
  oldParity_internal datum scalars (fun _ => 2) v w

example {v w : List Unit} {f : hom datum scalars (fun _ => 2) v w}
    (hf : f ∈ ideal datum scalars (fun _ => 2) v w) (n : ℤ) :
    homDproj datum sy scalars homogeneous (fun _ => 2) n f ∈
      ideal datum scalars (fun _ => 2) v w :=
  ideal_dproj_mem datum sy scalars homogeneous (fun _ => 2) hf n

example (p : ZMod 2) {v s t : List Unit} {m n : ℤ}
    {r : hom datum scalars (fun _ => 3) s t} {f : Old datum scalars (fun _ => 3) v s}
    (hr : r ∈ elvHomDegree datum sy scalars homogeneous (fun _ => 3) s t n)
    (hf : f ∈ oldDegree datum sy scalars homogeneous (fun _ => 3) v s m) :
    oldCompose datum scalars (fun _ => 3) p r f ∈
      oldDegree datum sy scalars homogeneous (fun _ => 3) v t (m + n) :=
  oldCompose_mem_oldDegree datum sy scalars homogeneous (fun _ => 3) p hr hf

example (p : ZMod 2) (n : ℤ) (v w : List Unit)
    (f : Old datum scalars (fun _ => 2) v w) :
    oldProj datum scalars (fun _ => 2) v w p
      (oldDproj datum sy scalars homogeneous (fun _ => 2) v w n f) =
    oldDproj datum sy scalars homogeneous (fun _ => 2) v w n
      (oldProj datum scalars (fun _ => 2) v w p f) :=
  oldProj_oldDproj datum sy scalars homogeneous (fun _ => 2) p n v w f

-- The coefficient category still has a nonzero exterior generator of integer degree two.
-- This is a coefficient test, not a positive-content nonvanishing assertion.
example : SKM.SYM.elvCoefficientQuotient datum (fun _ => 2) delta ≠ 0 :=
  quotient_delta_ne_zero 2 (by decide)

universe u
example {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (sy : SKM.Symmetrizer D) (Sc : SKM.Scalars D k)
    (hc : Sc.Homogeneous) (cutoff : I → ℕ) (v w : List I) :
    DirectSum.IsInternal (oldDegree D sy Sc hc cutoff v w) :=
  oldDegree_internal D sy Sc hc cutoff v w

end ELVOldGradingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVOldGrading]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if owners.contains moduleNames[idx.toNat]! then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations audited"
  logInfo m!"Audited {count} declarations owned by ELVOldGrading; all transitive axioms allowed."
