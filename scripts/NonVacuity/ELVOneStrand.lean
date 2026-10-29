import OddMath.QuiverHecke.CyclotomicAction.ELVOneStrand
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVOneStrandConsumer
open OddMath OddMath.QuiverHecke ELVOld

/-- Rank one of either parity, over the ordinary rational ground field. -/
def datum (p : ZMod 2) : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => p
  even_of_odd := fun _ _ _ => even_two

def scalars (p : ZMod 2) : SKM.Scalars (datum p) ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

example (N : ℕ) : singleSpan (datum 0) (scalars 0) (fun _ => N) () = ⊤ :=
  singleSpan_eq_top (datum 0) (scalars 0) (fun _ => N) ()

example (N : ℕ) : singleSpan (datum 1) (scalars 1) (fun _ => N) () = ⊤ :=
  singleSpan_eq_top (datum 1) (scalars 1) (fun _ => N) ()

example (z : Old (datum 1) (scalars 1) (fun _ => 2) [()] [()]) :
    z ∈ singleSpan (datum 1) (scalars 1) (fun _ => 2) () :=
  single_mem_span (datum 1) (scalars 1) (fun _ => 2) () z

example (z : Old (datum 1) (scalars 1) (fun _ => 3) [()] [()]) :
    z ∈ singleSpan (datum 1) (scalars 1) (fun _ => 3) () :=
  single_mem_span (datum 1) (scalars 1) (fun _ => 3) () z

example (p : ZMod 2) (z : Old (datum p) (scalars p) (fun _ => 0) [()] [()]) : z = 0 :=
  single_eq_zero_of_cutoff_zero (datum p) (scalars p) (fun _ => 0) () rfl z

def oddColour : {i : Unit // (datum 1).parity i = 1} := ⟨(), rfl⟩
def delta : SKM.SYM (datum 1) ℚ := SKM.SYM.delta (datum 1) ℚ oddColour

/-- The coefficients in the spanning theorem have not killed the odd parameter.
This assertion concerns the coefficient ring, not independence of old dot classes. -/
theorem coefficient_delta_ne_zero (N : ℕ) (hN : 1 ≤ N) :
    SKM.SYM.elvCoefficientQuotient (datum 1) (fun _ => N) delta ≠ 0 := by
  have hd : delta ∈ SKM.SYM.CoefficientAtMost (datum 1) ℚ 1 := by
    apply Submodule.subset_span
    refine ⟨(0, {oddColour}), ?_, ?_⟩
    · simp [SKM.SYM.coefficientWeight]
    · exact SKM.SYM.coefficientBasis_delta (datum 1) ℚ oddColour
  intro hz
  have hi := SKM.SYM.elvCoefficient_quotient_injective (datum 1) ℚ
    (cutoff := fun _ => N) (d := 1) (fun _ => hN)
  have he := hi (a₁ := ⟨delta, hd⟩) (a₂ := 0) hz
  have hd0 : delta = 0 := congrArg Subtype.val he
  have hext := congrArg (SKM.SYM.exteriorProjection (datum 1) ℚ) hd0
  simp only [delta, SKM.SYM.exteriorProjection_delta, map_zero] at hext
  have hz' := (ExteriorAlgebra.ι_eq_zero_iff (R := ℚ) _).mp hext
  have h := congrArg (fun f : SKM.SYM.OddModule (datum 1) ℚ => f oddColour) hz'
  simp at h

example := coefficient_delta_ne_zero 2 (by decide)
example := coefficient_delta_ne_zero 3 (by decide)

end ELVOneStrandConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVOneStrand]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if owners.contains moduleNames[idx.toNat]! then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations audited"
  logInfo m!"Audited {count} declarations owned by ELVOneStrand; all transitive axioms allowed."
