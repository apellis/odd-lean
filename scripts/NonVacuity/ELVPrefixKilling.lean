import OddMath.QuiverHecke.CyclotomicAction.ELVPrefixKilling
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVPrefixKillingConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld
open scoped TensorProduct

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

/-- Odd moving colour, repeated prefix, nonempty right context, arbitrary cutoff. -/
example (N : ℕ) :=
  allPrefix_relation_context (datum 1) (scalars 1) (fun _ => N) () [(), ()] [()]
    [(), (), (), (), ()] (𝟙 _)

/-- Even moving colour and zero cutoff are not removed from the statement. -/
example := allPrefix_relation_context (datum 0) (scalars 0) (fun _ => 0) () [] [()]
  [(), (), ()] (𝟙 _)

/-- The minimal repeated-colour prefix is allowed at odd cutoff. -/
example := allPrefix_relation_context (datum 1) (scalars 1) (fun _ => 3) () [] []
  [(), ()] (𝟙 _)

/-- The positive even-cutoff top relation stays in the coefficient quotient. -/
example := allPrefix_relation_context (datum 1) (scalars 1) (fun _ => 2) () [()] []
  [(), (), ()] (𝟙 _)

/-- An arbitrary full old Hom, not just an affine crossing or scalar tensor. -/
example (p : ZMod 2) (N : ℕ)
    (f : hom (datum p) (scalars p) (fun _ => N) [()] [()]) :=
  projection_prefix_relation_context (datum p) (scalars p) (fun _ => N) () () rfl
    [()] [(), (), ()] f (𝟙 _)

/-- Exterior and scalar components are mixed in one old morphism. -/
example := projection_prefix_relation_context (datum 1) (scalars 1) (fun _ => 3) () () rfl
  [()] [(), (), ()]
  (((1 : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) (datum 1) (fun _ => 3)) +
      SKM.SYM.elvCoefficientQuotient (datum 1) (fun _ => 3)
        (SKM.SYM.delta (datum 1) ℚ ⟨(), rfl⟩)) ⊗ₜ[ℚ]
    (𝟙 ((pres (datum 1) (scalars 1)).obj (ob (datum 1) [()])))) (𝟙 _)

#print axioms allPrefix_relation_context
#print axioms projection_prefix_relation_context
#print axioms insert_comp_move
end ELVPrefixKillingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVOldRightContext,
      `OddMath.QuiverHecke.CyclotomicAction.ELVPrefixKilling] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory: {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
