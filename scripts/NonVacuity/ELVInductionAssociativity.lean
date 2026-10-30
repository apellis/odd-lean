import OddMath.QuiverHecke.CyclotomicAction.ELVInductionAssociativity
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
open OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E F : Type u} [Category.{u} C] [Category.{u} D]
  [Category.{u} E] [Category.{u} F]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
  [Preadditive F] [Linear k F] [Supercategory k F]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
variable (L : E ⥤ F) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

example (M : Superfunctor k C (SVec k)) (t : F) :
    compForward (J ⋙ K) L M t ∘ₗ
        mapComponent L (M := induced K (induced J M)) (N := induced (J ⋙ K) M)
        ((inductionComp J K).hom.app M) 0 t =
      compForward J (K ⋙ L) M t ∘ₗ compForward K L (induced J M) t :=
  compForward_assoc J K L M t

#print axioms compForward_assoc
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionAssociativity
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
