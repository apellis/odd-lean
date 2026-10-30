import OddMath.QuiverHecke.CyclotomicAction.ELVInductionWhiskering
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
open OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]


variable {J}
variable {J' : C ⥤ D} [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
example {p : ZMod 2}
    {α : ∀ v, J.obj v ⟶ J'.obj v} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (z : E) :
    compForward J K M z ∘ₗ mapComponent K (transformComponent hα M) p z =
      transformLinear (hα.whiskerRight K) M z ∘ₗ compForward J' K M z :=
  compForward_transform_inner K hα M z

variable (J) {K}
variable {K' : D ⥤ E} [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
example {p : ZMod 2}
    {β : ∀ w, K.obj w ⟶ K'.obj w} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) (z : E) :
    compForward J K M z ∘ₗ transformLinear hβ (induced J M) z =
      transformLinear (hβ.whiskerLeft J) M z ∘ₗ compForward J K' M z :=
  compForward_transform_outer J hβ M z

#print axioms compForward_transform_inner
#print axioms compForward_transform_outer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionWhiskering
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
