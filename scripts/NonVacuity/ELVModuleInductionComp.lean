import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace ELVModuleInductionCompConsumer
open BalancedInduction
universe u
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

example : induction (k := k) J ⋙ induction K ≅ induction (J ⋙ K) := inductionComp J K

example (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).hom.app M ≫ (inductionComp J K).inv.app M =
      𝟙 ((induction K).obj ((induction J).obj M)) :=
  (inductionComp J K).hom_inv_id_app M

example (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).inv.app M ≫ (inductionComp J K).hom.app M =
      𝟙 ((induction (J ⋙ K)).obj M) :=
  (inductionComp J K).inv_hom_id_app M

example (M N : Superfunctor k C (SVec k)) (f : M ⟶ N) :
    (induction K).map ((induction J).map f) ≫ (inductionComp J K).hom.app N =
      (inductionComp J K).hom.app M ≫ (induction (J ⋙ K)).map f :=
  inductionComp_naturality J K f

example (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).hom.app M ∈ parity (R := k) _ _ 0 := inductionComp_hom_mem J K M
example (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).inv.app M ∈ parity (R := k) _ _ 0 := inductionComp_inv_mem J K M

example (M : Superfunctor k C (SVec k)) (v : C) (w : D) (z : E)
    (g : K.obj w ⟶ z) (h : J.obj v ⟶ w) (m : M.obj v) :
    ((inductionComp J K).hom.app M).total z
      (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
      tensor (J ⋙ K) M.toFunctor v (K.map h ≫ g) m :=
  inductionComp_hom_total_tensor J K M v w z g h m

example (M : Superfunctor k C (SVec k)) (v : C) (z : E)
    (a : K.obj (J.obj v) ⟶ z) (m : M.obj v) :
    ((inductionComp J K).inv.app M).total z (tensor (J ⋙ K) M.toFunctor v a m) =
      tensor K (induced J M).toFunctor (J.obj v) a (tensor J M.toFunctor v (𝟙 _) m) :=
  inductionComp_inv_total_tensor J K M v z a m

end ELVModuleInductionCompConsumer

#print axioms OddMath.QuiverHecke.ELVOld.BalancedInduction.inductionComp
#print axioms OddMath.QuiverHecke.ELVOld.BalancedInduction.inductionComp_hom_tensor
#print axioms OddMath.QuiverHecke.ELVOld.BalancedInduction.inductionComp_inv_tensor
#print axioms OddMath.QuiverHecke.ELVOld.BalancedInduction.inductionComp_hom_mem
#print axioms OddMath.QuiverHecke.ELVOld.BalancedInduction.inductionComp_inv_mem

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations audited"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
