import OddMath.Algebra.HomogeneousSuperfunctorIso
import StringDiagrams.Super.SVec
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.HomogeneousSuperfunctorIso
namespace HomogeneousSuperfunctorIsoExamples

private def F : Superfunctor ℚ (SVec ℚ) (SVec ℚ) :=
  ⟨PiSupercategory.pi (R := ℚ)⟩
private def G : Superfunctor ℚ (SVec ℚ) (SVec ℚ) := Superfunctor.id ℚ (SVec ℚ)
private def e (V : SVec ℚ) : F.obj V ≅ G.obj V := PiSupercategory.ζ V
private theorem h : IsSupernatural ℚ 1 (F := F.toFunctor) (G := G.toFunctor) (fun V => (e V).hom) :=
  PiSupercategory.ζ_isSupernatural
private def E : F ≅ G := ofComponents e h

/-- The inverse has odd parity, with its actual pointwise inverse formula. -/
example : E.inv ∈ parity (R := ℚ) G F 1 := ofComponents_inv_mem e h
example (V : SVec ℚ) : E.inv.total V = (e V).inv := ofComponents_inv_total e h V
example : E.hom ≫ E.inv = 𝟙 F := E.hom_inv_id
example : E.inv ≫ E.hom = 𝟙 G := E.inv_hom_id

/-- Odd naturality is tested on the odd parity-change map of the rational unit. -/
example := (inverseSupernatural e h).naturality
  (PiSupercategory.ζ_hom_mem (R := ℚ) (SVec.unit (k := ℚ)))

private def f : F ⟶ G := h.toSuperNatTrans
private theorem hf : f ∈ parity (R := ℚ) F G 1 :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr h.toSuperNatTrans_isHomogeneous
private theorem he (V : SVec ℚ) : (e V).hom = f.total V :=
  (homogeneous_total h V).symm

/-- The constructor preserves a given odd forward map, rather than just its carrier. -/
example : (ofHom f hf e he).hom = f := ofHom_hom f hf e he
example : (ofHom f hf e he).inv ∈ parity (R := ℚ) G F 1 := ofHom_inv_mem f hf e he
example : f ≫ (ofHom f hf e he).inv = 𝟙 F := ofHom_hom_inv_id f hf e he
example : (ofHom f hf e he).inv ≫ f = 𝟙 G := ofHom_inv_hom_id f hf e he
example : (ofHom f hf e he).inv.total (SVec.unit (k := ℚ)) =
    (e (SVec.unit (k := ℚ))).inv := ofHom_inv_total f hf e he _

end HomogeneousSuperfunctorIsoExamples
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.Algebra.HomogeneousSuperfunctorIso
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} declarations in {owner}"
