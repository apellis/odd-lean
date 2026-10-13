/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.ChevalleyHom
import OddMath.SKM.ChevalleyGradedHom

/-!
# Chevalley placement and composition comparisons

`Om_plcL_all` proves placement compatibility on arbitrary quotient morphisms,
retaining the original endpoint transports. `chevHomObj_id` and `chevHomObj_comp`
compare actual `UGr` 1-morphisms for whiskering compatibility and coherence.
These are prerequisites for the extension in [BE2] §9, Proposition 9.3;
the global coherence and shifted-envelope extension are not asserted here.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- The original Chevalley map commutes with placement on every quotient morphism,
not just a chosen parity component. The region and signed-word casts are explicit. -/
theorem Om_plcL_all (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)) :
    Om D Sc μ (u ++ s ++ v) (u ++ t ++ v) (plcL D Sc μ u v s t f) =
      wordCast (-μ) (by simp only [flipW_append]) (by simp only [flipW_append])
        (plcL D Sc (-μ) (flipW u) (flipW v) (flipW t) (flipW s)
          (regionCast (wt_flipW D μ v).symm (Om D Sc (wt D μ v) s t f))) := by
  obtain ⟨g, rfl⟩ := (pres D Sc).lin_surjective f
  induction g using Finsupp.induction_linear with
  | zero => simp only [Presentation.lin_zero, map_zero, Om_zero, regionCast_zero]
  | add f g hf hg =>
    erw [Presentation.lin_add]
    simp only [map_add, Om_add, regionCast_add, hf, hg]
  | single d r =>
    obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
    erw [show (Finsupp.single (mkD D (wt D μ v) L hL) r : LinDiagram k _ _) =
        r • dg D (wt D μ v) L hL from (Finsupp.smul_single_one _ r).symm,
      Presentation.lin_smul, lin_dg hL]
    simp only [map_smul, Om_smul, regionCast_smul]
    congr 1
    exact Om_plcL μ u v (cl_mem_homPar hL rfl)

variable {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- Original Chevalley relabelling preserves the empty 1-morphism. -/
theorem chevHomObj_id (a : UGr D Sc sy hc) :
    chevHomObj (𝟙 a) = 𝟙 (negWeight a) := by
  apply Presentation.Bicat.Hom.ext
  rfl

/-- Original Chevalley relabelling preserves composition of actual 1-morphisms. -/
theorem chevHomObj_comp {a b c : UGr D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    chevHomObj (f ≫ g) = chevHomObj f ≫ chevHomObj g := by
  apply Presentation.Bicat.Hom.ext
  exact (chevMap D).obj_tensor f.obj g.obj
end OddMath.SKM
