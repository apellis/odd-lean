/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.Grading
import OddMath.SKM.ChevalleyRel

/-!
# Integer grading of the Chevalley involution

`omega_mem_gdeg` preserves the original integer degree and supplies gradedness of
`chevHom`. This is a prerequisite for Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, §9, Proposition 9.3, not its envelope extension.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (sy : Symmetrizer D)

/-- The actual images of all seven generator shapes preserve integer degree. -/
theorem gsum_chevL (g : Shape I) (μ : X) :
    gsum D sy (-μ) (chevL g) = gdeg D sy (g, μ) := by
  cases g <;>
    simp [chevL, ddotL, mateL, dcrossL, sigmaL, dotsL, lcrossL, dcapL, dcupL,
      whL, gsum, gdeg, Datum.d_self, sub_eq_add_neg] <;> ring

/-- Normal-form classes are homogeneous, including the zero class of an invalid chain. -/
theorem cl_mem_gdeg (μ : X) (s t : List (Letter I)) (L : List (LayerData I)) :
    cl D Sc μ s t L ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ s) (ob D μ t)
      (gsum D sy μ L) := by
  unfold cl
  split_ifs with h
  · exact Presentation.diag_mem_homDeg' (degree_gdeg_mkD D sy μ L h)
  · exact Submodule.zero_mem _

/-- Generator images, with their original typed endpoint transports, preserve degree. -/
theorem chevImg_mem_gdeg (g : (sig D).Gen) :
    chevImg D Sc g ∈ (pres D Sc).homDeg (gdeg D sy)
      (LocalMap.genCod (chevMap D) g) (LocalMap.genDom (chevMap D) g) (gdeg D sy g) := by
  have h := cl_mem_gdeg (Sc := Sc) sy (-g.2) (flipW g.1.cod) (flipW g.1.dom) (chevL g.1)
  rw [gsum_chevL] at h
  have ht := Presentation.comp_mem_homDeg
    (Presentation.eqToHom_mem_homDeg (P := pres D Sc) (gdeg D sy)
      (congrArg (pres D Sc).obj (genCod_chev g)))
    (Presentation.comp_mem_homDeg (Submodule.smul_mem _ (chevC D k g.1) h)
      (Presentation.eqToHom_mem_homDeg (P := pres D Sc) (gdeg D sy)
        (congrArg (pres D Sc).obj (genDom_chev g)).symm))
  unfold chevImg
  rw [zero_add, add_zero] at ht
  exact ht

/-- The original super-opposite interpretation preserves integer degree on layers. -/
theorem chevLayer_mem_gdeg (L : Layer (sig D)) :
    SOpMap.layerImg (chevMap D) (chevImg D Sc) L ∈
      (pres D Sc).homDeg (gdeg D sy) ((chevMap D).obj L.cod) ((chevMap D).obj L.dom)
        (gdeg D sy L.gen) := by
  unfold SOpMap.layerImg
  have ht := Presentation.comp_mem_homDeg
    (Presentation.eqToHom_mem_homDeg (P := pres D Sc) (gdeg D sy)
      (congrArg (pres D Sc).obj (LocalMap.whisker_genCod (chevMap D) L)).symm)
    (Presentation.comp_mem_homDeg
      (Presentation.whisk_mem_homDeg (chevImg_mem_gdeg (Sc := Sc) sy L.gen)
        ((chevMap D).obj ⟨L.start, L.left⟩) ((chevMap D).word L.right))
      (Presentation.eqToHom_mem_homDeg (P := pres D Sc) (gdeg D sy)
        (congrArg (pres D Sc).obj (LocalMap.whisker_genDom (chevMap D) L))))
  rw [zero_add, add_zero] at ht
  exact ht

/-- Integer homogeneity for arbitrary diagrams under the existing interpretation. -/
theorem chevFunctor_mem_gdeg {a b : Obj (sig D)} (d : a ⟶ b) :
    SOp.unsop ((SOpMap.functor (chevMap D) (chevImg D Sc)).map d) ∈
      (pres D Sc).homDeg (gdeg D sy) ((chevMap D).obj b) ((chevMap D).obj a)
        (Diagram.degree (gdeg D sy) d) := by
  obtain ⟨ls, hc⟩ := d
  induction ls generalizing a with
  | nil =>
    cases hc
    change SOp.unsop ((SOpMap.functor (chevMap D) (chevImg D Sc)).map (𝟙 b)) ∈ _
    erw [CategoryTheory.Functor.map_id, SOp.unsop_id]
    exact Presentation.id_mem_homDeg _ _ _
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc'⟩ := hc
    have e : (⟨L :: ls, hv, rfl, hc'⟩ : L.dom ⟶ b) =
        Diagram.ofLayer L hv ≫ ⟨ls, hc'⟩ := Diagram.ext rfl
    rw [e, Functor.map_comp, Diagram.degree_comp, Diagram.degree_ofLayer,
      SOp.comp_of_mem
        (SOp.mem_parity_iff.mp (SOpMap.functor_map_mem chevPar chevImg_mem _))
        (SOp.mem_parity_iff.mp (SOpMap.functor_map_mem chevPar chevImg_mem _)),
      SOpMap.functor_map_ofLayer]
    rw [add_comm]
    exact Submodule.smul_mem _ _
      (Presentation.comp_mem_homDeg (ih hc') (chevLayer_mem_gdeg (Sc := Sc) sy L))

/-- The original `omega` preserves integer degree on every homogeneous presented morphism.
No homogeneity hypothesis on the relations is needed for membership in the image submodules. -/
theorem omega_mem_gdeg {a b : Obj (sig D)} {n : ℤ}
    {f : (pres D Sc).obj a ⟶ (pres D Sc).obj b}
    (hf : f ∈ (pres D Sc).homDeg (gdeg D sy) a b n) :
    SOp.unsop ((omega Sc).map f) ∈
      (pres D Sc).homDeg (gdeg D sy) ((chevMap D).obj b) ((chevMap D).obj a) n := by
  obtain ⟨f, hrep, rfl⟩ := Presentation.mem_homDeg_iff.mp hf
  clear hf
  change SOp.unsop ((freeLift k (SOpMap.functor (chevMap D) (chevImg D Sc))).map f) ∈ _
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hrep
  induction hrep using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, hd, rfl⟩ := hy
    erw [freeLift_map_single, SOp.unsop_smul]
    exact Submodule.smul_mem _ _ (hd ▸ chevFunctor_mem_gdeg (Sc := Sc) sy d)
  | zero => rw [Functor.map_zero, SOp.unsop_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Functor.map_add, SOp.unsop_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [Functor.map_smul, SOp.unsop_smul]; exact Submodule.smul_mem _ r hy

end OddMath.SKM
