import OddMath.SKM.Rho.Computations
import OddMath.SKM.Rho.Whisker

/-!
# Normalize for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoInversionKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem tensor_eq (ν μ : X) (u s : List (Letter I)) (h : wt D μ s = ν) :
    (ob D ν u).tensor (ob D μ s) = ob D μ (u ++ s) := by
  apply Obj.ext
  · change wt D ν u = wt D μ (u ++ s)
    rw [wt_append, h]
  · change wd D ν u ++ wd D μ s = wd D μ (u ++ s)
    rw [wd_append, h]

private theorem raw_heq {C : Type*} [Category C] {a b a' b' : C}
    (ha : a = a') (hb : b = b') {f : a ⟶ b} {g : a' ⟶ b'}
    (h : f = eqToHom ha ≫ g ≫ eqToHom hb.symm) : HEq f g := by
  subst ha; subst hb
  exact heq_of_eq (by simpa using h)

theorem raw_context (a : k) (ν μ ξ ω : X) (u s r v : List (Letter I))
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hv : wt D ξ v = μ)
    (hω : wt D ν u = ω) (A : List (LayerData I)) (hA : SChain s A r) :
    HEq ((pres D Sc).wRAt ω
      ((pres D Sc).wL (ob D ν u) (a • cl D Sc μ s r A)) (ob D ξ v)
      hω hω)
      (a • cl D Sc ξ (u ++ s ++ v) (u ++ r ++ v) (A.map (whL u v))) := by
  subst μ ω
  have ho (q : List (Letter I)) (hq : wt D (wt D ξ v) q = ν) :
      ((ob D ν u).tensor (ob D (wt D ξ v) q)).tensor (ob D ξ v) =
        ob D ξ (u ++ q ++ v) := by
    rw [tensor_eq ν (wt D ξ v) u q hq]
    exact tensor_eq (wt D ξ v) ξ (u ++ q) v rfl
  apply raw_heq (congrArg (pres D Sc).obj (ho s hs)) (congrArg (pres D Sc).obj (ho r hr))
  rw [Presentation.wL_smul, Presentation.wRAt_smul, Linear.smul_comp, Linear.comp_smul]
  congr 1
  rw [cl_of hA]
  have hcomp : (ob D ν u).Composable (ob D (wt D ξ v) s) :=
    Presentation.Bicat.Hom.composable
      (psiWordAt (Sc := Sc) (wt D ν u) ν u rfl) (psiWordAt ν (wt D ξ v) s hs)
  rw [Presentation.wL_diag_of_composable _ _ _ hcomp]
  have hcomp' : ((ob D ν u).tensor (ob D (wt D ξ v) s)).Composable (ob D ξ v) :=
    Presentation.Bicat.Hom.composable
      ((psiWordAt (Sc := Sc) (wt D ν u) ν u rfl) ≫ psiWordAt ν (wt D ξ v) s hs)
      (psiWordAt (wt D ξ v) ξ v rfl)
  rw [Presentation.wRAt_diag _ _ _ hcomp', cl_of (hA.whisk u v)]
  refine Presentation.diag_eq_of_layers_eq' _ _ _ (ho s hs) (ho r hr) ?_
  simp only [Diagram.layers_lwhisker, Diagram.layers_rwhisker, layers_mkD]
  rw [← layList_whisker D ξ u v hA]
  simp only [List.map_map, ob, Layer.wl, Layer.wr, Layer.whisker, hs]
  rfl

end OddMath.SKM.RhoInversionKernel
