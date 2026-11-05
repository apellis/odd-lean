/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedClosedAction
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorMatrixCoefficients

/-! # Closed diagrams as source coefficients in the supported action

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, in the
matrix form of `docs/Nondegeneracy/SwappedActionAssembly.md` and the bubble evaluation of
`docs/Nondegeneracy/SwappedVacuumBubbles.md`, §5.

If the entry of a closed diagram `cl M` at every rightmost sector `t` is an endomorphism
`f t` of the target object `Ys t`, the closed diagram acts on the supported matrix module
by postcomposition with `F_p (f t)` (`pointwiseUpwardModuleAction_act_bubAt_cl_eq`). For the
tensor target family every sector other than the vacuum carries a zero object, so a closed
diagram acts as the source coefficient `a` as soon as its entry at the vacuum sector is the
coefficient action of `a` there (`pointwiseUpwardModuleAction_act_bubAt_cl_eq_coefficient`).
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams

/-- At a positive height `hᵢ(μ) > 0` the normalized left bubble `c_{μ;i}⁻¹ bubLs(s)` is the
closed diagram of the dotted leftward cup with `hᵢ(μ) - 1` dots followed by the rightward cap
with `s + hᵢ(μ) - 1` dots (Brundan–Ellis, arXiv:1701.04133v2, (2.11), (2.13), (2.17)). -/
theorem inv_smul_bubLs_of_pos {I X k : Type*} [AddCommGroup X] [CommRing k] {D : Datum I X}
    {Sc : Scalars D k} (cs : CScalars Sc) (i : I) (μ : X) (h : 0 < D.h i μ) (s : ℕ) :
    (↑(cs.c μ i)⁻¹ : k) • bubLs cs i μ s =
      cl D Sc μ [] [] (dcupL i (D.h i μ - 1).toNat ++ epsL i ((s : ℤ) + D.h i μ - 1).toNat) := by
  have hn : (0 : ℤ) ≤ (s : ℤ) + D.h i μ - 1 := by omega
  simp only [bubLs, bubL, hn, ite_true, etaP, h, Linear.smul_comp, smul_smul]
  rw [cl_comp (sChain_dcupL i _) (sChain_epsL i _), Units.inv_mul, one_smul]

end OddMath.SKM
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance supportedClosedCoefficientsHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

private theorem functorEquality_map_square {C B : Type*} [Category* C] [Category* B]
    (F G : C ⥤ B) (h : F = G) {V W : C} (f : V ⟶ W) :
    F.map f ≫ eqToHom (congrArg (fun H => H.obj W) h) =
    eqToHom (congrArg (fun H => H.obj V) h) ≫ G.map f := by
  subst G
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

section Generic
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

/-- Postcomposition with a supported path image is postcomposition with the chosen factor
path image of the same endomorphism, in the entry charts. -/
theorem entryEquiv_comp_map {w : List (Col I X)} {s t : Sector I} (p : SPath w s t)
    (G : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (g : G ⟶ (pathFunctor D (parameterTwist D Sc) m cutoff bound ΛP ΛR p).obj Z) (a : End Z) :
    entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p G Z
        (g ≫ (pathFunctor D (parameterTwist D Sc) m cutoff bound ΛP ΛR p).map a) =
      entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p G Z g ≫ ((P).pathFunctor p).map a.hom := by
  have hsq := functorEquality_map_square _ _
    (factor_pathFunctor_inclusion D Sc m cutoff bound ΛP ΛR hP hR p) a
  simp only [entryEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_inv,
    eqToIso.hom, Category.id_comp, Category.assoc]
  change (g ≫ _).hom ≫ _ = g.hom ≫ _ ≫ _
  rw [InducedCategory.comp_hom, Category.assoc]
  exact congrArg (g.hom ≫ ·) hsq

variable [Finite I] (sy : Symmetrizer D) (hc : Sc.Homogeneous)
  (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR
    (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
      (parameterTwist_homogeneous D Sc hc) bound)
local notation "leftward" => pointwiseLeftwardData D Sc m cutoff bound ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) bound)
local notation "gens" => ProbeReservoir.swappedGens (P) c leftward
local notation "action" => pointwiseUpwardModuleAction D Sc m cutoff bound ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) bound)
        (reservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR sy hc) Gs Ys
attribute [local irreducible] elvProbeCrossCoeffOf

/-- **A closed diagram with supported sector entries.** If the entry of the closed diagram
`cl M` at every rightmost sector `t` is the supported endomorphism `f t` of `Ys t`, then
`cl M`, placed to the right of the upward word of `t`, acts on the supported matrix module
by postcomposition with `F_p (f t)` at every summand path `p`. -/
theorem pointwiseUpwardModuleAction_act_bubAt_cl_eq (μ : X) (t : List I)
    (M : List (SKM.LayerData I)) (hM : SKM.SChain [] M []) (f : ∀ s, End (Ys s))
    (hf : ∀ s, ProbeReservoir.compDiag gens (SKM.mkD D μ M hM) (SPath.nil s) (SPath.nil s)
      (Ys s).obj = (f s).hom)
    (x : matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys (SKM.ob D μ (upWord t))) :
    (action μ).act t t (SKM.bubAt D Sc μ (upWord t) (SKM.cl D Sc μ [] [] M)) x =
      fun s τ p => x s τ p ≫
        (pathFunctor D (parameterTwist D Sc) m cutoff bound ΛP ΛR p).map (f τ.1) := by
  apply (matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys (SKM.ob D μ (upWord t))).injective
  funext s τ p
  rw [pointwiseUpwardModuleAction_act_bubAt_cl (hM := hM), hf]
  exact (entryEquiv_comp_map D Sc m cutoff bound ΛP ΛR hP hR p (Gs s) (Ys τ.1)
    (x s τ p) (f τ.1)).symm

end Generic
section Tensor
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (sy : Symmetrizer D) (hc : Sc.Homogeneous) (sw : List I)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff N ΛP ΛR hP hR
    (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
      (parameterTwist_homogeneous D Sc hc) N)
local notation "leftward" => pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) N)
local notation "gens" => ProbeReservoir.swappedGens (P) c leftward
local notation "Ys" => tensorTargetFamily D Sc m cutoff ΛP ΛR L
local notation "action" => pointwiseUpwardModuleAction D Sc m cutoff N ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) N)
        (reservoirWindowIdeal D Sc m cutoff N ΛP ΛR hP hR sy hc)
  (tensorSourceFamily D Sc m cutoff ΛP ΛR L sw) Ys
attribute [local irreducible] elvProbeCrossCoeffOf

/-- **A closed diagram acting as a source coefficient.** In the complete supported action on
the tensor families, the closed diagram `cl M`, placed to the right of the upward word of
`t`, acts as the source coefficient `a` (`tensorMatrixCoefficientAction`) as soon as its entry
at the vacuum sector is the coefficient action of `a` there: every other sector carries a
zero object. -/
theorem pointwiseUpwardModuleAction_act_bubAt_cl_eq_coefficient (μ : X) (t : List I)
    (M : List (SKM.LayerData I)) (hM : SKM.SChain [] M []) (a : SYM D k)
    (hvac : ProbeReservoir.compDiag gens (SKM.mkD D μ M hM) (SPath.nil (0,0)) (SPath.nil (0,0))
      (Ys (0,0)).obj = (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom) :
    (action μ).act t t (SKM.bubAt D Sc μ (upWord t) (SKM.cl D Sc μ [] [] M)) =
      tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L sw (SKM.ob D μ (upWord t)) a := by
  classical
  apply LinearMap.ext
  intro x
  rw [pointwiseUpwardModuleAction_act_bubAt_cl_eq D Sc m cutoff N ΛP ΛR hP hR sy hc
    (tensorSourceFamily D Sc m cutoff ΛP ΛR L sw) Ys μ t M hM
    (fun s => tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR s a)]
  · rfl
  · intro s
    by_cases hs : s = (0,0)
    · subst hs
      exact hvac
    · exact congrArg InducedCategory.Hom.hom
        ((tensorTargetFamily_isZero D Sc m cutoff ΛP ΛR L s hs).eq_of_src
          (⟨ProbeReservoir.compDiag gens (SKM.mkD D μ M hM) (SPath.nil s) (SPath.nil s)
            (Ys s).obj⟩ : End (Ys s)) _)

/-- **Normalized left bubbles at positive height as source coefficients.** At `hᵢ(μ) > 0`,
`c_{μ;i}⁻¹ bubLs(s)` beside the upward word of `t` acts as the source coefficient `a` once the
vacuum entry of its closed diagram (`SKM.inv_smul_bubLs_of_pos`) is the coefficient action
of `a`. -/
theorem pointwiseUpwardModuleAction_act_bubAt_bubLs_eq_coefficient (cs : SKM.CScalars Sc)
    (i : I) (μ : X) (h : 0 < D.h i μ) (n : ℕ) (t : List I) (a : SYM D k)
    (hvac : ProbeReservoir.compDiag gens
      (SKM.mkD D μ (SKM.dcupL i (D.h i μ - 1).toNat ++ SKM.epsL i ((n : ℤ) + D.h i μ - 1).toNat)
        ((SKM.sChain_dcupL i _).append (SKM.sChain_epsL i _)))
      (SPath.nil (0,0)) (SPath.nil (0,0)) (Ys (0,0)).obj =
        (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom) :
    (action μ).act t t (SKM.bubAt D Sc μ (upWord t) ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ n)) =
      tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L sw (SKM.ob D μ (upWord t)) a := by
  rw [SKM.inv_smul_bubLs_of_pos cs i μ h n]
  exact pointwiseUpwardModuleAction_act_bubAt_cl_eq_coefficient D Sc m cutoff ΛP ΛR L hP hR sy hc
    sw μ t _ _ a hvac

end Tensor

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
