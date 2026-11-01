import OddMath.QuiverHecke.CyclotomicAction.ELVProbeScalarModules

/-! # Old append induction preserves actual scalar coefficient evaluation
The full coefficient slide and the existing coend balance prove preservation,
including the odd coefficient kernel. No scalar evaluation is applied to a
positive-weight coefficient truncation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k)
local notation "cut" => probeCutoff D m
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cut
local notation "ev" => SKM.SYM.elvScalarEvaluation D cut (probeScalarValues D m) (probeScalarValues_vanish D m)
variable (ν : List I)
local notation "C" => ELVOld.OldContentCategory D Sc cut ν

@[simp] theorem probeOldCoefficient_zero (v : C) :
    probeOldCoefficient D m Sc ν v 0 = 0 := by
  change (ELVOld.ideal D Sc cut _ _).mkQ (0 ⊗ₜ[k] (𝟙 _)) = 0
  rw [TensorProduct.zero_tmul, map_zero]

theorem probeOldCoefficient_add (v : C) (c d : A) :
    probeOldCoefficient D m Sc ν v (c + d) =
      probeOldCoefficient D m Sc ν v c + probeOldCoefficient D m Sc ν v d := by
  change (ELVOld.ideal D Sc cut _ _).mkQ ((c+d) ⊗ₜ[k] (𝟙 _)) = _
  rw [TensorProduct.add_tmul, map_add]
  rfl

/-- The complete output parity twist is retained in the actual content quotient. -/
theorem probeOldCoefficient_slide {v w : C} {p : ZMod 2} {c : A}
    (hc : c ∈ SKM.SYM.elvCoefficientParity D cut p) (f : v ⟶ w) :
    f ≫ probeOldCoefficient D m Sc ν w c =
      probeOldCoefficient D m Sc ν v c ≫ twist k p f := by
  obtain ⟨f, rfl⟩ := (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ_surjective f
  have htw : twist k p (X := v) (Y := w)
      ((ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ f) =
    (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ
      (twist k p (X := ELVOld.obj D Sc cut v.obj.word) (Y := ELVOld.obj D Sc cut w.obj.word) f) := by
    change twist k p (X := v.obj) (Y := w.obj) _ = _
    simp only [twist_apply, ELVOld.oldCategory_proj, ELVOld.oldProj_mk, map_add, map_smul]
  rw [htw]
  exact congrArg (ELVOld.ideal D Sc cut v.obj.word w.obj.word).mkQ
    (ELVPScalar.scalar_slide_homogeneous D Sc cut hc f)

@[simp] theorem probeOldCoefficient_append (i : I) (v : C) (c : A) :
    (ELVOld.oldContentAppend D Sc cut ν i).map (probeOldCoefficient D m Sc ν v c) =
      probeOldCoefficient D m Sc (i :: ν) ((ELVOld.oldContentAppend D Sc cut ν i).obj v) c := by
  change (ELVOld.ideal D Sc cut _ _).mkQ
    (ELVOld.rightContext D Sc cut [i] v.obj.word v.obj.word
      (ELVPScalar.scalar D Sc cut v.obj.word c)) = _
  rw [ELVPScalar.rightContext_scalar]
  rfl

/-- The concrete scalar-evaluation class is closed under the actual old
content append induction, including its odd coefficient kernel. -/
theorem probeOldInduced_evaluatesCoefficients (i : I)
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    ProbeEvaluatesCoefficients D m Sc (i :: ν)
      (ELVOld.BalancedInduction.induced (ELVOld.oldContentAppend D Sc cut ν i) N) := by
  intro t c
  let J := ELVOld.oldContentAppend D Sc cut ν i
  let L := ELVOld.BalancedInduction.induced J N
  change L.toFunctor.map (probeOldCoefficient D m Sc (i :: ν) t c) = ev c • 𝟙 (L.obj t)
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cut) ?_ ?_ ?_ c
  · rw [probeOldCoefficient_zero, L.toFunctor.map_zero, map_zero, zero_smul]
  · intro p c
    change ELVOld.BalancedInduction.postcompose J N.toFunctor
      (probeOldCoefficient D m Sc (i :: ν) t c.val) = ev c.val • LinearMap.id
    apply ELVOld.BalancedInduction.hom_ext
    intro v g b
    rw [ELVOld.BalancedInduction.postcompose_tensor,
      probeOldCoefficient_slide D m Sc (i :: ν) c.property]
    have hcoef : probeOldCoefficient D m Sc (i :: ν) (J.obj v) c.val =
        J.map (probeOldCoefficient D m Sc ν v c.val) :=
      (probeOldCoefficient_append D m Sc ν i v c.val).symm
    rw [hcoef, ELVOld.BalancedInduction.balance, hN v c.val]
    change ELVOld.BalancedInduction.tensor J N.toFunctor v (twist k p g) (ev c.val • b) =
      ev c.val • ELVOld.BalancedInduction.tensor J N.toFunctor v g b
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [twist_zero]
      simp only [ELVOld.BalancedInduction.tensor, TensorProduct.tmul_smul, map_smul]
    · have hc : ev c.val = 0 := SKM.SYM.elvScalarEvaluation_odd_zero D cut
        (probeScalarValues D m) (probeScalarValues_vanish D m) c.property
      simp only [hc, zero_smul, ELVOld.BalancedInduction.tensor, TensorProduct.tmul_zero, map_zero]
  · intro c d hc hd
    rw [probeOldCoefficient_add, L.toFunctor.map_add, hc, hd, map_add, add_smul]

end OddMath.QuiverHecke

