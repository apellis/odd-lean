import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMomentMaps

/-! # Full coefficient endomorphisms of old supermodules

The source-word coefficient action required by `SwappedVacuumCoordinates.md`,
§6, consists of genuine supermodule maps. Its odd components retain their
parity and their signed balanced-induction tensor formula.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def coefficientHomLinear (v : List I) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      End (⟨v⟩ : OldCategory D Sc cutoff) :=
  (ideal D Sc cutoff v v).mkQ.comp (ELVPScalar.scalar D Sc cutoff v)

private def evaluateCoefficient (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (v : OldCategory D Sc cutoff) : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      End (M.obj v) :=
  (M.toFunctor.mapLinearMap k).comp (coefficientHomLinear D Sc cutoff v.word)

private def coefficientComponent (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (p : ZMod 2) (v : OldCategory D Sc cutoff) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] End (M.obj v) :=
  (evaluateCoefficient D Sc cutoff M v).comp
    (GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p)

private theorem component_mem (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (p : ZMod 2) (v : OldCategory D Sc cutoff) :
    coefficientComponent D Sc cutoff M p v a ∈ parity (R := k) (M.obj v) (M.obj v) p :=
  M.map_mem (coefficientEndomorphism_mem D Sc cutoff v.word
    (DirectSum.decompose (SKM.SYM.elvCoefficientParity D cutoff) a p).property)

private theorem component_naturality (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (p : ZMod 2)
    {v w : OldCategory D Sc cutoff} {q : ZMod 2} (f : v ⟶ w)
    (hf : f ∈ parity (R := k) v w q) :
    M.map f ≫ coefficientComponent D Sc cutoff M p w a =
      koszulSign p q • (coefficientComponent D Sc cutoff M p v a ≫ M.map f) := by
  let a0 := GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a
  have ha0 : a0 ∈ SKM.SYM.elvCoefficientParity D cutoff p :=
    (DirectSum.decompose (SKM.SYM.elvCoefficientParity D cutoff) a p).property
  have h := congrArg M.toFunctor.map
    (coefficientEndomorphism_slide D Sc cutoff ha0 v.word w.word f)
  rw [twist_of_mem p hf, Linear.comp_smul, M.toFunctor.map_smul] at h
  rw [koszulSign_smul (R := k)]
  simp only [Functor.map_comp] at h
  change M.map f ≫ coefficientComponent D Sc cutoff M p w a =
    sign k (p * q) • (coefficientComponent D Sc cutoff M p v a ≫ M.map f) at h
  exact h

/-- The full coefficient action as genuine old-supermodule maps, including
its inhomogeneous elements and both homogeneous components. -/
private def coefficientModuleLinear (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] End M where
  toFun a := Superfunctor.homMk {
    app p v := coefficientComponent D Sc cutoff M p v a
    app_mem := component_mem D Sc cutoff M a
    naturality := fun p _ _ _ f hf => component_naturality D Sc cutoff M a p f hf }
  map_add' a b := by
    apply Superfunctor.hom_ext
    intro p v
    exact (coefficientComponent D Sc cutoff M p v).map_add a b
  map_smul' r a := by
    apply Superfunctor.hom_ext
    intro p v
    exact (coefficientComponent D Sc cutoff M p v).map_smul r a

private theorem coefficient_projections_add (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) 0 a +
      GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) 1 a = a := by
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) (by simp) ?_ ?_ a
  · intro p a
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simp only [GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same _ a.property,
        DirectSum.decompose_of_mem_ne _ a.property (by decide : (0 : ZMod 2) ≠ 1), add_zero]
    · simp only [GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same _ a.property,
        DirectSum.decompose_of_mem_ne _ a.property (by decide : (1 : ZMod 2) ≠ 0), zero_add]
  · intro a b ha hb
    simpa only [map_add, add_add_add_comm] using congrArg₂ (· + ·) ha hb

/-- Total evaluation is exactly the original coefficient endomorphism
of the old category, with no reversed or unsigned replacement. -/
private theorem coefficientModuleLinear_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (v : OldCategory D Sc cutoff) :
    (coefficientModuleLinear D Sc cutoff M a).total v =
      M.map (X := v) (Y := v) (coefficientEndomorphism D Sc cutoff v.word a) := by
  change evaluateCoefficient D Sc cutoff M v
      (GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) 0 a) +
    evaluateCoefficient D Sc cutoff M v
      (GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) 1 a) = _
  rw [← map_add, coefficient_projections_add]
  rfl

private theorem module_hom_ext_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (f g : End M)
    (h : ∀ v, f.total v = g.total v) : f = g := by
  apply Superfunctor.hom_ext_parity
  · intro v
    have hh := congrArg (proj (R := k) 0) (h v)
    simpa only [SuperNatTrans.total, map_add, proj_of_mem (f.app_mem 0 v),
      proj_of_mem_ne (f.app_mem 1 v) (by decide : (1 : ZMod 2) ≠ 0),
      proj_of_mem (g.app_mem 0 v), proj_of_mem_ne (g.app_mem 1 v) (by decide : (1 : ZMod 2) ≠ 0),
      add_zero] using hh
  · intro v
    have hh := congrArg (proj (R := k) 1) (h v)
    simpa only [SuperNatTrans.total, map_add, proj_of_mem (f.app_mem 1 v),
      proj_of_mem_ne (f.app_mem 0 v) (by decide : (0 : ZMod 2) ≠ 1),
      proj_of_mem (g.app_mem 1 v), proj_of_mem_ne (g.app_mem 0 v) (by decide : (0 : ZMod 2) ≠ 1),
      zero_add] using hh

private theorem coefficient_one (v : OldCategory D Sc cutoff) :
    coefficientEndomorphism D Sc cutoff v.word (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) =
      (𝟙 v : v ⟶ v) := rfl

private theorem coefficient_comp (v : OldCategory D Sc cutoff)
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (coefficientEndomorphism D Sc cutoff v.word b : v ⟶ v) ≫
      coefficientEndomorphism D Sc cutoff v.word a = coefficientEndomorphism D Sc cutoff v.word (a * b) :=
  coefficientEndomorphism_comp D Sc cutoff v.word b a

/-- The genuine coefficient action on old supermodule endomorphisms is
an algebra map in the original multiplication order. -/
def coefficientModuleAction (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₐ[k] End M :=
  AlgHom.ofLinearMap (coefficientModuleLinear D Sc cutoff M) (by
    apply module_hom_ext_total D Sc cutoff M
    intro v
    rw [coefficientModuleLinear_total, coefficient_one]
    change M.toFunctor.map (𝟙 v) = (𝟙 M : End M).total v
    rw [M.toFunctor.map_id]
    exact (SuperNatTrans.id_total M.toFunctor v).symm) (by
    intro a b
    apply module_hom_ext_total D Sc cutoff M
    intro v
    rw [End.mul_def, Superfunctor.comp_total, coefficientModuleLinear_total,
      coefficientModuleLinear_total, coefficientModuleLinear_total, ← M.toFunctor.map_comp,
      coefficient_comp])

/-- Total evaluation is the original coefficient action on every old word. -/
theorem coefficientModuleAction_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (v : OldCategory D Sc cutoff) :
    (coefficientModuleAction D Sc cutoff M a).total v =
      M.map (X := v) (Y := v) (coefficientEndomorphism D Sc cutoff v.word a) :=
  coefficientModuleLinear_total D Sc cutoff M a v

variable (L : I × ℕ → ℕ)

end OddMath.QuiverHecke.ELVOld
