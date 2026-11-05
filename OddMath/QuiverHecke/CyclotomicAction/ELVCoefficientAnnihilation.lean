import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedInduction

/-! # Coefficient annihilators under old append induction and restriction

The coefficient-power quotient in `SwappedNondegeneracy.md`, §2 requires
preservation of its own annihilator, rather than identification with a
weighted coefficient quotient. These results apply to every homogeneous
full ELV coefficient, including the even power generators of that ideal.
They retain the signed coefficient slide and actual balanced induction.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- A full ELV coefficient acting at an arbitrary old word. -/
def coefficientEndomorphism (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨v⟩ :=
  (ideal D Sc cutoff v v).mkQ (ELVPScalar.scalar D Sc cutoff v a)

theorem coefficientEndomorphism_mem (v : List I) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    coefficientEndomorphism D Sc cutoff v a ∈
      parity (R := k) (⟨v⟩ : OldCategory D Sc cutoff) ⟨v⟩ p :=
  Submodule.mem_map_of_mem (ELVPScalar.scalar_mem D Sc cutoff v ha)

/-- Coefficient endomorphisms compose in the opposite multiplication
order. This order is material when two different odd colours occur. -/
theorem coefficientEndomorphism_comp (v : List I)
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    oldComp D Sc cutoff v v v (coefficientEndomorphism D Sc cutoff v a)
      (coefficientEndomorphism D Sc cutoff v b) =
      coefficientEndomorphism D Sc cutoff v (b * a) := by
  change (ideal D Sc cutoff v v).mkQ
    (ELVPScalar.scalar D Sc cutoff v a ≫ ELVPScalar.scalar D Sc cutoff v b) = _
  congr 1
  change BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff v) a (𝟙 _) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff v) b (𝟙 _) = _
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [twist_id, Category.comp_id, ← BoxProd.tmulHom_add_left,
    ← Preadditive.add_comp, proj_add_proj]
  rfl

/-- The full coefficient parity, rather than only affine parity, controls
the slide through an arbitrary old morphism. -/
theorem coefficientEndomorphism_slide {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p)
    (v w : List I) (f : (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨w⟩) :
    f ≫ coefficientEndomorphism D Sc cutoff w a =
      coefficientEndomorphism D Sc cutoff v a ≫ twist k p f := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v w).mkQ_surjective f
  have h := congrArg ((ideal D Sc cutoff v w).mkQ)
    (ELVPScalar.scalar_slide_homogeneous D Sc cutoff ha f)
  rw [oldQuotient_twist]
  exact h

@[simp] theorem append_coefficientEndomorphism (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (CyclotomicCrossingTensor.append D Sc cutoff i).map
      (X := ⟨v⟩) (Y := ⟨v⟩) (coefficientEndomorphism D Sc cutoff v a) =
      coefficientEndomorphism D Sc cutoff (v ++ [i]) a := by
  change (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
    (rightContext D Sc cutoff [i] v v (ELVPScalar.scalar D Sc cutoff v a)) = _
  rw [ELVPScalar.rightContext_scalar]
  rfl

/-- An old module annihilates this coefficient at every word. -/
def KillsCoefficient (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) : Prop :=
  ∀ v : List I, M.map (X := ⟨v⟩) (Y := ⟨v⟩)
    (coefficientEndomorphism D Sc cutoff v a) = 0

/-- Restriction preserves annihilation by each full coefficient. -/
theorem restriction_killsCoefficient (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (hM : KillsCoefficient D Sc cutoff M a) :
    KillsCoefficient D Sc cutoff
      ((BalancedInduction.restriction (CyclotomicCrossingTensor.append D Sc cutoff i)).obj M) a := by
  intro v
  change M.map (X := ⟨v ++ [i]⟩) (Y := ⟨v ++ [i]⟩)
    ((CyclotomicCrossingTensor.append D Sc cutoff i).map
      (X := ⟨v⟩) (Y := ⟨v⟩) (coefficientEndomorphism D Sc cutoff v a)) = 0
  rw [append_coefficientEndomorphism]
  exact hM _

/-- Actual balanced induction preserves the annihilator of every
homogeneous coefficient. No comparison with a weighted ideal is used. -/
theorem induced_killsCoefficient (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p)
    (hM : KillsCoefficient D Sc cutoff M a) :
    KillsCoefficient D Sc cutoff
      (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i) M) a := by
  intro w
  let J := CyclotomicCrossingTensor.append D Sc cutoff i
  change BalancedInduction.postcompose J M.toFunctor
    (coefficientEndomorphism D Sc cutoff w a) = 0
  apply BalancedInduction.hom_ext
  rintro ⟨v⟩ h m
  rw [BalancedInduction.postcompose_tensor, coefficientEndomorphism_slide D Sc cutoff ha]
  have hc : coefficientEndomorphism D Sc cutoff (v ++ [i]) a =
      J.map (X := ⟨v⟩) (Y := ⟨v⟩) (coefficientEndomorphism D Sc cutoff v a) :=
    (append_coefficientEndomorphism D Sc cutoff i v a).symm
  rw [hc, BalancedInduction.balance]
  have hz : M.toFunctor.map (X := ⟨v⟩) (Y := ⟨v⟩)
      (coefficientEndomorphism D Sc cutoff v a) = 0 := hM v
  rw [hz, LinearMap.zero_apply, BalancedInduction.tensor_zero_right]
  rfl

/-- In particular the defining powers of an even coefficient ideal remain
annihilating after actual induction. These are the paper's generators,
without replacing them by a larger weighted ideal. -/
theorem induced_killsEvenPower (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff 0) (L : ℕ)
    (hM : KillsCoefficient D Sc cutoff M (a ^ L)) :
    KillsCoefficient D Sc cutoff
      (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i) M) (a ^ L) := by
  have hp : a ^ L ∈ SKM.SYM.elvCoefficientParity D cutoff 0 := by
    clear hM
    induction L with
    | zero => simpa only [pow_zero] using
        (SetLike.GradedOne.one_mem :
          (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
            SKM.SYM.elvCoefficientParity D cutoff 0)
    | succ L ih => simpa only [pow_succ, add_zero] using
        SetLike.mul_mem_graded ih ha
  exact induced_killsCoefficient D Sc cutoff i M hp hM

end OddMath.QuiverHecke.ELVOld
