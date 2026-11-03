import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuotientInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridComposition

/-! # The literal equal-colour crossing under scalar probe specialization

The two-letter generator comparison in DeformedActionAssembly §§5–6 and
DeformedMatrixComparison (2), (4) retains the existing `crossLast` component,
its parity twist, and the prescribed extra minus on induced crossings.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "K" => ELVOld.oldContentAppend D Sc cut (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "Q₀" => probeOldOrdinaryFunctor D Sc m ν
local notation "Q₂" => probeOldOrdinaryFunctor D Sc m (i :: i :: ν)

/-- Restriction of the given old full-coefficient crossing to fixed content. -/
def probeOldContentEqualCross (v : ELVOld.OldContentCategory D Sc cut ν) :
    (J ⋙ K).obj v ⟶ (J ⋙ K).obj v :=
  ELVOld.CyclotomicCrossingTensor.equalCrossComponent D Sc cut i v.obj

theorem probeOldContentEqualCross_supernatural :
    IsSupernatural k (D.parity i * D.parity i) (probeOldContentEqualCross D Sc m ν i) where
  mem v := (ELVOld.CyclotomicCrossingTensor.equalCross_supernatural D Sc cut i).mem v.obj
  naturality hf :=
    (ELVOld.CyclotomicCrossingTensor.equalCross_supernatural D Sc cut i).naturality hf

/-- The same last crossing in the ordinary quotient, with successive append endpoints. -/
def probeOrdinaryEqualCross (v : OrdinaryContentCategory D Sc a ν) :
    (T ⋙ S).obj v ⟶ (T ⋙ S).obj v :=
  (cycHom D Sc a _ _).mkQ (crossLast D Sc v.word i i)

/-- Scalar specialization retains the literal crossing with its original normalization. -/
theorem probeOrdinaryEqualCross_old (v : ELVOld.OldContentCategory D Sc cut ν) :
    (Q₂).map (probeOldContentEqualCross D Sc m ν i v) =
      probeOrdinaryEqualCross D Sc m ν i ((Q₀).obj v) := by
  change (cycHom D Sc a _ _).mkQ (elvProbeScalarHom D m Sc _ _
    (ELVOld.affineUnit D Sc cut _ _ (crossLast D Sc v.obj.word i i))) = _
  rw [elvProbeScalarHom_affineUnit]
  rfl

/-- The two append functors have their literal commuting scalar square. -/
theorem probeOldOrdinaryFunctor_doubleAppend :
    (J ⋙ K) ⋙ Q₂ = Q₀ ⋙ (T ⋙ S) :=
  ELVOld.BalancedInduction.coendGrid_comp_eq J K Q₀
    (probeOldOrdinaryFunctor D Sc m (i :: ν)) Q₂ T S
    (probeOldOrdinaryFunctor_append D Sc m ν i)
    (probeOldOrdinaryFunctor_append D Sc m (i :: ν) i)

/-- Object transports of the literal square are identities on the same words. -/
theorem probeOldOrdinaryFunctor_doubleAppend_map
    {v w : ELVOld.OldContentCategory D Sc cut ν} (f : v ⟶ w) :
    (Q₂).map ((J ⋙ K).map f) = (T ⋙ S).map ((Q₀).map f) := by
  have h := (eqToHom (probeOldOrdinaryFunctor_doubleAppend D Sc m ν i)).naturality f
  simpa only [eqToHom_app, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.comp_map] using h

/-- The scalar crossing retains the full supernatural twist on ordinary arrows. -/
theorem probeOrdinaryEqualCross_supernatural :
    IsSupernatural k (D.parity i * D.parity i) (probeOrdinaryEqualCross D Sc m ν i) := by
  apply IsSupernatural.of_twist
  · intro v
    exact probeOrdinaryHomSpace_mk_mem D Sc m (crossLast_mem D Sc v.word i i)
  · intro v w f
    let v' := probeOrdinaryOldObject D Sc m ν v
    let w' := probeOrdinaryOldObject D Sc m ν w
    obtain ⟨fr, hfr⟩ := elvProbeOldHom_surjective D m Sc v.word w.word f
    let f' : v' ⟶ w' := fr
    have hf : (Q₀).map f' = f := hfr
    have h := congrArg (fun g => (Q₂).map g)
      ((probeOldContentEqualCross_supernatural D Sc m ν i).naturality_twist f')
    rw [Functor.map_comp, Functor.map_comp,
      probeOrdinaryEqualCross_old D Sc m ν i v',
      probeOrdinaryEqualCross_old D Sc m ν i w',
      probeOldOrdinaryFunctor_doubleAppend_map D Sc m ν i f',
      probeOldOrdinaryFunctor_doubleAppend_map D Sc m ν i
        (twist k (D.parity i * D.parity i) f'), map_twist, hf] at h
    exact h

variable (M : Superfunctor k (OrdinaryContentCategory D Sc
  (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))

/-- The composite scalar coend square intertwines the literal crossing,
including the full twist on an arbitrary coefficient arrow. -/
theorem probeCoendDoubleSquare_crossing
    (w : ELVOld.OldContentCategory D Sc cut (i :: i :: ν)) :
    ELVOld.BalancedInduction.coendSquareMap (J ⋙ K) Q₂ Q₀ (T ⋙ S)
        (probeOldOrdinaryFunctor_doubleAppend D Sc m ν i) M.toFunctor w ∘ₗ
      ELVOld.BalancedInduction.transformLinear
        (probeOldContentEqualCross_supernatural D Sc m ν i)
        (probeOrdinaryRestriction D Sc m ν M) w =
    ELVOld.BalancedInduction.transformLinear
        (probeOrdinaryEqualCross_supernatural D Sc m ν i) M ((Q₂).obj w) ∘ₗ
      ELVOld.BalancedInduction.coendSquareMap (J ⋙ K) Q₂ Q₀ (T ⋙ S)
        (probeOldOrdinaryFunctor_doubleAppend D Sc m ν i) M.toFunctor w := by
  apply ELVOld.BalancedInduction.coendSquareMap_transform
    (J ⋙ K) (J ⋙ K) Q₂ Q₀ (T ⋙ S) (T ⋙ S)
    (probeOldOrdinaryFunctor_doubleAppend D Sc m ν i)
    (probeOldOrdinaryFunctor_doubleAppend D Sc m ν i) M
    (probeOldContentEqualCross_supernatural D Sc m ν i)
    (probeOrdinaryEqualCross_supernatural D Sc m ν i)
  intro v
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    probeOrdinaryEqualCross_old D Sc m ν i v

/-- The prescribed extra minus is unchanged by scalar crossing transport. -/
theorem probeCoendDoubleSquare_signedCrossing
    (w : ELVOld.OldContentCategory D Sc cut (i :: i :: ν)) :
    ELVOld.BalancedInduction.coendSquareMap (J ⋙ K) Q₂ Q₀ (T ⋙ S)
        (probeOldOrdinaryFunctor_doubleAppend D Sc m ν i) M.toFunctor w ∘ₗ
      (-ELVOld.BalancedInduction.transformLinear
        (probeOldContentEqualCross_supernatural D Sc m ν i)
        (probeOrdinaryRestriction D Sc m ν M) w) =
    (-ELVOld.BalancedInduction.transformLinear
        (probeOrdinaryEqualCross_supernatural D Sc m ν i) M ((Q₂).obj w)) ∘ₗ
      ELVOld.BalancedInduction.coendSquareMap (J ⋙ K) Q₂ Q₀ (T ⋙ S)
        (probeOldOrdinaryFunctor_doubleAppend D Sc m ν i) M.toFunctor w := by
  rw [LinearMap.comp_neg, LinearMap.neg_comp,
    probeCoendDoubleSquare_crossing D Sc m ν i M w]

end OddMath.QuiverHecke
