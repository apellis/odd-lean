import OddMath.QuiverHecke.CyclotomicAction.AppendContent.AppendDot
import OddMath.QuiverHecke.CyclotomicAction.ContentModules.AppendQuotientTensors
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate.InductionSquareTensors

/-!
# Weighted append

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Literal tensor generators of weighted append comparison

For DeformedActionAssembly §§5–6 and STATUS critical-chain item 2,
the selected old/truncated comparison preserves the input vector and sends
every old coend arrow to its literal quotient. No homogeneity restriction
is imposed on either tensor factor.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "F" => BalancedInduction.induced J RM
local notation "hF" => induced_killsWeightedCoefficients D Sc cutoff N i RM
  (weightedRestriction_kills D Sc cutoff N M)

private def appendQuotientCounit : (BalancedInduction.induction Q).obj RM ⟶ M :=
  (quotientInductionCounitIso D Sc cutoff N M).hom

local notation "S" => BalancedInduction.squareLinear J Q Q T
  (oldAppend_truncate D Sc cutoff N i) RM M (appendQuotientCounit D Sc cutoff N M)

private theorem appendWeightedModuleIso_hom_factor :
    (appendWeightedModuleIso D Sc cutoff N i M).hom =
      (quotientInducedWeightedModuleIso D Sc cutoff N F hF).inv ≫
        BalancedInduction.squareComparison J Q Q T (oldAppend_truncate D Sc cutoff N i)
          RM M (quotientInductionCounitIso D Sc cutoff N M).hom := by
  rw [BalancedInduction.squareComparison_eq]
  rfl

/-- The chosen comparison on the literal old and truncated coends.
The endpoint module instances are fixed before generator evaluation. -/
def weightedAppendComparisonLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (RM).toFunctor w →ₗ[k]
      BalancedInduction.Obj T M.toFunctor ((Q).obj w) :=
  (appendWeightedModuleIso D Sc cutoff N i M).hom.total ((Q).obj w)

private def appendQuotientInverseLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (RM).toFunctor w →ₗ[k]
      BalancedInduction.Obj Q (F).toFunctor ((Q).obj w) :=
  (quotientInducedWeightedModuleIso D Sc cutoff N F hF).inv.total ((Q).obj w)

private theorem weightedAppendComparisonLinear_factor (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M w =
      S ((Q).obj w) ∘ₗ appendQuotientInverseLinear D Sc cutoff N i M w := by
  exact (BalancedInduction.total_linear_congr
    (appendWeightedModuleIso_hom_factor D Sc cutoff N i M) ((Q).obj w)).trans
      (BalancedInduction.composition_total_linear _ _ ((Q).obj w))

/-- The selected five-isomorphism comparison sends the old tensor to the
truncated tensor with exactly the quotient arrow and unchanged vector. -/
theorem appendWeightedModuleIso_hom_tensor
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w)
    (b : M.obj ((Q).obj s)) :
    weightedAppendComparisonLinear D Sc cutoff N i M w
      (BalancedInduction.tensor J (RM).toFunctor s g b) =
      BalancedInduction.tensor T M.toFunctor ((Q).obj s) ((Q).map g) b := by
  have h₁ : appendQuotientInverseLinear D Sc cutoff N i M w
      (BalancedInduction.tensor J (RM).toFunctor s g b) =
      BalancedInduction.tensor Q (F).toFunctor w (𝟙 ((Q).obj w))
        (BalancedInduction.tensor J (RM).toFunctor s g b) :=
    quotientInducedWeightedModuleIso_inv_tensor D Sc cutoff N F hF ((Q).obj w)
      (BalancedInduction.tensor J (RM).toFunctor s g b)
  have h₂ := BalancedInduction.squareLinear_tensor J Q Q T
    (oldAppend_truncate D Sc cutoff N i) RM M (appendQuotientCounit D Sc cutoff N M)
    (quotientInductionCounitIso_hom_mem D Sc cutoff N M) s w g b
  have hs : S ((Q).obj w)
      (BalancedInduction.tensor Q (F).toFunctor w (𝟙 ((Q).obj w))
        (BalancedInduction.tensor J (RM).toFunctor s g b)) =
      BalancedInduction.tensor T M.toFunctor ((Q).obj s) ((Q).map g) b := by
    have hi : eqToHom (congrArg
        (fun H : OldCategory D Sc cutoff ⥤ TruncatedCategory D Sc cutoff N => H.obj s)
        (oldAppend_truncate D Sc cutoff N i)).symm ≫ (Q).map g = (Q).map g := by
      change 𝟙 _ ≫ (Q).map g = (Q).map g
      exact Category.id_comp _
    have hb : (appendQuotientCounit D Sc cutoff N M).app 0 ((Q).obj s)
        (BalancedInduction.unit Q (RM).toFunctor s b) = b := by
      change BalancedInduction.counit Q M.toFunctor ((Q).obj s)
        (BalancedInduction.unit Q (Q ⋙ M.toFunctor) s b) = b
      exact LinearMap.congr_fun (BalancedInduction.counit_unit Q M.toFunctor s) b
    exact h₂.trans (congrArg₂
      (fun z x => BalancedInduction.tensor T M.toFunctor ((Q).obj s) z x) hi hb)
  rw [weightedAppendComparisonLinear_factor, LinearMap.comp_apply]
  exact (congrArg (S ((Q).obj w)) h₁).trans hs

/-- The same selected comparison preserves the literal coend units. -/
theorem appendWeightedModuleIso_hom_unit
    (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj s)
      (BalancedInduction.unit J (RM).toFunctor s b) =
      BalancedInduction.unit T M.toFunctor ((Q).obj s) b := by
  have h := appendWeightedModuleIso_hom_tensor D Sc cutoff N i M s ((J).obj s) (𝟙 _) b
  have hin := congrArg (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj s))
    (BalancedInduction.unit_apply J (RM).toFunctor s b)
  have hout := BalancedInduction.unit_apply T M.toFunctor ((Q).obj s) b
  exact hin.trans ((h.trans (congrArg
    (fun z => BalancedInduction.tensor T M.toFunctor ((Q).obj s) z b)
    ((Q).map_id ((J).obj s)))).trans hout.symm)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Ordinary adjunction under weighted append comparison

DeformedActionAssembly §§5–6 and STATUS critical-chain item 2 require
compatibility of the chosen
old/truncated append comparison with the ordinary adjunction maps.
Restriction commutes with the actual quotient by an even comparison
whose components are identities. The selected append comparison
intertwines the literal counits after that restriction comparison.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
section CounitCarriers
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (M : Superfunctor k D (SVec k))

/-- The ordinary counit on the literal coend of the restricted module. -/
def restrictionCounitLinear (w : D) :
    BalancedInduction.Obj J ((BalancedInduction.restriction J).obj M).toFunctor w →ₗ[k] M.obj w :=
  BalancedInduction.counit J M.toFunctor w

/-- This carrier realization is the prescribed ordinary counit. -/
theorem restrictionCounitLinear_apply (w : D)
    (b : BalancedInduction.Obj J ((BalancedInduction.restriction J).obj M).toFunctor w) :
    restrictionCounitLinear J M w b = BalancedInduction.counit J M.toFunctor w b := rfl

/-- The canonical counit evaluates its exact tensor arrow. -/
theorem restrictionCounitLinear_tensor (v : C) (w : D) (g : J.obj v ⟶ w)
    (b : M.obj (J.obj v)) :
    restrictionCounitLinear J M w
      (BalancedInduction.tensor J ((BalancedInduction.restriction J).obj M).toFunctor v g b) =
      M.map g b :=
  BalancedInduction.counit_tensor J M.toFunctor w v g b
end CounitCarriers

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- Pullback of truncated restriction and old restriction of pullback
are compared on the same module vector spaces. -/
def weightedAppendRestrictionIso :
    weightedRestriction D Sc cutoff N ((BalancedInduction.restriction T).obj M) ≅
      (BalancedInduction.restriction J).obj (weightedRestriction D Sc cutoff N M) :=
  moduleIsoOfEvenNatIso _ _
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun {v w} f => by
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
      rfl))
    (fun _ => id_mem _) (fun _ => id_mem _)

@[simp] theorem weightedAppendRestrictionIso_hom_app
    (p : ZMod 2) (s : OldCategory D Sc cutoff) :
    (weightedAppendRestrictionIso D Sc cutoff N i M).hom.app p s =
      if p = 0 then LinearMap.id else 0 := rfl

theorem weightedAppendRestrictionIso_hom_mem :
    (weightedAppendRestrictionIso D Sc cutoff N i M).hom ∈ parity (R := k) _ _ 0 := by
  unfold weightedAppendRestrictionIso
  exact moduleIsoOfEvenNatIso_hom_mem _ _ _ _ _

/-- The selected old/truncated append comparison carries the literal
ordinary counit to the truncated counit. The old-side source is identified
by the canonical even restriction-square comparison above. -/
theorem appendWeightedModuleIso_hom_counit (w : OldCategory D Sc cutoff) :
    restrictionCounitLinear T M ((Q).obj w) ∘ₗ
        weightedAppendComparisonLinear D Sc cutoff N i
          ((BalancedInduction.restriction T).obj M) w =
      restrictionCounitLinear J (weightedRestriction D Sc cutoff N M) w ∘ₗ
        BalancedInduction.mapComponent J
          (weightedAppendRestrictionIso D Sc cutoff N i M).hom 0 w := by
  apply BalancedInduction.hom_ext
  intro s g b
  let A := weightedRestriction D Sc cutoff N ((BalancedInduction.restriction T).obj M)
  let B := (BalancedInduction.restriction J).obj (weightedRestriction D Sc cutoff N M)
  let e := weightedAppendRestrictionIso D Sc cutoff N i M
  have ht := appendWeightedModuleIso_hom_tensor D Sc cutoff N i
    ((BalancedInduction.restriction T).obj M) s w g b
  have hT := restrictionCounitLinear_tensor T M ((Q).obj s) ((Q).obj w) ((Q).map g) b
  have hm := BalancedInduction.mapComponent_tensor J e.hom 0 w s g b
  have hb : e.hom.app 0 s b = b := rfl
  have hx : BalancedInduction.mapComponent J e.hom 0 w
      (BalancedInduction.tensor J A.toFunctor s g b) =
      BalancedInduction.tensor J B.toFunctor s g b := by
    refine hm.trans ?_
    exact congrArg₂ (fun z x => BalancedInduction.tensor J B.toFunctor s z x)
      (twist_zero g) hb
  have hJ := restrictionCounitLinear_tensor J (weightedRestriction D Sc cutoff N M) s w g b
  have hleft := (congrArg (restrictionCounitLinear T M ((Q).obj w)) ht).trans hT
  have hright :=
    (congrArg (restrictionCounitLinear J (weightedRestriction D Sc cutoff N M) w) hx).trans hJ
  exact hleft.trans hright.symm

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Weighted quotient comparison for a pair of appended strands

The same-colour crossing and mate comparison in DeformedActionAssembly §5
and DeformedMatrixComparison (2), (4) needs the canonical two-strand append
square. The pair preserves the complete weighted coefficient annihilator,
including odd generators, before the two canonical induction flattenings
are attached. The final comparison with iterated induction is separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i j : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "K" => CyclotomicCrossingTensor.append D Sc cutoff j
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "U" => truncatedAppend D Sc cutoff N [j]

/-- Successive old appends preserve the literal full coefficient basis. -/
theorem pairAppend_oldCoefficientBasis (v : List I) (a : SKM.SYM.CoefficientIndex D) :
    (J ⋙ K).map (oldCoefficientBasis D Sc cutoff v a) =
      oldCoefficientBasis D Sc cutoff (v ++ [i] ++ [j]) a := by
  rw [Functor.comp_map, append_oldCoefficientBasis, append_oldCoefficientBasis]

/-- The literal quotient square for two successive appends; no list-word
reassociation or content equivalence is inserted. -/
theorem pairAppend_truncate : (J ⋙ K) ⋙ Q = Q ⋙ (T ⋙ U) := by
  refine Functor.hext (F := (J ⋙ K) ⋙ Q) (G := Q ⋙ (T ⋙ U)) (fun _ => rfl) ?_
  intro v w f
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
  rfl

private theorem coefficient_slide_object
    {v w : OldCategory D Sc cutoff} (a : SKM.SYM.CoefficientIndex D) (g : v ⟶ w) :
    g ≫ oldCoefficientBasis D Sc cutoff w.word a =
      oldCoefficientBasis D Sc cutoff v.word a ≫ twist k (a.2.card : ZMod 2) g := by
  cases v
  cases w
  exact oldCoefficientBasis_slide D Sc cutoff _ _ a g

private theorem induced_kills_of_coefficient_image
    (L : OldCategory D Sc cutoff ⥤ OldCategory D Sc cutoff)
    [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (hL : ∀ (v : OldCategory D Sc cutoff) (a : SKM.SYM.CoefficientIndex D),
      L.map (oldCoefficientBasis D Sc cutoff v.word a) =
        oldCoefficientBasis D Sc cutoff (L.obj v).word a)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    KillsWeightedCoefficients D Sc cutoff N (BalancedInduction.induced L M) := by
  intro w a ha
  change BalancedInduction.postcompose L M.toFunctor
    (oldCoefficientBasis D Sc cutoff w a) = 0
  apply BalancedInduction.hom_ext
  intro v g b
  rw [BalancedInduction.postcompose_tensor, coefficient_slide_object, ← hL v a,
    BalancedInduction.balance]
  have hz : M.toFunctor.map (oldCoefficientBasis D Sc cutoff v.word a) = 0 := hM v.word a ha
  rw [hz, LinearMap.zero_apply]
  exact BalancedInduction.tensor_zero_right L M.toFunctor v _

/-- Induction along the successive-append functor preserves the exact
weighted coefficient annihilator. The input is any annihilated old module. -/
theorem pairInduced_killsWeightedCoefficients
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    KillsWeightedCoefficients D Sc cutoff N (BalancedInduction.induced (J ⋙ K) M) :=
  induced_kills_of_coefficient_image D Sc cutoff N (J ⋙ K)
    (fun v a => pairAppend_oldCoefficientBasis D Sc cutoff i j v.word a) M hM

section Comparison
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "JP" => J ⋙ K
local notation "TP" => T ⋙ U
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "FP" => BalancedInduction.induced JP RM
local notation "hFP" => pairInduced_killsWeightedCoefficients D Sc cutoff N i j RM
  (weightedRestriction_kills D Sc cutoff N M)

private def pairQuotientCounit : (BalancedInduction.induction Q).obj RM ⟶ M :=
  (quotientInductionCounitIso D Sc cutoff N M).hom


end Comparison

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The equal-colour crossing through the weighted quotient

DeformedActionAssembly §5 and DeformedMatrixComparison (2), (4) require the
last-strand crossing, with the prescribed sign, on the chosen two-induction
comparison. The literal quotient of `crossLast` is identified with the
existing `crossTwo` append component under word associativity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- The crossing at the last two positions on successive singleton appends. -/
def truncatedEqualCrossComponent (s : TruncatedCategory D Sc cutoff N) :
    (T ⋙ T).obj s ⟶ (T ⋙ T).obj s :=
  (truncatedIdeal D Sc cutoff N _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i))

/-- Quotienting retains the literal affine crossing. -/
theorem oldTruncateFunctor_map_equalCross (s : OldCategory D Sc cutoff) :
    (Q).map (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s) =
      truncatedEqualCrossComponent D Sc cutoff N i ((Q).obj s) := rfl

/-- Full coefficient supernaturality descends from the old crossing. -/
theorem truncatedEqualCross_supernatural :
    IsSupernatural k (D.parity i * D.parity i)
      (truncatedEqualCrossComponent D Sc cutoff N i) := by
  apply IsSupernatural.of_twist
  · intro s
    exact Submodule.mem_map_of_mem
      (ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word i i))
  · intro s t f
    obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N s.word t.word).mkQ_surjective f
    let f' : (⟨s.word⟩ : OldCategory D Sc cutoff) ⟶ ⟨t.word⟩ :=
      (ideal D Sc cutoff s.word t.word).mkQ a
    have h := congrArg (fun g => (Q).map g)
      ((CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i).naturality_twist f')
    simp only [Functor.map_comp, map_twist] at h
    rw [map_twist]
    exact h

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Dot transport by weighted append comparison

The generator compatibility in DeformedActionAssembly §§5–6 and STATUS
critical-chain item 2 uses
the selected five-isomorphism comparison. It intertwines the old signed
coend dot with the literal truncated appended dot, retaining the parity
twist of arbitrary old arrows.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The old dot maps to the same appended affine diagram in the literal
weighted quotient. -/
theorem oldTruncateFunctor_map_appendDot (s : OldCategory D Sc cutoff) :
    (Q).map (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i s) =
      truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0) ((Q).obj s) := rfl

/-- The chosen weighted append comparison intertwines the actual signed
old coend dot and the prescribed truncated dot on every output word.
No homogeneous-arrow or homogeneous-vector restriction is needed. -/
theorem appendWeightedModuleIso_hom_dot (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M w ∘ₗ
        CyclotomicCrossingTensor.inductionDot D Sc cutoff i RM w =
      BalancedInduction.transformLinear
        (truncatedAppendComponent_supernatural D Sc cutoff N (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M ((Q).obj w) ∘ₗ
        weightedAppendComparisonLinear D Sc cutoff N i M w := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply,
    CyclotomicCrossingTensor.inductionDot_tensor,
    appendWeightedModuleIso_hom_tensor, BalancedInduction.transformLinear_tensor]
  rw [(Q).map_comp, map_twist, oldTruncateFunctor_map_appendDot]
  rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Iterated weighted append comparison

DeformedActionAssembly §5 and DeformedMatrixComparison (2), (4) use the
crossing on iterated induction. The comparison is obtained from the chosen
pair comparison by descending the old induction flattening and undoing the
truncated flattening. Thus its flattening coherence uses the prescribed maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

variable (i j : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "K" => CyclotomicCrossingTensor.append D Sc cutoff j
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "U" => truncatedAppend D Sc cutoff N [j]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "FI" => Functor.obj (BalancedInduction.induction J ⋙ BalancedInduction.induction K) RM
local notation "FP" => BalancedInduction.induced (J ⋙ K) RM
local notation "hFP" => pairInduced_killsWeightedCoefficients D Sc cutoff N i j RM
  (weightedRestriction_kills D Sc cutoff N M)

/-- The twice-induced old module satisfies the complete weighted annihilator. -/
theorem doubleInduced_killsWeightedCoefficients :
    KillsWeightedCoefficients D Sc cutoff N FI :=
  induced_killsWeightedCoefficients D Sc cutoff N j _
    (induced_killsWeightedCoefficients D Sc cutoff N i RM
      (weightedRestriction_kills D Sc cutoff N M))

end OddMath.QuiverHecke.ELV
end

end
