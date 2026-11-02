import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridComposition

/-! # The selected scalar comparison for two append inductions

The crossing comparison in DeformedActionAssembly §§5–6 and
DeformedMatrixComparison (2), (4) uses the composite of the selected
single-letter module isomorphisms. Its generator formula retains both old
coefficient arrows and the canonical order of the two append inductions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u

section EvenMap
variable {k : Type u} [CommRing k]
  {C A : Type u} [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)

private theorem probeEvenModuleMap_tensor (hf : f ∈ parity (R := k) _ _ 0)
    (v : C) (w : A) (g : (J).obj v ⟶ w) (b : M.obj v) :
    ((ELVOld.BalancedInduction.induction J).map f).total w
        (ELVOld.BalancedInduction.tensor J M.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor J N.toFunctor v g (f.total v b) := by
  change (ELVOld.BalancedInduction.moduleMap J f).total w
    (ELVOld.BalancedInduction.tensor J M.toFunctor v g b) = _
  have h := ELVOld.BalancedInduction.moduleMap_total_tensor J f w v g b
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) v
  simpa only [SuperNatTrans.total, hz, SVec.add_apply, SVec.zero_apply,
    add_zero, ELVOld.BalancedInduction.tensor_zero_right] using h

private def probeInducedIsoComp
    (A' : Superfunctor k A (SVec k))
    (e : A' ≅ (ELVOld.BalancedInduction.induction J).obj M) (t : M ≅ N) :
    A' ≅ (ELVOld.BalancedInduction.induction J).obj N :=
  e ≪≫ (ELVOld.BalancedInduction.induction J).mapIso t

private theorem probeInducedIsoComp_mem
    (A' : Superfunctor k A (SVec k))
    (e : A' ≅ (ELVOld.BalancedInduction.induction J).obj M) (t : M ≅ N)
    (he : e.hom ∈ parity (R := k) _ _ 0) (ht : t.hom ∈ parity (R := k) _ _ 0) :
    (probeInducedIsoComp J A' e t).hom ∈ parity (R := k) _ _ 0 := by
  simpa only [probeInducedIsoComp, Iso.trans_hom, Functor.mapIso_hom, zero_add] using
    comp_mem he (map_mem (ELVOld.BalancedInduction.induction J) ht)

private def probeInducedHomLinear (t : M ⟶ N) (w : A) :
    ELVOld.BalancedInduction.Obj J M.toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj J N.toFunctor w :=
  ((ELVOld.BalancedInduction.induction J).map t).total w

private theorem probeInducedHomLinear_tensor (t : M ⟶ N)
    (ht : t ∈ parity (R := k) _ _ 0)
    (v : C) (w : A) (g : (J).obj v ⟶ w) (b : M.obj v) :
    probeInducedHomLinear J t w (ELVOld.BalancedInduction.tensor J M.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor J N.toFunctor v g (t.total v b) :=
  probeEvenModuleMap_tensor J t ht v w g b

private theorem probeInducedIsoComp_apply
    (A' : Superfunctor k A (SVec k))
    (e : A' ≅ (ELVOld.BalancedInduction.induction J).obj M) (t : M ≅ N)
    (w : A) (b : A'.obj w) :
    (probeInducedIsoComp J A' e t).hom.total w b =
      probeInducedHomLinear J t.hom w (e.hom.total w b) := by
  rw [probeInducedIsoComp, Iso.trans_hom, Superfunctor.comp_total, SVec.comp_apply]
  rfl

private theorem probeInducedIsoComp_tensor
    (A' : Superfunctor k A (SVec k))
    (e : A' ≅ (ELVOld.BalancedInduction.induction J).obj M) (t : M ≅ N)
    (ht : t.hom ∈ parity (R := k) _ _ 0)
    (v : C) (w : A) (g : (J).obj v ⟶ w)
    (b : A'.obj w) (x : M.obj v) (y : N.obj v)
    (ho : e.hom.total w b = ELVOld.BalancedInduction.tensor J M.toFunctor v g x)
    (hi : t.hom.total v x = y) :
    (probeInducedIsoComp J A' e t).hom.total w b =
      ELVOld.BalancedInduction.tensor J N.toFunctor v g y := by
  exact (probeInducedIsoComp_apply J A' e t w b).trans
    ((congrArg (probeInducedHomLinear J t.hom w) ho).trans
      ((probeInducedHomLinear_tensor J t.hom ht v w g x).trans
        (congrArg (ELVOld.BalancedInduction.tensor J N.toFunctor v g) hi)))

private def probeInducedIsoCompLinear
    (A' : Superfunctor k A (SVec k))
    (e : A' ≅ (ELVOld.BalancedInduction.induction J).obj M) (t : M ≅ N) (w : A) :
    A'.obj w →ₗ[k] ELVOld.BalancedInduction.Obj J N.toFunctor w :=
  (probeInducedIsoComp J A' e t).hom.total w

private theorem probeInducedIsoCompLinear_tensor
    (A' : Superfunctor k A (SVec k))
    (e : A' ≅ (ELVOld.BalancedInduction.induction J).obj M) (t : M ≅ N)
    (ht : t.hom ∈ parity (R := k) _ _ 0)
    (v : C) (w : A) (g : J.obj v ⟶ w)
    (b : A'.obj w) (x : M.obj v) (y : N.obj v)
    (ho : e.hom.total w b = ELVOld.BalancedInduction.tensor J M.toFunctor v g x)
    (hi : t.hom.total v x = y) :
    probeInducedIsoCompLinear J A' e t w b =
      ELVOld.BalancedInduction.tensor J N.toFunctor v g y := by
  have hs := probeInducedIsoComp_tensor J A' e t ht v w g b x y ho hi
  set_option backward.dsimp.instances true in
    dsimp only [probeInducedIsoCompLinear, ELVOld.BalancedInduction.induction] at hs ⊢
  exact hs

end EvenMap

section MappedAppend
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (μ : List I)
  (R : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) μ) (SVec k))
  (hR : ProbeEvaluatesCoefficients D m Sc μ R)
  (M : Superfunctor k (OrdinaryContentCategory D Sc
    (probePolynomial (k := k) (probeDotExponent D) m) μ) (SVec k))
  (c : probeOrdinaryModuleSuperfunctor D Sc m μ R hR ≅ M) (j : I)
local notation "JR" => ELVOld.oldContentAppend D Sc (probeCutoff D m) μ j
local notation "TR" => probeOrdinaryAppend D Sc m μ j
local notation "QR" => probeOldOrdinaryFunctor D Sc m μ
local notation "UR" => probeOldOrdinaryFunctor D Sc m (j :: μ)

private def probeMappedAppendIso :
    probeOrdinaryModuleSuperfunctor D Sc m (j :: μ)
      (ELVOld.BalancedInduction.induced JR R)
      (probeOldInduced_evaluatesCoefficients D m Sc μ j R hR) ≅
        (ELVOld.BalancedInduction.induction TR).obj M :=
  probeInducedIsoComp TR _ (probeAppendOrdinaryModuleIso D Sc m μ R hR j) c

private def probeMappedAppendLinear
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (j :: μ)) :
    ELVOld.BalancedInduction.Obj JR R.toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj TR M.toFunctor ((UR).obj w) :=
  probeInducedHomLinear TR c.hom ((UR).obj w) ∘ₗ
    probeAppendComparisonLinear D Sc m μ R hR j w

private theorem probeMappedAppendLinear_tensor
    (hc : c.hom ∈ parity (R := k) _ _ 0)
    (v : ELVOld.OldContentCategory D Sc (probeCutoff D m) μ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (j :: μ))
    (g : (JR).obj v ⟶ w) (b : R.obj v) :
    probeMappedAppendLinear D Sc m μ R hR M c j w
      (ELVOld.BalancedInduction.tensor JR R.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor TR M.toFunctor ((QR).obj v) ((UR).map g)
        (c.hom.total ((QR).obj v) b) := by
  unfold probeMappedAppendLinear
  rw [LinearMap.comp_apply, probeAppendOrdinaryModuleIso_hom_tensor]
  exact probeInducedHomLinear_tensor TR c.hom hc ((QR).obj v) ((UR).obj w) ((UR).map g) b

private theorem probeMappedAppendLinear_eq
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (j :: μ))
    (b : ELVOld.BalancedInduction.Obj JR R.toFunctor w) :
    probeMappedAppendLinear D Sc m μ R hR M c j w b =
      (probeMappedAppendIso D Sc m μ R hR M c j).hom.total ((UR).obj w) b := by
  exact (probeInducedIsoComp_apply TR _
    (probeAppendOrdinaryModuleIso D Sc m μ R hR j) c ((UR).obj w) b).symm

end MappedAppend

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N) (i j : I)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "K" => ELVOld.oldContentAppend D Sc (probeCutoff D m) (i :: ν) j
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) j
local notation "L" => ELVOld.BalancedInduction.induced J N
local notation "hL" => probeOldInduced_evaluatesCoefficients D m Sc ν i N hN
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν N hN
local notation "Q₀" => probeOldOrdinaryFunctor D Sc m ν
local notation "Q₁" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "Q₂" => probeOldOrdinaryFunctor D Sc m (j :: i :: ν)

/-- The two selected one-letter comparisons, in their append order. -/
def probeDoubleAppendOrdinaryModuleIso :
    probeOrdinaryModuleSuperfunctor D Sc m (j :: i :: ν)
      (ELVOld.BalancedInduction.induced K L)
      (probeOldInduced_evaluatesCoefficients D m Sc (i :: ν) j L hL) ≅
    (ELVOld.BalancedInduction.induction S).obj ((ELVOld.BalancedInduction.induction T).obj O) :=
  probeMappedAppendIso D Sc m (i :: ν) L hL
    ((ELVOld.BalancedInduction.induction T).obj O)
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i) j

/-- The total component of the selected iterated comparison on literal coends. -/
def probeDoubleAppendComparisonLinear (w : ELVOld.OldContentCategory D Sc
    (probeCutoff D m) (j :: i :: ν)) :=
  probeMappedAppendLinear D Sc m (i :: ν) L hL
    ((ELVOld.BalancedInduction.induction T).obj O)
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i) j w

/-- The selected iterated comparison maps every nested tensor to the two
ordinary quotient tensors, without reordering either coefficient. -/
theorem probeDoubleAppendOrdinaryModuleIso_hom_tensor
    (s : ELVOld.OldContentCategory D Sc (probeCutoff D m) ν)
    (v : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν))
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (j :: i :: ν))
    (a : (J).obj s ⟶ v) (g : (K).obj v ⟶ w) (b : N.obj s) :
    probeDoubleAppendComparisonLinear D Sc m ν N hN i j w
      (ELVOld.BalancedInduction.tensor K (L).toFunctor v g
        (ELVOld.BalancedInduction.tensor J N.toFunctor s a b)) =
    ELVOld.BalancedInduction.tensor S ((ELVOld.BalancedInduction.induction T).obj O).toFunctor
      ((Q₁).obj v) ((Q₂).map g)
      (ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q₀).obj s) ((Q₁).map a) b) := by
  have ht := probeMappedAppendLinear_tensor D Sc m (i :: ν) L hL
    ((ELVOld.BalancedInduction.induction T).obj O)
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i) j
    (probeAppendOrdinaryModuleIso_hom_mem D Sc m ν N hN i)
    v w g (ELVOld.BalancedInduction.tensor J N.toFunctor s a b)
  have hi := probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN i s v a b
  exact ht.trans (congrArg (ELVOld.BalancedInduction.tensor S
    ((ELVOld.BalancedInduction.induction T).obj O).toFunctor ((Q₁).obj v) ((Q₂).map g)) hi)

end OddMath.QuiverHecke
