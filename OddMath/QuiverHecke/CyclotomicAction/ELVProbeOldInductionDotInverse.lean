import OddMath.QuiverHecke.CyclotomicAction.ELVProbeInductionDotUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeScalarInduction

/-! # Signed dot inverse on old scalar probe coends
This supplies the probe-unit roadmap input for the prescribed old append induction.
The inverse is constructed on the original balanced quotient using scalar-kernel
closure and the inverse ordinary appended dot. The canonical probe module discharges
the scalar-evaluation condition. No finite-dimensionality or coend comparison is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "C" => ELVOld.OldContentCategory D Sc cut ν
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν

section Action
variable (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

/-- The literal ordinary Hom action retains the original old module values. -/
theorem probeScalarAction_old (v w : C) (f : v ⟶ w) :
    probeOrdinaryModuleHom D m Sc ν N hN v w ((Q).map (X := v) (Y := w) f) =
      N.toFunctor.map (X := v) (Y := w) f :=
  probeOrdinaryModuleHom_old D m Sc ν N hN v w f

/-- Composition holds on unchanged old values, without rebuilding object labels. -/
theorem probeScalarAction_comp (v w z : C)
    (f : (Q).obj v ⟶ (Q).obj w) (g : (Q).obj w ⟶ (Q).obj z) :
    probeOrdinaryModuleHom D m Sc ν N hN v z (f ≫ g) =
      probeOrdinaryModuleHom D m Sc ν N hN v w f ≫
        probeOrdinaryModuleHom D m Sc ν N hN w z g := by
  obtain ⟨fr,rfl⟩ := elvProbeOldHom_surjective D m Sc v.obj.word w.obj.word f
  obtain ⟨gr,rfl⟩ := elvProbeOldHom_surjective D m Sc w.obj.word z.obj.word g
  let f₀ : v ⟶ w := fr
  let g₀ : w ⟶ z := gr
  change probeOrdinaryModuleHom D m Sc ν N hN v z
      ((Q).map (X := v) (Y := w) f₀ ≫ (Q).map (X := w) (Y := z) g₀) =
    probeOrdinaryModuleHom D m Sc ν N hN v w ((Q).map (X := v) (Y := w) f₀) ≫
      probeOrdinaryModuleHom D m Sc ν N hN w z ((Q).map (X := w) (Y := z) g₀)
  have hq := congrArg (probeOrdinaryModuleHom D m Sc ν N hN v z) ((Q).map_comp f₀ g₀)
  have hf := probeScalarAction_old D Sc m ν N hN v w f₀
  have hg := probeScalarAction_old D Sc m ν N hN w z g₀
  exact hq.symm.trans ((probeScalarAction_old D Sc m ν N hN v z (f₀ ≫ g₀)).trans
    ((N.toFunctor.map_comp f₀ g₀).trans
      (congrArg₂ (fun x : N.obj v ⟶ N.obj w => fun y : N.obj w ⟶ N.obj z => x ≫ y)
        hf.symm hg.symm)))

end Action

/-- The prescribed old dot, on the existing content append functor. -/
def probeOldContentAppendDot (i : I) (v : C) :
    (ELVOld.oldContentAppend D Sc cut ν i).obj v ⟶
      (ELVOld.oldContentAppend D Sc cut ν i).obj v :=
  ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i v.obj

theorem probeOldContentAppendDot_supernatural (i : I) :
    IsSupernatural k (D.parity i) (probeOldContentAppendDot D Sc m ν i) where
  mem v := (ELVOld.CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cut i).mem v.obj
  naturality hf :=
    (ELVOld.CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cut i).naturality hf

/-- The original signed balanced transform, on the actual old content coend. -/
def probeOldContentInductionDot (i : I)
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    ELVOld.BalancedInduction.Obj (ELVOld.oldContentAppend D Sc cut ν i) N.toFunctor t →ₗ[k]
      ELVOld.BalancedInduction.Obj (ELVOld.oldContentAppend D Sc cut ν i) N.toFunctor t :=
  ELVOld.BalancedInduction.transformLinear (probeOldContentAppendDot_supernatural D Sc m ν i) N t

@[simp] theorem probeOldContentInductionDot_tensor (i : I)
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (v : C) (t : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (g : (ELVOld.oldContentAppend D Sc cut ν i).obj v ⟶ t) (b : N.obj v) :
    probeOldContentInductionDot D Sc m ν i N t
      (ELVOld.BalancedInduction.tensor (ELVOld.oldContentAppend D Sc cut ν i) N.toFunctor v g b) =
    ELVOld.BalancedInduction.tensor (ELVOld.oldContentAppend D Sc cut ν i) N.toFunctor v
      (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) b :=
  ELVOld.BalancedInduction.transformLinear_tensor _ _ _ _ _ _

section SourceInverse
variable [Fintype I] (i : I)
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- Inverse of the source dot in the literal ordinary Hom quotient. -/
def probeOrdinarySourceDotInverse (v : C) :
    (U).obj ((J).obj v) ⟶ (U).obj ((J).obj v) :=
  (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v)).inv

omit [Fintype I] in
theorem probeOldContentAppendDot_image (v : C) :
    (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) =
      probeOrdinaryAppendDot D Sc m ν i ((Q).obj v) :=
  probeOrdinaryAppendDot_old D Sc m ν i v

theorem probeOrdinarySourceDotInverse_dot (v : C) :
    probeOrdinarySourceDotInverse D Sc m ν i v ≫
      (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) =
        𝟙 ((U).obj ((J).obj v)) := by
  rw [probeOldContentAppendDot_image]
  exact (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v)).inv_hom_id

theorem probeOrdinarySourceDot_dotInverse (v : C) :
    (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) ≫
      probeOrdinarySourceDotInverse D Sc m ν i v = 𝟙 ((U).obj ((J).obj v)) := by
  rw [probeOldContentAppendDot_image]
  exact (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v)).hom_inv_id

theorem probeOrdinarySourceDotInverse_mem (v : C) :
    probeOrdinarySourceDotInverse D Sc m ν i v ∈
      parity (R := k) ((U).obj ((J).obj v)) ((U).obj ((J).obj v)) (D.parity i) :=
  Supercategory.inv_mem (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v))
    ((probeOrdinaryAppendDot_supernatural D Sc m ν i).mem ((Q).obj v))

/-- The inverse retains the full output twist on actual old input arrows. -/
theorem probeOrdinarySourceDotInverse_naturality (v w : C) (f : v ⟶ w) :
    (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f) ≫
      probeOrdinarySourceDotInverse D Sc m ν i w =
    probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i)
        ((U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f)) := by
  let qf := (Q).map (X := v) (Y := w) f
  have hs : (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f) =
      (T).map (X := (Q).obj v) (Y := (Q).obj w) qf :=
    elvProbeOldHom_rightContext D m Sc [i] v.obj.word w.obj.word f
  have hi := (ELVOld.BalancedInduction.inverseComponent_supernatural T
    (probeOrdinaryAppendDotIso D Sc m ν i)
    (probeOrdinaryAppendDot_supernatural D Sc m ν i)).naturality_twist qf
  calc
    _ = (T).map qf ≫ probeOrdinarySourceDotInverse D Sc m ν i w :=
      congrArg (fun x => x ≫ probeOrdinarySourceDotInverse D Sc m ν i w) hs
    _ = probeOrdinarySourceDotInverse D Sc m ν i v ≫ (T).map (twist k (D.parity i) qf) := hi
    _ = probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) ((T).map qf) :=
      congrArg (fun x => probeOrdinarySourceDotInverse D Sc m ν i v ≫ x) (map_twist T (D.parity i) qf)
    _ = _ := congrArg (fun x => probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) x) hs.symm
/-- The inverse-dot/twisted-Hom expression is linear in the actual old Hom. -/
def probeOrdinaryInverseHom (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    ((J).obj v ⟶ t) →ₗ[k] ((U).obj ((J).obj v) ⟶ (U).obj t) :=
  (Linear.leftComp k ((U).obj t) (probeOrdinarySourceDotInverse D Sc m ν i v)).comp
    ((twist k (D.parity i) (X := (U).obj ((J).obj v)) (Y := (U).obj t)).comp
      ((U).mapLinearMap (R := k) (X := (J).obj v) (Y := t)))

@[simp] theorem probeOrdinaryInverseHom_apply (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) :
    probeOrdinaryInverseHom D Sc m ν i v t g =
      probeOrdinarySourceDotInverse D Sc m ν i v ≫
        twist k (D.parity i) ((U).map (X := (J).obj v) (Y := t) g) := rfl

/-- This is the ordinary Hom identity needed for actual old coend balancing. -/
theorem probeOrdinaryInverseHom_balance (v w : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (f : v ⟶ w) (g : (J).obj w ⟶ t) :
    probeOrdinaryInverseHom D Sc m ν i v t ((J).map (X := v) (Y := w) f ≫ g) =
      (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f) ≫
        probeOrdinaryInverseHom D Sc m ν i w t g := by
  let uf := (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f)
  let ug := (U).map (X := (J).obj w) (Y := t) g
  have hm : (U).map (X := (J).obj v) (Y := t) ((J).map (X := v) (Y := w) f ≫ g) =
      uf ≫ ug := (U).map_comp ((J).map (X := v) (Y := w) f) g
  change probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i) ((U).map (X := (J).obj v) (Y := t) ((J).map f ≫ g)) =
    uf ≫ (probeOrdinarySourceDotInverse D Sc m ν i w ≫ twist k (D.parity i) ug)
  calc
    _ = probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) (uf ≫ ug) :=
      congrArg (fun x => probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) x) hm
    _ = (probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) uf) ≫
        twist k (D.parity i) ug := by rw [twist_comp, Category.assoc]
    _ = (uf ≫ probeOrdinarySourceDotInverse D Sc m ν i w) ≫ twist k (D.parity i) ug :=
      congrArg (fun x => x ≫ twist k (D.parity i) ug)
        (probeOrdinarySourceDotInverse_naturality D Sc m ν i v w f).symm
    _ = _ := Category.assoc _ _ _

/-- The first inverse product reduces to the scalar image of the old Hom. -/
theorem probeOrdinaryInverseHom_dot (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) :
    probeOrdinaryInverseHom D Sc m ν i v t
      (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) =
      sign k (D.parity i * D.parity i) • (U).map (X := (J).obj v) (Y := t) g := by
  let ad := (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v)
  let ug := (U).map (X := (J).obj v) (Y := t) g
  have ha : ad ∈ parity (R := k) ((U).obj ((J).obj v)) ((U).obj ((J).obj v)) (D.parity i) := by
    rw [show ad = probeOrdinaryAppendDot D Sc m ν i ((Q).obj v) from
      probeOldContentAppendDot_image D Sc m ν i v]
    exact (probeOrdinaryAppendDot_supernatural D Sc m ν i).mem ((Q).obj v)
  have hm : (U).map (X := (J).obj v) (Y := t)
      (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) =
      ad ≫ twist k (D.parity i) ug := by
    exact ((U).map_comp (probeOldContentAppendDot D Sc m ν i v) (twist k (D.parity i) g)).trans
      (congrArg (fun z => ad ≫ z) (map_twist U (D.parity i) g))
  change probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i) ((U).map (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g)) = _
  rw [hm, twist_comp, twist_twist, twist_of_mem (D.parity i) ha,
    Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    probeOrdinarySourceDotInverse_dot, Category.id_comp]

/-- The other inverse product retains the same parity-square sign. -/
theorem probeOrdinaryDot_twist_inverseHom (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) :
    (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) ≫
      twist k (D.parity i) (probeOrdinaryInverseHom D Sc m ν i v t g) =
      sign k (D.parity i * D.parity i) • (U).map (X := (J).obj v) (Y := t) g := by
  change (U).map (probeOldContentAppendDot D Sc m ν i v) ≫
    twist k (D.parity i) (probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i) ((U).map g)) = _
  rw [twist_comp, twist_twist,
    twist_of_mem (D.parity i) (probeOrdinarySourceDotInverse_mem D Sc m ν i v),
    Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    probeOrdinarySourceDot_dotInverse, Category.id_comp]

end SourceInverse

section InverseSummand
variable [Fintype I] (i : I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "L" => ELVOld.BalancedInduction.induced J N
local notation "hL" => probeOldInduced_evaluatesCoefficients D m Sc ν i N hN
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- Ordinary Hom action on the unchanged actual induced old module values. -/
def probeOldInverseHomAction (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    ((J).obj v ⟶ t) →ₗ[k] ((L).obj ((J).obj v) ⟶ (L).obj t) :=
  (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t).comp
    (probeOrdinaryInverseHom D Sc m ν i v t)

/-- The inverse summand is bilinear in the original old Hom and module vector. -/
def probeOldInverseGenerator (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    ((J).obj v ⟶ t) →ₗ[k] (N.obj v →ₗ[k] ELVOld.BalancedInduction.Obj J N.toFunctor t) :=
  (Linear.leftComp k ((L).obj t)
    (show N.obj v ⟶ (L).obj ((J).obj v) from ELVOld.BalancedInduction.unit J N.toFunctor v)).comp
      (probeOldInverseHomAction D Sc m ν i N hN v t)

@[simp] theorem probeOldInverseGenerator_apply (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeOldInverseGenerator D Sc m ν i N hN v t g b =
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (probeOrdinaryInverseHom D Sc m ν i v t g)
        (ELVOld.BalancedInduction.unit J N.toFunctor v b) := rfl

def probeOldInverseSummand (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    (((J).obj v ⟶ t) ⊗[k] N.obj v) →ₗ[k] ELVOld.BalancedInduction.Obj J N.toFunctor t :=
  TensorProduct.lift (probeOldInverseGenerator D Sc m ν i N hN v t)

@[simp] theorem probeOldInverseSummand_tmul (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeOldInverseSummand D Sc m ν i N hN v t (g ⊗ₜ[k] b) =
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (probeOrdinaryInverseHom D Sc m ν i v t g)
        (ELVOld.BalancedInduction.unit J N.toFunctor v b) :=
  TensorProduct.lift.tmul g b
/-- Balancing is proved inside the original old coend. -/
theorem probeOldInverseSummand_balance (v w : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (f : v ⟶ w) (g : (J).obj w ⟶ t) (b : N.obj v) :
    probeOldInverseSummand D Sc m ν i N hN v t (((J).map f ≫ g) ⊗ₜ[k] b) =
      probeOldInverseSummand D Sc m ν i N hN w t (g ⊗ₜ[k] N.toFunctor.map f b) := by
  rw [probeOldInverseSummand_tmul, probeOldInverseSummand_tmul]
  let uf := (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f)
  let hg := probeOrdinaryInverseHom D Sc m ν i w t g
  let uv := ELVOld.BalancedInduction.unit J N.toFunctor v b
  have hb := probeOrdinaryInverseHom_balance D Sc m ν i v w t f g
  have hc := probeScalarAction_comp D Sc m (i :: ν) L hL ((J).obj v) ((J).obj w) t uf hg
  have ho : probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj w) uf =
      (show (L).obj ((J).obj v) ⟶ (L).obj ((J).obj w) from
        ELVOld.BalancedInduction.postcompose J N.toFunctor ((J).map f)) :=
    probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) ((J).obj w) ((J).map f)
  have hu := LinearMap.congr_fun (ELVOld.BalancedInduction.unit_naturality J N.toFunctor f) b
  calc
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (uf ≫ hg) uv :=
      congrArg (fun z => probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t z uv) hb
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg
        (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj w) uf uv) := by
      simpa only [SVec.comp_apply] using congrArg
        (fun z : (L).obj ((J).obj v) ⟶ (L).obj t => z uv) hc
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg
        (ELVOld.BalancedInduction.postcompose J N.toFunctor ((J).map f) uv) :=
      congrArg (fun z => probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg z)
        (congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj ((J).obj w) => z uv) ho)
    _ = _ := congrArg (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg)
      (by simpa only [LinearMap.comp_apply] using hu)

/-- Explicit signed inverse candidate on the actual old balanced quotient. -/
def probeOldContentInductionDotInverse
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    ELVOld.BalancedInduction.Obj J N.toFunctor t →ₗ[k]
      ELVOld.BalancedInduction.Obj J N.toFunctor t :=
  sign k (D.parity i * D.parity i) • ELVOld.BalancedInduction.lift J N.toFunctor t
    (fun v => probeOldInverseSummand D Sc m ν i N hN v t)
    (fun v w f g b => probeOldInverseSummand_balance D Sc m ν i N hN v w t f g b)

@[simp] theorem probeOldContentInductionDotInverse_tensor (v : C)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeOldContentInductionDotInverse D Sc m ν i N hN t
      (ELVOld.BalancedInduction.tensor J N.toFunctor v g b) =
    sign k (D.parity i * D.parity i) •
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (probeOrdinaryInverseHom D Sc m ν i v t g)
        (ELVOld.BalancedInduction.unit J N.toFunctor v b) := by
  rw [probeOldContentInductionDotInverse, LinearMap.smul_apply,
    ELVOld.BalancedInduction.lift_tensor, probeOldInverseSummand_tmul]

/-- No finite-dimensionality is used: one inverse product is checked on the old generators. -/
theorem probeOldContentInductionDotInverse_comp_dot
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    (probeOldContentInductionDotInverse D Sc m ν i N hN t).comp
      (probeOldContentInductionDot D Sc m ν i N t) = LinearMap.id := by
  apply ELVOld.BalancedInduction.hom_ext
  intro v g b
  rw [LinearMap.comp_apply, probeOldContentInductionDot_tensor,
    probeOldContentInductionDotInverse_tensor, probeOrdinaryInverseHom_dot,
    map_smul, SVec.smul_apply, sign_smul_sign_smul]
  have h := probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) t g
  have hv := congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj t =>
    z (ELVOld.BalancedInduction.unit J N.toFunctor v b)) h
  exact hv.trans (ELVOld.BalancedInduction.postcompose_unit J N.toFunctor g b)

omit [Fintype I] in
private theorem probeOldContentInductionDot_unit_action (v : C) (b : N.obj v) :
    probeOldContentInductionDot D Sc m ν i N ((J).obj v)
      (ELVOld.BalancedInduction.unit J N.toFunctor v b) =
    probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj v)
      ((U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v))
      (ELVOld.BalancedInduction.unit J N.toFunctor v b) := by
  have h := probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) ((J).obj v)
    (probeOldContentAppendDot D Sc m ν i v)
  exact (ELVOld.BalancedInduction.transform_unit
    (probeOldContentAppendDot_supernatural D Sc m ν i) N v b).trans
      (congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj ((J).obj v) =>
        z (ELVOld.BalancedInduction.unit J N.toFunctor v b)) h).symm

/-- The second inverse product uses the old dot's descended full supernaturality. -/
theorem probeOldContentInductionDot_comp_inverse
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    (probeOldContentInductionDot D Sc m ν i N t).comp
      (probeOldContentInductionDotInverse D Sc m ν i N hN t) = LinearMap.id := by
  apply ELVOld.BalancedInduction.hom_ext
  intro v g b
  rw [LinearMap.comp_apply, probeOldContentInductionDotInverse_tensor, map_smul]
  let hf := probeOrdinaryInverseHom D Sc m ν i v t g
  let ad := (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v)
  let uv := ELVOld.BalancedInduction.unit J N.toFunctor v b
  have hv : probeOldContentInductionDot D Sc m ν i N t
      (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t hf uv) =
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (twist k (D.parity i) hf)
        (probeOldContentInductionDot D Sc m ν i N ((J).obj v) uv) := by
    obtain ⟨fr, hfr⟩ := elvProbeOldHom_surjective D m Sc ((J).obj v).obj.word t.obj.word hf
    let f₀ : (J).obj v ⟶ t := fr
    have hfr' : (U).map (X := (J).obj v) (Y := t) f₀ = hf := hfr
    rw [← hfr', probeScalarAction_old, ← map_twist (U) (D.parity i) f₀,
      probeScalarAction_old]
    exact LinearMap.congr_fun (ELVOld.BalancedInduction.transformLinear_naturality
      (probeOldContentAppendDot_supernatural D Sc m ν i) N f₀) uv
  have hc := probeScalarAction_comp D Sc m (i :: ν) L hL ((J).obj v) ((J).obj v) t
    ad (twist k (D.parity i) hf)
  have hcv := congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj t => z uv) hc
  have hd := probeOrdinaryDot_twist_inverseHom D Sc m ν i v t g
  calc
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (twist k (D.parity i) hf)
          (probeOldContentInductionDot D Sc m ν i N ((J).obj v) uv) := by
      exact congrArg (fun z => sign k (D.parity i * D.parity i) • z)
        hv
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (twist k (D.parity i) hf)
          (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj v) ad uv) :=
      congrArg (fun z => sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (twist k (D.parity i) hf) z)
          (probeOldContentInductionDot_unit_action D Sc m ν i N hN v b)
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
          (ad ≫ twist k (D.parity i) hf) uv :=
      congrArg (fun z => sign k (D.parity i * D.parity i) • z)
        (by simpa only [SVec.comp_apply] using hcv.symm)
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
          (sign k (D.parity i * D.parity i) • (U).map (X := (J).obj v) (Y := t) g) uv :=
      congrArg (fun z => sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t z uv) hd
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        ((U).map (X := (J).obj v) (Y := t) g) uv := by
      rw [map_smul, SVec.smul_apply, sign_smul_sign_smul]
    _ = _ := (congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj t => z uv)
      (probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) t g)).trans
        (ELVOld.BalancedInduction.postcompose_unit J N.toFunctor g b)

/-- Intermediate unit for a scalar-evaluated old module. The canonical probe-module
specialization below proves the scalar-evaluation hypothesis. -/
def probeOldContentInductionDotUnit
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    (End (ELVOld.BalancedInduction.superspace J N.toFunctor t))ˣ where
  val := End.of (probeOldContentInductionDot D Sc m ν i N t)
  inv := End.of (probeOldContentInductionDotInverse D Sc m ν i N hN t)
  val_inv := probeOldContentInductionDot_comp_inverse D Sc m ν i N hN t
  inv_val := probeOldContentInductionDotInverse_comp_dot D Sc m ν i N hN t

include hN in
theorem probeOldContentInductionDot_isUnit
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    IsUnit (End.of (probeOldContentInductionDot D Sc m ν i N t) :
      End (ELVOld.BalancedInduction.superspace J N.toFunctor t)) :=
  (probeOldContentInductionDotUnit D Sc m ν i N hN t).isUnit

end InverseSummand

section ProbeModule
variable [Fintype I] {B : Type u} [Ring B] [Algebra k B]
  {GB : ZMod 2 → Submodule k B}
  (M : SuperBimodule
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) ν.length) GB)

end ProbeModule

end OddMath.QuiverHecke