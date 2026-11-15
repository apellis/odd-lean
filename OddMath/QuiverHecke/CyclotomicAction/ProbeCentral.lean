import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightCap
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.SKM.RouquierFTriangle
import OddMath.SKM.RouquierPreAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import Mathlib.RingTheory.Nilpotent.Basic
import OddMath.SKM.RouquierHomMixedRational
import Mathlib.Tactic.Abel
import OddMath.QuiverHecke.CyclotomicAction.TensorWord
import OddMath.QuiverHecke.SwappedVacuum.NegativeCapMoments
import Mathlib.Algebra.Polynomial.Expand
import OddMath.QuiverHecke.SwappedVacuum.InverseColumnOddSeries
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.CapWindows
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorVacuum
import OddMath.SKM.RouquierHomWeightCoordinates

/-!
# Probe central

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Comparing the inverse-defined Rouquier cap with the regular probe row

The existing left-adjunction route uses adjacent local Rouquier inverses,
not a separate Frobenius construction. At negative height the raw left cap
is an inverse row; its unit window forces its component at the regular
probe to be the specified native cap. The normalized counit additionally
retains the exact fixed scalar from `RouquierFTriangle`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u+1} k}
    {F : A ⟶ B} (d : End F) (n : ℕ) (M : A) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]

private theorem whisker_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The existing ordinary right adjunction on the chosen native probe edge. -/
def appendRightAdjunction (i : I) :
    SKM.SuperAdjunction (k := k) (inductionCell D Sc m i) (restrictionCell D Sc m i) :=
  ordinaryEvenSuperAdjunction (inductionCell D Sc m i) (restrictionCell D Sc m i)
    (adjunction (K i)) (adjunctionUnit_mem (K i)) (adjunctionCounit_mem (K i))

section Local
variable (i : I)
  {A : PiSCat.{u,u,u+1} k}
  {E₀ : A ⟶ modulePiCategory D Sc m} {F₀ : modulePiCategory D Sc m ⟶ A}
  (A₀ : SKM.SuperAdjunction (k := k) E₀ F₀) (x₀ : End E₀)
  (t : End (E₀ ≫ inductionCell D Sc m i))
  (L : SKM.SuperRouquierLoc A₀ (appendRightAdjunction D Sc m i)
    x₀ (inductionDotCell D Sc m i) t (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ)))

section Adjacent
variable {Z : PiSCat.{u,u,u+1} k}
  {E₃ : raisedModulePiCategory D Sc m i ⟶ Z} {F₃ : Z ⟶ raisedModulePiCategory D Sc m i}
  (A₃ : SKM.SuperAdjunction (k := k) E₃ F₃) (x₃ : End E₃)
  (t' : End (inductionCell D Sc m i ≫ E₃))
  (U : SKM.SuperRouquierLoc (appendRightAdjunction D Sc m i) A₃
    (inductionDotCell D Sc m i) x₃ t' (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ) + 2))
  (hP : 0 < probeCutoff D m i) (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
  (hB : E₀ ◁ t' ≫ ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' =
    ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' ≫
      ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
        (associator E₀ (inductionCell D Sc m i) E₃).hom))

end Adjacent

end Local

end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # Finite-local precomposition adjunction of the probe

For SwappedHomInversion §1, use the checked negative-height left adjunction
from the prescribed two adjacent local inverses on the given probe edge.
Its unshifted precomposition adjunction is constructed on the whole Hom
supercategory. Its counit evaluates to the already specified shifted cap,
including both diagonal Koszul factors. This supplies no arbitrary mate.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u
local instance probeLocalPreAdjunctionPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def sourceIso {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    (E : A ⟶ B) (F : B ⟶ A) (H : A ⟶ R) (σ : ZMod 2) :=
  (SKM.homPre (k := k) E).mapIso ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ H)) ≪≫
    (associator E F H).symm

private theorem total_zsmul {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ R} (η : F ⟶ G) (z : ℤ) (M : A) :
    (z • η).total M = z • η.total M := by
  change z • η.app 0 M + z • η.app 1 M = z • (η.app 0 M + η.app 1 M)
  exact (smul_add _ _ _).symm

private theorem whisker_total_2 {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

private theorem preCounit_total {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {E : A ⟶ B} {F : B ⟶ A} {σ : ZMod 2}
    (L : SKM.ShiftedSuperAdjunction (k := k) F E σ) (H : A ⟶ R) (M : A) :
    ((SKM.unshiftedPreAdjunction L R).counit.app H).total M =
      koszulSign σ σ • ((sourceIso E F H σ).hom.total M ≫ H.map (L.counit.total M)) := by
  rw [SKM.unshiftedPreAdjunction_counit_app, total_zsmul]
  have he : (sourceIso E F H σ).hom ≫ L.counit ▷ H ≫ (leftUnitor H).hom =
      E ◁ ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ≫
        (associator E F H).inv ≫ L.counit ▷ H ≫ (leftUnitor H).hom := by
    change (_ ≫ _) ≫ _ ≫ _ = _
    exact Category.assoc _ _ _
  rw [← he]
  rw [Superfunctor.comp_total, Superfunctor.comp_total, whisker_total_2]
  have hi : ((leftUnitor H).hom).total M = 𝟙 (H.obj M) := SuperNatTrans.id_total H.toFunctor M
  rw [hi]
  erw [Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
section Local
variable (i : I)
  {A : PiSCat.{u,u,u+1} k}
  {E₀ : A ⟶ modulePiCategory D Sc m} {F₀ : modulePiCategory D Sc m ⟶ A}
  (A₀ : SKM.SuperAdjunction (k := k) E₀ F₀) (x₀ : End E₀)
  (t : End (E₀ ≫ inductionCell D Sc m i))
  (L : SKM.SuperRouquierLoc A₀ (appendRightAdjunction D Sc m i)
    x₀ (inductionDotCell D Sc m i) t (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ)))

section Adjacent
variable {Z : PiSCat.{u,u,u+1} k}
  {E₃ : raisedModulePiCategory D Sc m i ⟶ Z} {F₃ : Z ⟶ raisedModulePiCategory D Sc m i}
  (A₃ : SKM.SuperAdjunction (k := k) E₃ F₃) (x₃ : End E₃)
  (t' : End (inductionCell D Sc m i ≫ E₃))
  (U : SKM.SuperRouquierLoc (appendRightAdjunction D Sc m i) A₃
    (inductionDotCell D Sc m i) x₃ t' (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ) + 2))
  (hP : 0 < probeCutoff D m i) (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
  (hB : E₀ ◁ t' ≫ ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' =
    ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' ≫
      ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
        (associator E₀ (inductionCell D Sc m i) E₃).hom))

end Adjacent
end Local
end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # Evaluation of the mixed diagonal at the regular probe

SwappedHomInversion §3 (A6), (3)–(5). The inverse probe dot is used only on
the scalar-evaluated regular probe carrier. The evaluated bend uses the
chosen post unit and the constructed pre counit, in that order. Attachment
to the complete swapped matrix is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u

local instance centralBendHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private theorem isUnit_of_square_plus_one_pow {R : Type*} [Ring R] (x : R) (m : ℕ)
    (hx : (x ^ 2 + 1) ^ m = 0) : IsUnit x := by
  have hn : IsNilpotent (x ^ 2 + 1) := ⟨m, hx⟩
  have hu : IsUnit (x ^ 2) := by simpa only [add_sub_cancel_right] using hn.isUnit_sub_one
  exact (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hu

private theorem homogeneous_total_mem
    {k C R : Type*} [CommRing k] [Category C] [Category R]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R]
    {F G : Superfunctor k C R} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (M : C) :
    f.total M ∈ parity (R := k) _ _ p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0), add_zero]
    exact f.app_mem 0 M
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1), zero_add]
    exact f.app_mem 1 M

private theorem inverse_mem_of_isUnit
    {k C : Type*} [CommRing k] [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {X : C} (x : End X) (hx : IsUnit x) {p : ZMod 2} (hm : x ∈ parity (R := k) _ _ p) :
    Ring.inverse x ∈ parity (R := k) _ _ p := by
  obtain ⟨v, rfl⟩ := hx
  rw [Ring.inverse_unit]
  let e : X ≅ X := {
    hom := (v : End X)
    inv := ((v⁻¹ : (End X)ˣ) : End X)
    hom_inv_id := v.inv_val
    inv_hom_id := v.val_inv }
  exact inv_mem e hm

private theorem end_pow_mem
    {k C : Type*} [CommRing k] [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {X : C} {x : End X} {p : ZMod 2} (hx : x ∈ parity (R := k) _ _ p) (n : ℕ) :
    x ^ n ∈ parity (R := k) _ _ (n • p) := by
  induction n with
  | zero => simpa only [pow_zero, zero_nsmul, End.one_def] using id_mem (R := k) X
  | succ n ih => simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm] using comp_mem hx ih

private theorem adjacent_parity_product_zero (p : ZMod 2) (r : ℕ) :
    (r • p) * ((r + 1) • p) = 0 := by
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  generalize (r : ZMod 2) = a
  fin_cases a <;> fin_cases p <;> decide

private theorem map_inverse_of_isUnit
    {C B : Type*} [Category C] [Category B] [Preadditive C] [Preadditive B] {X : C}
    (F : C ⥤ B) (x : End X) (hx : IsUnit x) :
    (F.mapEnd X) (Ring.inverse x) = Ring.inverse (F.mapEnd X x) := by
  obtain ⟨v, rfl⟩ := hx
  change (F.mapEnd X) (Ring.inverse (v : End X)) =
    Ring.inverse ((Units.map (F.mapEnd X) v : (End (F.obj X))ˣ) : End (F.obj X))
  simp only [Ring.inverse_unit, Units.coe_map_inv]

private theorem neg_one_pow_mul {R : Type*} [Ring R] (r : ℕ) (z : R) :
    (-1 : R) ^ r * z = (-1 : ℤ) ^ r • z := by
  rw [zsmul_eq_mul]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

section Bend
variable {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, End (J.obj s)} (hα : IsSupernatural k p α)

private theorem dot_power_supernatural (n : ℕ) :
    IsSupernatural k (n • p) (F := induction J) (G := induction J)
      (fun M => dotEnd J hα M ^ n) := by
  have hd := transformComponent_supernatural hα
  induction n with
  | zero => simpa only [zero_nsmul, pow_zero, End.one_def] using
      (isSupernatural_id (R := k) (F := induction J))
  | succ n ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm, dotEnd] using hd.comp ih

/-- The evaluated cup–diagonal–cap component, using the given ordinary
post unit and the same post induction/restriction maps. -/
private def postBend (M N : Superfunctor k C (SVec k)) (v : M ⟶ N)
    (a : End ((induction J).obj M)) : M ⟶ (restriction J).obj ((induction J).obj N) :=
  (adjunction J).unit.app M ≫ (restriction J).map a ≫
    (restriction J).map ((induction J).map v)

private def postBendLinear (M N : Superfunctor k C (SVec k)) (v : M ⟶ N) :
    End ((induction J).obj M) →ₗ[k] (M ⟶ (restriction J).obj ((induction J).obj N)) :=
  (Linear.leftComp k _ ((adjunction J).unit.app M)).comp
    ((Linear.rightComp k _ ((restriction J).map ((induction J).map v))).comp
      ((restriction J).mapLinearMap k))

private theorem postBend_monomial (M N : Superfunctor k C (SVec k))
    (v : M ⟶ N) (hv : v ∈ parity (R := k) _ _ 0) (f : End M) (r : ℕ) :
    postBend J M N v ((induction J).map f ≫ dotEnd J hα M ^ r) =
      f ≫ v ≫ (adjunction J).unit.app N ≫ (restrictedDotEnd J hα N ^ r) := by
  have hd : (dotEnd J hα M ^ r) ≫ (induction J).map v =
      (induction J).map v ≫ (dotEnd J hα N ^ r) := by
    have h := (dot_power_supernatural J hα r).naturality hv
    simpa only [mul_zero, sign_zero, one_smul] using h.symm
  have hc : ((induction J).map f ≫ dotEnd J hα M ^ r) ≫ (induction J).map v =
      (induction J).map (f ≫ v) ≫ dotEnd J hα N ^ r := by
    rw [Category.assoc, hd, ← Category.assoc, ← Functor.map_comp]
  have hu := (adjunction J).unit.naturality (f ≫ v)
  change (f ≫ v) ≫ (adjunction J).unit.app N =
    (adjunction J).unit.app M ≫ (restriction J).map ((induction J).map (f ≫ v)) at hu
  have hp := map_pow ((restriction J).mapEnd ((induction J).obj N)) (dotEnd J hα N) r
  change (restriction J).map (dotEnd J hα N ^ r) = restrictedDotEnd J hα N ^ r at hp
  calc
    _ = (adjunction J).unit.app M ≫
        (restriction J).map ((induction J).map (f ≫ v) ≫ dotEnd J hα N ^ r) := by
      unfold postBend
      rw [← Functor.map_comp, hc]
    _ = ((adjunction J).unit.app M ≫ (restriction J).map ((induction J).map (f ≫ v))) ≫
        (restriction J).map (dotEnd J hα N ^ r) := by
      rw [Functor.map_comp, Category.assoc]
    _ = ((f ≫ v) ≫ (adjunction J).unit.app N) ≫
        (restriction J).map (dotEnd J hα N ^ r) :=
      congrArg (fun g => g ≫ (restriction J).map (dotEnd J hα N ^ r)) hu.symm
    _ = _ := by rw [hp]; simp only [Category.assoc]

private theorem dot_inverse_powers_exchange (M : Superfunctor k C (SVec k))
    (x : End M) (hx : IsUnit x) (hm : x ∈ parity (R := k) _ _ p) (r : ℕ) :
    (induction J).map (Ring.inverse x ^ (r + 1)) ≫ dotEnd J hα M ^ r =
      (dotEnd J hα M ^ r) ≫ (induction J).map (Ring.inverse x ^ (r + 1)) := by
  have h := (dot_power_supernatural J hα r).naturality
    (end_pow_mem (inverse_mem_of_isUnit x hx hm) (r + 1))
  simpa only [adjacent_parity_product_zero, sign_zero, one_smul] using h

/-- Evaluation of a finite diagonal series retains its prescribed cap and post-unit. -/
theorem postBend_sum (M N : Superfunctor k C (SVec k))
    (v : M ⟶ N) (hv : v ∈ parity (R := k) _ _ 0)
    (f : ℕ → End M) (c : ℕ → ℤ) (n : ℕ) :
    postBend J M N v (∑ r ∈ Finset.range n, c r • ((induction J).map (f r) ≫ dotEnd J hα M ^ r)) =
      ∑ r ∈ Finset.range n, c r • (f r ≫ v ≫ (adjunction J).unit.app N ≫ (restrictedDotEnd J hα N ^ r)) := by
  change postBendLinear J M N v (∑ r ∈ Finset.range n, c r • _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [map_zsmul]
  change c r • postBend J M N v _ = _
  rw [postBend_monomial J hα M N v hv (f r) r]

private theorem odd_diagonal_expansion (M : Superfunctor k C (SVec k))
    (x : End M) (hx : IsUnit x) (hm : x ∈ parity (R := k) _ _ p) (hodd : p = 1)
    (n : ℕ) (hn : dotEnd J hα M ^ n = 0) :
    ((induction J).mapEnd M x - dotEnd J hα M) *
      Ring.inverse (((induction J).mapEnd M x) ^ 2 - dotEnd J hα M ^ 2) =
      ∑ r ∈ Finset.range (2 * n), (-1 : ℤ) ^ r •
        ((induction J).map (Ring.inverse x ^ (r + 1)) ≫ dotEnd J hα M ^ r) := by
  let X := (induction J).mapEnd M x
  let Y := dotEnd J hα M
  have hxy := (transformComponent_supernatural hα).naturality hm
  change X ≫ Y = sign k (p * p) • (Y ≫ X) at hxy
  rw [hodd, mul_one, sign_one, neg_one_smul] at hxy
  have ha : X * Y = -(Y * X) := by
    change Y ≫ X = -(X ≫ Y)
    exact (neg_eq_iff_eq_neg.mp hxy.symm)
  obtain ⟨u, hu⟩ := hx.map ((induction J).mapEnd M)
  change (u : End ((induction J).obj M)) = X at hu
  have h := SKM.mixedOddInverse_expansion u Y (by simpa only [hu] using ha) n hn
  have hi : (↑u⁻¹ : End ((induction J).obj M)) = Ring.inverse X := by
    rw [← hu, Ring.inverse_unit]
  rw [hu, hi] at h
  change (X - Y) * Ring.inverse (X ^ 2 - Y ^ 2) = _
  rw [h]
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_assoc, neg_one_pow_mul]
  congr 1
  dsimp only [X, Y]
  rw [← map_inverse_of_isUnit (induction J) x hx, ← map_pow ((induction J).mapEnd M)]
  change (dotEnd J hα M ^ r) ≫ (induction J).map (Ring.inverse x ^ (r + 1)) =
    (induction J).map (Ring.inverse x ^ (r + 1)) ≫ dotEnd J hα M ^ r
  exact (dot_inverse_powers_exchange J hα M x hx hm r).symm

end Bend

namespace ProbeVacuumCap
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)

/-- The raw shifted pre-dot is a unit on the actual regular probe carrier.
This does not assert invertibility on arbitrary old modules. -/
theorem shiftedPreDot_isUnit (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 1)
    (H : modulePiCategory D Sc m ⟶ R) : IsUnit (shiftedPreDot D Sc m R i H) :=
  isUnit_of_square_plus_one_pow _ _ (shiftedPreDot_odd_polynomial D Sc m R i hi H)

/-- The same raw pre-E dot retains the moving-colour degree before its
post induction and before any coordinate comparison removes a shift. -/
theorem shiftedPreDot_mem (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreDot D Sc m R i H ∈ parity (R := k) _ _ (D.parity i) := by
  unfold shiftedPreDot
  exact homogeneous_total_mem
    (TwoSupercategory.whiskerRight_mem _ (inductionDotCell_mem D Sc m i)) _

variable (reservoirCutoff : I → ℕ) (bound : ℕ)
local notation "R₀" => contentModuleTarget D Sc reservoirCutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m

omit [Fintype I] in
private theorem reservoir_dot_supernatural (i : I) :
    IsSupernatural k (D.parity i)
      (F := contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])
      (G := contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])
      (contentAppendToComponent D Sc reservoirCutoff bound
        (β := (0 : Multiset I)) (γ := 0 + ([i] : Multiset I)) rfl rfl (dotE D Sc [i] 0)) :=
  contentAppendTo_supernatural D Sc reservoirCutoff bound rfl rfl (firstDot_parity D Sc i [])

/-- The chosen raw pre-E dot, after the actual post induction, on the
regular-probe mixed carrier. Its sign is not replaced by coordinateDot. -/
def diagonalPreDot (i : I) (H : modulePiCategory D Sc m ⟶ R₀) :=
  (induction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).mapEnd _
    (shiftedPreDot D Sc m R₀ i H)

/-- The given reservoir dot on precisely the same induced mixed carrier. -/
def diagonalPostDot (i : I) (H : modulePiCategory D Sc m ⟶ R₀) :=
  dotEnd (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])
    (reservoir_dot_supernatural D Sc reservoirCutoff bound i)
    (shiftedPreSourceObject D Sc m R₀ i H)

/-- The given restricted reservoir dot on the target vacuum module. -/
abbrev evaluatedPostDot (i : I) (H : modulePiCategory D Sc m ⟶ R₀) :=
  restrictedDotEnd (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])
    (reservoir_dot_supernatural D Sc reservoirCutoff bound i) (H.obj N₀)

/-- The prescribed A6 rational diagonal on the evaluated regular-probe
carrier. No inverse on the category of all OLD modules is asserted. -/
def evaluatedMixedDiagonal (i : I) (H : modulePiCategory D Sc m ⟶ R₀) :=
  if D.parity i = 0 then Ring.inverse
    (diagonalPostDot D Sc m reservoirCutoff bound i H - diagonalPreDot D Sc m reservoirCutoff bound i H)
  else (diagonalPreDot D Sc m reservoirCutoff bound i H - diagonalPostDot D Sc m reservoirCutoff bound i H) *
    Ring.inverse (diagonalPreDot D Sc m reservoirCutoff bound i H ^ 2 -
      diagonalPostDot D Sc m reservoirCutoff bound i H ^ 2)

/-- Evaluation of the given post-unit/diagonal/pre-cap bend. The cap is
the prescribed shifted cap identified with the constructed local adjunction
counit, rather than an independent extractor. -/
def evaluatedMixedBend (i : I) (hP : 0 < probeCutoff D m i)
    (H : modulePiCategory D Sc m ⟶ R₀) :=
  postBend (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])
    (shiftedPreSourceObject D Sc m R₀ i H) (H.obj N₀)
    (shiftedPreCap D Sc m R₀ i hP H) (evaluatedMixedDiagonal D Sc m reservoirCutoff bound i H)

/-- The actual mixed dots have their given super-interchange sign, on
this regular-probe induced carrier. -/
theorem diagonal_dots_exchange (i : I) (H : modulePiCategory D Sc m ⟶ R₀) :
    diagonalPreDot D Sc m reservoirCutoff bound i H ≫ diagonalPostDot D Sc m reservoirCutoff bound i H =
      koszulSign (D.parity i) (D.parity i) •
        (diagonalPostDot D Sc m reservoirCutoff bound i H ≫ diagonalPreDot D Sc m reservoirCutoff bound i H) := by
  have h := (transformComponent_supernatural
    (reservoir_dot_supernatural D Sc reservoirCutoff bound i)).naturality
      (shiftedPreDot_mem D Sc m R₀ i H)
  simpa only [diagonalPreDot, diagonalPostDot, dotEnd, Functor.mapEnd_apply, koszulSign_smul (R := k)] using h

/-- A fixed-content nilpotence exponent works on the actual mixed
reservoir dot at every regular-probe Hom object. -/
theorem diagonalPostDot_pow_zero
    (hdot : TruncatedAppendDotNilpotent D Sc reservoirCutoff bound) (i : I) :
    ∃ n : ℕ, 0 < n ∧ ∀ H : modulePiCategory D Sc m ⟶ R₀,
      diagonalPostDot D Sc m reservoirCutoff bound i H ^ n = 0 := by
  obtain ⟨n, hn, hp⟩ := contentInductionDot_module_pow_zero D Sc reservoirCutoff bound
    hdot [] i
  refine ⟨n, hn, fun H => ?_⟩
  have h := hp (shiftedPreSourceObject D Sc m R₀ i H)
  rw [contentInductionDot_component] at h
  exact h

/-- The target's restricted reservoir dot has a positive nilpotence
exponent at this fixed content, on every regular-probe Hom object. -/
theorem evaluatedPostDot_pow_zero
    (hdot : TruncatedAppendDotNilpotent D Sc reservoirCutoff bound) (i : I) :
    ∃ n : ℕ, 0 < n ∧ ∀ H : modulePiCategory D Sc m ⟶ R₀,
      evaluatedPostDot D Sc m reservoirCutoff bound i H ^ n = 0 := by
  obtain ⟨n, hn, hp⟩ := contentInductionDot_module_pow_zero D Sc reservoirCutoff bound
    hdot [] i
  refine ⟨n, hn, fun H => ?_⟩
  have h := hp (H.obj N₀)
  rw [contentInductionDot_component] at h
  have hy : dotEnd (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])
      (reservoir_dot_supernatural D Sc reservoirCutoff bound i) (H.obj N₀) ^ n = 0 := h
  have hr := congrArg
    ((restriction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).mapEnd _) hy
  rw [map_pow] at hr
  simpa only [evaluatedPostDot, restrictedDotEnd, Functor.mapEnd_apply, Functor.map_zero] using hr

/-- The given A6 odd diagonal is the finite ordered geometric series
on the regular-probe mixed carrier, using its raw pre-E dot inverse. -/
theorem evaluatedMixedDiagonal_odd_expansion (i : I) (hi : D.parity i = 1)
    (H : modulePiCategory D Sc m ⟶ R₀) (n : ℕ)
    (hn : diagonalPostDot D Sc m reservoirCutoff bound i H ^ n = 0) :
    evaluatedMixedDiagonal D Sc m reservoirCutoff bound i H =
      ∑ r ∈ Finset.range (2 * n), (-1 : ℤ) ^ r •
        ((induction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).map
          (Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1)) ≫
            diagonalPostDot D Sc m reservoirCutoff bound i H ^ r) := by
  rw [evaluatedMixedDiagonal, ite_eq_right (by rw [hi]; decide)]
  exact odd_diagonal_expansion _ (reservoir_dot_supernatural D Sc reservoirCutoff bound i)
    _ _ (shiftedPreDot_isUnit D Sc m R₀ i hi H) (shiftedPreDot_mem D Sc m R₀ i H) hi n hn

/-- The prescribed evaluated odd A6 bend is the finite central entry in
chronological order: inverse raw pre-dot, given cap, given post unit,
and powers of the given reservoir dot. The source shift is retained. -/
theorem evaluatedMixedBend_odd_expansion (i : I) (hi : D.parity i = 1)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) (n : ℕ)
    (hn : diagonalPostDot D Sc m reservoirCutoff bound i H ^ n = 0) :
    evaluatedMixedBend D Sc m reservoirCutoff bound i hP H =
      ∑ r ∈ Finset.range (2 * n), (-1 : ℤ) ^ r •
        ((Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1)) ≫
          shiftedPreCap D Sc m R₀ i hP H ≫
            (adjunction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀) ≫
              (evaluatedPostDot D Sc m reservoirCutoff bound i H ^ r)) := by
  rw [evaluatedMixedBend, evaluatedMixedDiagonal_odd_expansion D Sc m reservoirCutoff bound i hi H n hn]
  exact postBend_sum _ (reservoir_dot_supernatural D Sc reservoirCutoff bound i) _ _ _
    (shiftedPreCap_mem D Sc m R₀ i hP H) (fun r => Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1))
      (fun r => (-1 : ℤ) ^ r) (2 * n)

section Local
variable (i : I)
  {A : PiSCat.{u,u,u+1} k}
  {E₀ : A ⟶ modulePiCategory D Sc m} {F₀ : modulePiCategory D Sc m ⟶ A}
  (A₀ : SKM.SuperAdjunction (k := k) E₀ F₀) (x₀ : End E₀)
  (t : End (E₀ ≫ inductionCell D Sc m i))
  (L : SKM.SuperRouquierLoc A₀ (appendRightAdjunction D Sc m i)
    x₀ (inductionDotCell D Sc m i) t (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ)))

section Adjacent
variable {Z : PiSCat.{u,u,u+1} k}
  {E₃ : raisedModulePiCategory D Sc m i ⟶ Z} {F₃ : Z ⟶ raisedModulePiCategory D Sc m i}
  (A₃ : SKM.SuperAdjunction (k := k) E₃ F₃) (x₃ : End E₃)
  (t' : End (inductionCell D Sc m i ≫ E₃))
  (U : SKM.SuperRouquierLoc (appendRightAdjunction D Sc m i) A₃
    (inductionDotCell D Sc m i) x₃ t' (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ) + 2))
  (hP : 0 < probeCutoff D m i) (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
  (hB : E₀ ◁ t' ≫ ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' =
    ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' ≫
      ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
        (associator E₀ (inductionCell D Sc m i) E₃).hom))

end Adjacent
end Local

end ProbeVacuumCap
end OddMath.QuiverHecke.ELV
end

end

section

/-! # The signed slide of the evaluated mixed bend

SwappedVacuumNonpositiveBubbles §1 (1) for the actual evaluated A6 bend.
The finite central series telescopes using its raw regular-probe dot unit
and the given fixed-content reservoir nilpotence. No slide for an arbitrary
map is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u
section Series
variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}
private theorem inverse_power_cancel (x : End X) (hx : IsUnit x) (m : ℕ) :
    x ≫ (Ring.inverse x ^ (m + 1)) = Ring.inverse x ^ m := by
  change Ring.inverse x ^ (m + 1) * x = Ring.inverse x ^ m
  rw [pow_succ, mul_assoc, Ring.inverse_mul_cancel _ hx, mul_one]
private def series (x : End X) (y : End Y) (t : X ⟶ Y) (m : ℕ) : X ⟶ Y :=
  ∑ r ∈ Finset.range m, (-1 : ℤ) ^ r • ((Ring.inverse x ^ (r + 1)) ≫ t ≫ (y ^ r))
private theorem series_slide_boundary (x : End X) (hx : IsUnit x) (y : End Y) (t : X ⟶ Y) (m : ℕ) :
    series x y t m ≫ y + x ≫ series x y t m =
      t - (-1 : ℤ) ^ m • ((Ring.inverse x ^ m) ≫ t ≫ (y ^ m)) := by
  induction m with
  | zero => simp only [series, Finset.sum_range_zero, pow_zero, End.one_def, Category.id_comp,
      Category.comp_id, one_zsmul, sub_self, Limits.zero_comp, Limits.comp_zero, zero_add]
  | succ m ih =>
    have hs : series x y t (m + 1) = series x y t m +
        (-1 : ℤ) ^ m • ((Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ m)) := by
      rw [series, Finset.sum_range_succ]
      rfl
    have hY : ((Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ m)) ≫ y =
        (Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ (m + 1)) := by
      simp only [pow_succ' y m, End.mul_def, Category.assoc]
    have hX : x ≫ ((Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ m)) =
        (Ring.inverse x ^ m) ≫ t ≫ (y ^ m) := by
      rw [← Category.assoc, ← Category.assoc, inverse_power_cancel x hx m]
      exact Category.assoc _ _ _
    rw [hs, Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, hY, hX]
    calc
      _ = (series x y t m ≫ y + x ≫ series x y t m) +
          (-1 : ℤ) ^ m • ((Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ (m + 1))) +
          (-1 : ℤ) ^ m • ((Ring.inverse x ^ m) ≫ t ≫ (y ^ m)) := by abel
      _ = _ := by
        rw [ih, show (-1 : ℤ) ^ (m + 1) = -((-1 : ℤ) ^ m) by rw [pow_succ, mul_neg_one],
          neg_smul, sub_neg_eq_add]
        abel
private theorem series_slide (x : End X) (hx : IsUnit x) (y : End Y) (t : X ⟶ Y)
    (m : ℕ) (hy : y ^ m = 0) :
    series x y t m ≫ y + x ≫ series x y t m = t := by
  rw [series_slide_boundary x hx y t m, hy, Limits.comp_zero, Limits.comp_zero,
    smul_zero, sub_zero]
end Series
namespace ProbeVacuumCap
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
  (reservoirCutoff : I → ℕ) (bound : ℕ) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
local notation "R₀" => contentModuleTarget D Sc reservoirCutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m

/-- The signed mate slide on the actual regular-probe evaluated mixed
bend. All its maps are the given raw dot, shifted cap and reservoir unit. -/
theorem evaluatedMixedBend_odd_slideOf
    (hdot : TruncatedAppendDotNilpotent D Sc reservoirCutoff bound) (i : I) (hi : D.parity i = 1)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) :
    evaluatedMixedBend D Sc m reservoirCutoff bound i hP H ≫
        evaluatedPostDot D Sc m reservoirCutoff bound i H -
      koszulSign (D.parity i) (D.parity i) •
        (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m reservoirCutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫
        (adjunction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀) := by
  obtain ⟨n, hn, hd⟩ := diagonalPostDot_pow_zero D Sc m reservoirCutoff bound hdot i
  obtain ⟨l, hl, hy⟩ := evaluatedPostDot_pow_zero D Sc m reservoirCutoff bound hdot i
  have hd' : diagonalPostDot D Sc m reservoirCutoff bound i H ^ (n + l) = 0 :=
    pow_eq_zero_of_le (by omega) (hd H)
  have hy' : evaluatedPostDot D Sc m reservoirCutoff bound i H ^ (2 * (n + l)) = 0 :=
    pow_eq_zero_of_le (by omega) (hy H)
  have he := evaluatedMixedBend_odd_expansion D Sc m reservoirCutoff bound i hi hP H (n + l) hd'
  have hs : evaluatedMixedBend D Sc m reservoirCutoff bound i hP H =
      series (shiftedPreDot D Sc m R₀ i H) (evaluatedPostDot D Sc m reservoirCutoff bound i H)
        (shiftedPreCap D Sc m R₀ i hP H ≫
          (adjunction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀))
        (2 * (n + l)) := by
    simpa only [series, Category.assoc] using he
  rw [hs, hi, koszulSign_one_one, neg_one_zsmul, sub_neg_eq_add]
  exact series_slide _ (shiftedPreDot_isUnit D Sc m R₀ i hi H) _ _ _ hy'

/-- `evaluatedMixedBend_odd_slideOf` with the odd Koszul sign evaluated. -/
theorem evaluatedMixedBend_odd_slide_neg
    (hdot : TruncatedAppendDotNilpotent D Sc reservoirCutoff bound) (i : I) (hi : D.parity i = 1)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) :
    evaluatedMixedBend D Sc m reservoirCutoff bound i hP H ≫
        evaluatedPostDot D Sc m reservoirCutoff bound i H -
      (-1 : k) •
        (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m reservoirCutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫
        (adjunction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).unit.app
          (H.obj N₀) := by
  have hs := evaluatedMixedBend_odd_slideOf D Sc m reservoirCutoff bound hdot i hi hP H
  simpa only [hi, koszulSign_one_one, neg_one_zsmul, neg_one_smul] using hs

end ProbeVacuumCap
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Column moments of a positive-height inverse on the tensor vacuum

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8 (the left-bubble series of `AdjunctionBubbleSeries.left_odd`).

On the prescribed tensor vacuum at an odd colour, take any column
`a : V ⟶ X` of positive height `h` against the actual A6 bend: `a` is killed
by the bend and `a ≫ x^j ≫ v = δ_(j,h-1)` for `j < h`, where `x` is the
shifted pre dot and `v` the shifted pre cap. With the actual mate slide
(`q = -1`), the probe `(x² + 1)^m`, the reservoir window and the reservoir
moments `tensorPowerVacuumCap_moment_even/odd`, the decoded column moments
are the coefficients of the substituted series of `left_odd`
(`tensorVacuumColumn_odd_moments`): the moment `a ≫ x^(h-1+2s) ≫ v` acts
on the coefficient chart as left multiplication by the `s`-th coefficient
of `C(-w)(1 + w)^(-m)`, and `a ≫ x^(h+2s) ≫ v` by `±δ` times it.

The identity is transported from `End V` to linear operators on the
coefficient quotient by evaluating at the vacuum point and conjugating with
the decode chart (`tensorVacuumEndDecode`). No bubble value, inverse row or
factor action is assumed; the column is arbitrary subject to its defining
window. See `docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
open Finset
universe u

section Generic

variable {I' X' k' : Type u} [AddCommGroup X'] [CommRing k'] {C : Type*} [Category C]
  [Preadditive C] [Linear k' C] {Xo Yo V' : C}

/-- The odd inverse-column moment identity for an arbitrary column `a`, read through
an algebra map `ρ` on `End V'`: with the mate slide at `q = -1`, the odd probe, the
two windows and the reservoir series `T(z) = A(z²)(1 + e z)`, the column moments are
the substituted-series coefficients. -/
theorem column_moments_of_slide (D : SKM.Datum I' X') {R : Type*} [Ring R] [Algebra k' R]
    (φ : MvPolynomial (I' × ℕ) k' →ₐ[k'] R) (ρ : End V' →ₐ[k'] R) (P : I' → ℕ) (i : I')
    (hi : D.parity i = 1) (h N : ℕ) (hh : 0 < h) (hN : 0 < N) (hhN : h + N = 2 * P i)
    (e : R) (he : e * e = 0) (x : End Xo) (y : End Yo) (s : Xo ⟶ Yo) (u : V' ⟶ Yo)
    (v : Xo ⟶ V') (ell : Yo ⟶ V') (a : V' ⟶ Xo)
    (hslide : s ≫ y - (-1 : k') • (x ≫ s) = v ≫ u) (has : a ≫ s = 0)
    (hprobe : SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k') ^ P i).coeff n) (h + N) x = 0)
    (hcol : ∀ j < h, a ≫ (x ^ j) ≫ v = if j + 1 = h then 𝟙 V' else 0)
    (hwin : ∀ j < N, u ≫ (y ^ j) ≫ ell = if j + 1 = N then 𝟙 V' else 0)
    (hT : PowerSeries.mk (fun l => ρ (u ≫ (y ^ (N - 1 + l)) ≫ ell)) =
      PowerSeries.map φ.toRingHom (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k' i)) 1)) *
        (1 + PowerSeries.C e * PowerSeries.X))
    (n : ℕ) :
    ρ (a ≫ (x ^ (h - 1 + 2 * n)) ≫ v) = φ (PowerSeries.coeff n
        (VacuumSeries.substitutedSeries k' (SKM.SYM.probeSeries D k' P) i)) ∧
      ρ (a ≫ (x ^ (h + 2 * n)) ≫ v) = e * φ (PowerSeries.coeff n
        (VacuumSeries.substitutedSeries k' (SKM.SYM.probeSeries D k' P) i)) := by
  refine SwappedVacuum.odd_inverse_column_moments D φ P i hi h N hh hN hhN e he
    (fun j => ρ (a ≫ (x ^ j) ≫ v)) (fun j => ρ (u ≫ (y ^ j) ≫ ell)) ?_ ?_ ?_ ?_ hT n
  · intro j hj
    simp only [hcol j hj]
    split_ifs
    exacts [map_one ρ, map_zero ρ]
  · intro j hj
    simp only [hwin j hj]
    split_ifs
    exacts [map_one ρ, map_zero ρ]
  · intro d
    have h0 := congrArg ρ (SwappedVacuum.column_reservoir_relation (-1 : k') (by norm_num)
      x y s u v ell a (h + N) _ hslide has hprobe d)
    rw [map_zero, map_sum] at h0
    rw [← h0]
    refine sum_congr rfl fun n _ => ?_
    rw [map_smul, map_sum]
    refine congrArg _ (sum_congr rfl fun j _ => ?_)
    rw [map_smul, ← map_mul, End.mul_def]
  · intro mm
    have h0 := congrArg ρ (SwappedVacuum.column_probe_relation x v a (h + N) _ hprobe mm)
    rw [map_zero, map_sum] at h0
    rw [← h0]
    refine sum_congr rfl fun n _ => ?_
    rw [map_smul]

end Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1

variable (hdot :
  TruncatedAppendDotNilpotent D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1))

local notation "W₀" => Functor.obj (restriction (contentInclusion D Sc cutoff bound (0 : Multiset I)))
  (weightedVacuum D Sc cutoff L)
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "V" => Superfunctor.obj H N₀
local notation "star" => (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

/-- The decode chart of the tensor vacuum value, with its input chart as inverse. -/
def tensorVacuumDecodeEquiv : (V).obj star ≃ₗ[k] AQ :=
  LinearEquiv.ofLinearMap (tensorVacuumDecodeLinear D Sc m cutoff L)
    (tensorVacuumInputLinear D Sc m cutoff L)
    (LinearMap.ext (tensorVacuumDecode_input D Sc m cutoff L))
    (LinearMap.ext (tensorVacuumInput_decode D Sc m cutoff L))

/-- Endomorphisms of the tensor vacuum value, evaluated at the vacuum point
and read in the decode chart. -/
def tensorVacuumEndDecode : End V →ₐ[k] Module.End k AQ :=
  ((tensorVacuumDecodeEquiv D Sc m cutoff L).conjAlgEquiv k).toAlgHom.comp
    ((svecEndEvaluation ((V).obj star)).comp (supernaturalEndEvaluation V star))

theorem tensorVacuumEndDecode_apply (f : End V) (z : (V).obj star) :
    tensorVacuumEndDecode D Sc m cutoff L f (tensorVacuumDecodeLinear D Sc m cutoff L z) =
      tensorVacuumDecodeLinear D Sc m cutoff L (f.total star z) := by
  change tensorVacuumDecodeLinear D Sc m cutoff L (f.total star
    (tensorVacuumInputLinear D Sc m cutoff L (tensorVacuumDecodeLinear D Sc m cutoff L z))) = _
  rw [tensorVacuumInput_decode]

variable (i : I)
local notation "K" => contentAppend D Sc cutoff bound (0 : Multiset I) [i]

/-- An endomorphism whose evaluation at the vacuum point is read in the decode
chart as `g` decodes to `g`. -/
theorem tensorVacuumEndDecode_eq_of (f : End V) (g : Module.End k AQ)
    (hfg : ∀ z, tensorVacuumDecodeLinear D Sc m cutoff L (f.total star z) =
      g (tensorVacuumDecodeLinear D Sc m cutoff L z)) :
    tensorVacuumEndDecode D Sc m cutoff L f = g := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨z, rfl⟩ := (tensorVacuumDecodeEquiv D Sc m cutoff L).surjective w
  exact (tensorVacuumEndDecode_apply D Sc m cutoff L f z).trans (hfg z)

/-- Left multiplication by the polynomial coefficients on the coefficient quotient. -/
private def coefficientLmul : MvPolynomial (I × ℕ) k →ₐ[k] Module.End k AQ :=
  (Algebra.lmul k AQ).comp (polynomialToPower D cutoff L)

omit [Fintype I] in
private theorem coefficientLmul_apply (p : MvPolynomial (I × ℕ) k) (w : AQ) :
    coefficientLmul D cutoff L p w = polynomialToPower D cutoff L p * w := rfl

omit [Fintype I] in
private theorem coefficientLmul_ringHom_apply (p : MvPolynomial (I × ℕ) k) (w : AQ) :
    (coefficientLmul D cutoff L).toRingHom p w = polynomialToPower D cutoff L p * w := rfl

omit [Fintype I] in
private theorem lmul_apply' (a w : AQ) : Algebra.lmul k AQ a w = a * w := rfl

omit [Fintype I] in
private theorem end_mul_apply' (f g : Module.End k AQ) (w : AQ) : (f * g) w = f (g w) := rfl

private theorem unit_cap_closure (hN : 0 < cutoff i) (n : ℕ) :
    (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN = tensorUnitCapClosure D Sc m cutoff L i hN n := by
  rw [tensorUnitCapClosure, unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  rfl

omit [Fintype I] in
private theorem odd_coefficient_commute (hi : D.parity i = 1) (p : MvPolynomial (I × ℕ) k) :
    Commute (polynomialToPower D cutoff L p) ((-1 : k) ^ (cutoff i + 1) •
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) :=
  (((SKM.SYM.polynomialInclude_commute D k p (SKM.SYM.delta D k ⟨i, hi⟩)).map
    (coefficientPowerQuotientMap D cutoff L)).smul_right _)

private theorem reservoir_even_coefficient (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + 2 * r)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN) =
      (coefficientLmul D cutoff L).toRingHom (PowerSeries.coeff r
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) := by
  refine tensorVacuumEndDecode_eq_of D Sc m cutoff L _ _ fun z => ?_
  rw [unit_cap_closure D Sc m cutoff L i hN, coefficientLmul_ringHom_apply]
  have hm := tensorPowerVacuumCap_moment_even D Sc m cutoff L i hi hN r z
  show _ = completeCoefficient D cutoff L i r * _
  convert hm using 3

private theorem reservoir_odd_coefficient (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫
          (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + (2 * r + 1))) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN) =
      (coefficientLmul D cutoff L).toRingHom (PowerSeries.coeff r
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) *
        Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) := by
  refine tensorVacuumEndDecode_eq_of D Sc m cutoff L _ _ fun z => ?_
  rw [unit_cap_closure D Sc m cutoff L i hN, end_mul_apply', lmul_apply',
    coefficientLmul_ringHom_apply, ← mul_assoc, (odd_coefficient_commute D cutoff L i hi _).eq,
    smul_mul_assoc]
  convert tensorPowerVacuumCap_moment_odd D Sc m cutoff L i hi hN r z using 3
  rfl

private theorem tensorVacuum_reservoir_series (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    PowerSeries.mk (fun l => tensorVacuumEndDecode D Sc m cutoff L
        ((adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ (cutoff i - 1 + l)) ≫
          tensorPowerVacuumCap D Sc m cutoff L i hN)) =
      PowerSeries.map (coefficientLmul D cutoff L).toRingHom (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1)) *
        (1 + PowerSeries.C (Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩))) * PowerSeries.X) :=
  SwappedVacuum.mk_eq_expand_mul_one_add (coefficientLmul D cutoff L).toRingHom _ _ _
    (reservoir_even_coefficient D Sc m cutoff L i hi hN)
    (reservoir_odd_coefficient D Sc m cutoff L i hi hN)

include hdot in
private theorem odd_slide_neg (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      (-1 : k) • (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
  have hs := evaluatedMixedBend_odd_slideOf D Sc m cutoff bound hdot i hi hP H
  simpa only [hi, koszulSign_one_one, neg_one_zsmul, neg_one_smul] using hs

private theorem odd_probe_polynomial (hi : D.parity i = 1) (h : ℕ) (hhN : h + cutoff i = 2 * m i) :
    SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff n) (h + cutoff i)
      (shiftedPreDot D Sc m R₀ i H) = 0 := by
  rw [hhN]
  have hb : (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree ≤ 2 :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le (Polynomial.natDegree_X_pow_le 2) (by simp))
  have hd : ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).natDegree ≤ 2 * m i := by
    calc
      _ ≤ m i * (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree := Polynomial.natDegree_pow_le
      _ ≤ m i * 2 := Nat.mul_le_mul_left (m i) hb
      _ = 2 * m i := Nat.mul_comm _ _
  rw [SwappedVacuum.capPolynomial,
    ← Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd) (shiftedPreDot D Sc m R₀ i H)]
  simp only [map_pow, map_add, Polynomial.aeval_X, map_one]
  exact shiftedPreDot_odd_polynomial D Sc m R₀ i hi H

omit [Fintype I] in
private theorem odd_coefficient_sq (hi : D.parity i = 1) :
    Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
        coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
      Algebra.lmul k AQ ((-1 : k) ^ (cutoff i + 1) •
        coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) = 0 := by
  have h2 := SKM.SYM.delta_sq D k ⟨i, hi⟩
  rw [pow_two] at h2
  rw [← map_mul, smul_mul_smul_comm, ← map_mul, h2, map_zero, smul_zero, map_zero]

include hdot in
/-- **Odd-colour column moments on the tensor vacuum.** For a column `a`
killed by the actual A6 bend with the column window of height `h`, where
`h + cutoff i = 2 m i`, the decoded column moments are the coefficients of
the substituted series of `AdjunctionBubbleSeries.left_odd`; the odd moments
carry the normalized odd coefficient `(-1)^(cutoff i + 1) δ`. -/
theorem tensorVacuumColumn_odd_moments
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (h : ℕ) (hh : 0 < h) (hhN : h + cutoff i = 2 * m i)
    (a : V ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (has : a ≫ evaluatedMixedBend D Sc m cutoff bound i hP H = 0)
    (hcol : ∀ j < h, a ≫ (shiftedPreDot D Sc m R₀ i H ^ j) ≫ shiftedPreCap D Sc m R₀ i hP H =
      if j + 1 = h then 𝟙 V else 0)
    (s : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + 2 * s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z ∧
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h + 2 * s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  have hwin : ∀ j < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ j) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if j + 1 = cutoff i then 𝟙 V else 0 :=
    fun j hj => tensorPowerVacuumCap_window D Sc m cutoff L i hN j hj
  have hmom := column_moments_of_slide D (coefficientLmul D cutoff L)
    (tensorVacuumEndDecode D Sc m cutoff L) m i hi h (cutoff i) hh hN hhN
    _ (odd_coefficient_sq D cutoff L i hi) (shiftedPreDot D Sc m R₀ i H)
    (evaluatedPostDot D Sc m cutoff bound i H) (evaluatedMixedBend D Sc m cutoff bound i hP H)
    ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
    (tensorPowerVacuumCap D Sc m cutoff L i hN) a
    (odd_slide_neg D Sc m cutoff L hdot i hi hP) has
    (odd_probe_polynomial D Sc m cutoff L i hi h hhN) hcol hwin
    (tensorVacuum_reservoir_series D Sc m cutoff L i hi hN) s
  constructor
  · have e1 := tensorVacuumEndDecode_apply D Sc m cutoff L
      (a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + 2 * s)) ≫ shiftedPreCap D Sc m R₀ i hP H) z
    rw [hmom.1, coefficientLmul_apply] at e1
    exact e1.symm
  · have e2 := tensorVacuumEndDecode_apply D Sc m cutoff L
      (a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h + 2 * s)) ≫ shiftedPreCap D Sc m R₀ i hP H) z
    rw [hmom.2, end_mul_apply', lmul_apply', coefficientLmul_apply] at e2
    exact e2.symm

include hdot in
/-- **Chosen inverse column.** If the cap window `[bend; x^n ≫ v]_(n < h)` of the actual A6
bend has an entrywise inverse `(j, A)` (`IsCapInverse`), its last padded column `A (h - 1)`
has the substituted-series moments of `tensorVacuumColumn_odd_moments`. -/
theorem tensorVacuumCapInverse_odd_moments
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (h : ℕ) (hh : 0 < h) (hhN : h + cutoff i = 2 * m i)
    (jY : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (A : Fin h → (V ⟶ shiftedPreSourceObject D Sc m R₀ i H))
    (hA : SwappedAssembly.ProbeWindow.IsCapInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n : Fin h => (shiftedPreDot D Sc m R₀ i H ^ (n : ℕ)) ≫ shiftedPreCap D Sc m R₀ i hP H)
      jY A)
    (s : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((A ⟨h - 1, by omega⟩ ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + 2 * s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z ∧
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((A ⟨h - 1, by omega⟩ ≫ (shiftedPreDot D Sc m R₀ i H ^ (h + 2 * s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
          coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        (polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) :=
  by
  have hcol : ∀ j < h, A ⟨h - 1, by omega⟩ ≫ (shiftedPreDot D Sc m R₀ i H ^ j) ≫
      shiftedPreCap D Sc m R₀ i hP H = if j + 1 = h then 𝟙 V else 0 := by
    intro j hj
    have e := hA.2.2.2.1 ⟨h - 1, by omega⟩ ⟨j, hj⟩
    dsimp only at e
    rw [e]
    by_cases hj' : j + 1 = h
    · have hf : (⟨h - 1, by omega⟩ : Fin h) = ⟨j, hj⟩ := Fin.ext (by dsimp only; omega)
      simp only [hf, hj', ↓reduceIte]
    · have hf : ¬((⟨h - 1, by omega⟩ : Fin h) = ⟨j, hj⟩) := fun e => hj' (by
        rw [Fin.ext_iff] at e; dsimp only at e; omega)
      simp only [hf, hj', ↓reduceIte]
  exact tensorVacuumColumn_odd_moments D Sc m cutoff L hdot i hi hP hN h hh hhN
    (A ⟨h - 1, by omega⟩) (hA.2.1 _) hcol s z

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The whole-output tensor input at the vacuum weights

SwappedVacuumCoordinates §§2–3: the tensor input used by the native
pre-cap retains every output block. Its empty-probe pullback is the
specified supported tensor Hom, with both weight presentations retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open CyclotomicAction SwappedAssembly
universe u
local instance tensorWholeHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛR : X)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "W" => ReservoirWordValue.initialValue D ΛR Sc cutoff L

private def tensorOutputFunctor : ProbeVacuumCap.modulePiCategory D Sc m ⥤
    ELVWeightProduct D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0) :=
  Functor.pi' fun β => (VacuumTensor.superfunctor (W β) (probeOldVacuumObject D Sc m)).toFunctor

private instance : (tensorOutputFunctor D Sc m cutoff L ΛR).Additive where
  map_add := funext fun β => (VacuumTensor.superfunctor (W β)
    (probeOldVacuumObject D Sc m)).toFunctor.map_add
private instance : (tensorOutputFunctor D Sc m cutoff L ΛR).Linear k where
  map_smul f r := funext fun β => (VacuumTensor.superfunctor (W β)
    (probeOldVacuumObject D Sc m)).toFunctor.map_smul r f
private instance : IsSuperfunctor k (tensorOutputFunctor D Sc m cutoff L ΛR) where
  map_mem hf β := IsSuperfunctor.map_mem
    (F := (VacuumTensor.superfunctor (W β) (probeOldVacuumObject D Sc m)).toFunctor) hf

/-- Tensor with the full chosen reservoir family before empty-probe evaluation. -/
def tensorOutput : ProbeVacuumCap.modulePiCategory D Sc m ⟶
    elvWeightSpace D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0) :=
  ⟨tensorOutputFunctor D Sc m cutoff L ΛR⟩

omit [Fintype I] in
/-- The empty reservoir word has its prescribed original weight. -/
theorem reservoirWeight_empty : ReservoirWord.weight D ΛR 0 = -ΛR := by
  simp [ReservoirWord.weight]

/-- The same full tensor output, at the weight used by the native bend chart. -/
def tensorOutputAt : ProbeVacuumCap.modulePiCategory D Sc m ⟶
    elvWeightSpace D Sc cutoff bound ΛR (-ΛR) :=
  reservoirWeight_empty D ΛR ▸ tensorOutput D Sc m cutoff L ΛR

private theorem output_cast_block
    {A : PiSCat.{u,u,u+1} k} {x y : X} (h : x = y)
    (F : A ⟶ elvWeightSpace D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR x)
    (δ : WeightBlocks D ΛR y) :
    (show A ⟶ elvWeightSpace D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR y from
      h ▸ F).comp (elvBlockEval D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR δ) =
      F.comp (elvBlockEval D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR
        ⟨δ.1, δ.2.trans h.symm⟩) := by
  subst y
  rfl

/-- The selected block is the native tensor functor used by the moment maps. -/
theorem tensorOutputAt_empty :
    (tensorOutputAt D Sc m cutoff L ΛR).comp
        (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)) =
      VacuumTensor.probeFunctor D Sc m cutoff bound
        ((BalancedInduction.restriction (contentInclusion D Sc cutoff bound (0 : Multiset I))).obj
          (PowerVacuumCoefficient.weightedVacuum D Sc cutoff L)) := by
  rw [tensorOutputAt, output_cast_block]
  rfl

variable (ΛP : X)

private theorem comp_cast_heq
    {x y : X} (h : x = y)
    (G : ProbeVacuumCap.modulePiCategory D Sc m ⟶ elvWeightSpace D Sc cutoff bound ΛR x) :
    HEq ((emptyProbe D Sc m ΛP).comp
      (show ProbeVacuumCap.modulePiCategory D Sc m ⟶ elvWeightSpace D Sc cutoff bound ΛR y from
        h ▸ G)) ((emptyProbe D Sc m ΛP).comp G) := by
  subst y
  rfl

private theorem input_cast_heq
    {x y z : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR z) :
    HEq (show probeOldWeightSpace D Sc m ΛP y ⟶ elvWeightSpace D Sc cutoff bound ΛR z from
      h ▸ F) F := by
  subst y
  rfl

omit [Fintype I] in
private theorem homWeight_inverse_obj_heq
    (TT WW : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    {a a' b b' : X} (ha : a = a') (hb : b = b')
    (Z : SKM.homWeightSector TT.obj WW.obj a' b') :
    HEq ((SKM.homWeightEquivalence TT WW ha hb).inverse.obj Z) Z := by
  subst a'
  subst b'
  rfl

variable
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "T" => probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hcP
local notation "R" => elvRouquierFamily D (parameterTwist D Sc) cutoff bound ΛR hcR

private theorem probeWeight_zero : (P).muP (0,0) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
private theorem reservoirWeight_zero : (P).muM (0,0) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

/-- The full tensor input in the precise weight presentations of the padded bend. -/
def tensorSectorInput : (P).H (0,0) :=
  (SKM.homWeightEquivalence T R
    (probeWeight_zero D Sc m cutoff L ΛR ΛP hcP hcR)
    (reservoirWeight_zero D Sc m cutoff L ΛR ΛP hcP hcR)).inverse.obj
      (preCapInput D (parameterTwist D Sc) m ΛP hcP
        (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR)
          (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR))

/-- Both presentations retain the same selected supported tensor Hom. -/
theorem tensorSectorInput_eq_supported :
    tensorSectorInput D Sc m cutoff L ΛR ΛP hcP hcR =
      (SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR).obj := by
  apply eq_of_heq
  have h₁ := homWeight_inverse_obj_heq D T R
    (probeWeight_zero D Sc m cutoff L ΛR ΛP hcP hcR)
    (reservoirWeight_zero D Sc m cutoff L ΛR ΛP hcP hcR)
    (preCapInput D (parameterTwist D Sc) m ΛP hcP
      (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR)
        (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR))
  have h₂ := comp_cast_heq D (parameterTwist D Sc) m cutoff L ΛR ΛP
    (reservoirWeight_empty D ΛR)
    (tensorOutput D (parameterTwist D Sc) m cutoff L ΛR)
  have h₃ : HEq (SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR).obj
      (selectedHom D (parameterTwist D Sc) m cutoff ΛP ΛR L) := by
    rw [SupportedSectors.tensorVacuum_obj]
    unfold SupportedSectors.tensorHomAt
    exact input_cast_heq D (parameterTwist D Sc) m cutoff L ΛR ΛP
      (SupportedSectors.probeWeight_vacuum D ΛP).symm _
  exact (h₁.trans h₂).trans h₃.symm

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end
