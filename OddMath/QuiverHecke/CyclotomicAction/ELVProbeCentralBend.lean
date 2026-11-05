import OddMath.QuiverHecke.CyclotomicAction.ELVProbeLocalPreAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionNilpotence
import Mathlib.RingTheory.Nilpotent.Basic
import OddMath.SKM.RouquierHomMixedRational

/-! # Evaluation of the mixed diagonal at the regular probe

SwappedHomInversion §3 (A6), (3)–(5). The inverse probe dot is used only on
the scalar-evaluated regular probe carrier. The evaluated bend uses the
chosen post unit and the constructed pre counit, in that order. Attachment
to the complete swapped matrix is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
namespace OddMath.QuiverHecke.ELVOld
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
theorem diagonalPostDot_pow_zero (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I) :
    ∃ n : ℕ, 0 < n ∧ ∀ H : modulePiCategory D Sc m ⟶ R₀,
      diagonalPostDot D Sc m reservoirCutoff bound i H ^ n = 0 := by
  obtain ⟨n, hn, hp⟩ := contentInductionDot_module_pow_zero D Sc reservoirCutoff sy hc bound [] i
  refine ⟨n, hn, fun H => ?_⟩
  have h := hp (shiftedPreSourceObject D Sc m R₀ i H)
  rw [contentInductionDot_component] at h
  exact h

/-- The target's restricted reservoir dot has a positive nilpotence
exponent at this fixed content, on every regular-probe Hom object. -/
theorem evaluatedPostDot_pow_zero (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I) :
    ∃ n : ℕ, 0 < n ∧ ∀ H : modulePiCategory D Sc m ⟶ R₀,
      evaluatedPostDot D Sc m reservoirCutoff bound i H ^ n = 0 := by
  obtain ⟨n, hn, hp⟩ := contentInductionDot_module_pow_zero D Sc reservoirCutoff sy hc bound [] i
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
end OddMath.QuiverHecke.ELVOld
