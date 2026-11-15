import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumBends
import OddMath.QuiverHecke.CyclotomicAction.ProbeCentral
import OddMath.QuiverHecke.CyclotomicAction.ProbeMixedBraid
import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowEquations
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWordSeries
import OddMath.SKM.RouquierHomWeightCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ParameterUntwist
import OddMath.QuiverHecke.SwappedAssembly.Sigma.VacuumCapInverseWindow
import OddMath.QuiverHecke.SwappedAssembly.Sigma.FactorWindowInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseBubbleEntry
import Mathlib.Tactic.Abel
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseCupInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseRightBubbleEntry

/-!
# Probe padded vacuum

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The finite even vacuum bend

SwappedHomInversion §3 (A6), (3)–(5): on an even moving colour the chosen
mixed diagonal is `(Y-X)⁻¹`, hence the negative finite geometric series.
This evaluates the same post unit and shifted pre-cap used in the odd
calculation. Other colours of the datum may be odd.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem inverse_neg_unit {R : Type*} [Ring R] (a : R) (ha : IsUnit a) :
    Ring.inverse (-a) = -Ring.inverse a := by
  calc
    Ring.inverse (-a) = Ring.inverse (-a) * 1 := (mul_one _).symm
    _ = Ring.inverse (-a) * ((-a) * (-Ring.inverse a)) := by
      rw [neg_mul_neg, Ring.mul_inverse_cancel _ ha]
    _ = -Ring.inverse a := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ ha.neg, one_mul]

private theorem negative_even_series {R : Type*} [Ring R] (x : Rˣ) (y : R)
    (hxy : Commute (x : R) y) (n : ℕ) (hn : y ^ n = 0) :
    Ring.inverse (y - (x : R)) =
      ∑ r ∈ Finset.range n, (-1 : ℤ) • (y ^ r * (↑x⁻¹ : R) ^ (r + 1)) := by
  rw [← neg_sub (x : R) y, inverse_neg_unit _ (SKM.mixedEvenDenominator_isUnit x y hxy n hn),
    SKM.mixedEvenInverse_expansion x y hxy n hn, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [neg_one_zsmul, (hxy.units_inv_left.pow_pow (r + 1) r).eq]

private theorem map_inverse {A B : Type*} [Ring A] [Ring B]
    (f : A →* B) (x : A) (hx : IsUnit x) : f (Ring.inverse x) = Ring.inverse (f x) := by
  obtain ⟨v, rfl⟩ := hx
  change f (Ring.inverse (v : A)) = Ring.inverse ((Units.map f v : Bˣ) : B)
  simp only [Ring.inverse_unit, Units.coe_map_inv]

namespace ProbeVacuumCap
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "J" => contentAppend D Sc cutoff bound (0 : Multiset I)

/-- The post-induced even probe dot is a unit on the selected mixed carrier. -/
theorem diagonalPreDot_even_isUnit (i : I) (hi : D.parity i = 0)
    (H : modulePiCategory D Sc m ⟶ R₀) : IsUnit (diagonalPreDot D Sc m cutoff bound i H) :=
  (shiftedPreDot_even_isUnit D Sc m R₀ i hi H).map ((induction (J [i])).mapEnd _)

/-- The literal even rational diagonal is the negative finite geometric series. -/
theorem evaluatedMixedDiagonal_even_expansion (i : I) (hi : D.parity i = 0)
    (H : modulePiCategory D Sc m ⟶ R₀) (n : ℕ)
    (hn : diagonalPostDot D Sc m cutoff bound i H ^ n = 0) :
    evaluatedMixedDiagonal D Sc m cutoff bound i H =
      ∑ r ∈ Finset.range n, (-1 : ℤ) •
        ((induction (J [i])).map (Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1)) ≫
          diagonalPostDot D Sc m cutoff bound i H ^ r) := by
  rw [evaluatedMixedDiagonal, ite_eq_left hi]
  let x := diagonalPreDot D Sc m cutoff bound i H
  let y := diagonalPostDot D Sc m cutoff bound i H
  have hc : Commute x y := by
    have h := diagonal_dots_exchange D Sc m cutoff bound i H
    simp only [hi, koszulSign_zero_left, one_smul] at h
    exact h.symm
  obtain ⟨v, hv⟩ := diagonalPreDot_even_isUnit D Sc m cutoff bound i hi H
  change (v : End _) = x at hv
  have hs := negative_even_series v y (by simpa only [hv] using hc) n hn
  have hv' : (↑v⁻¹ : End _) = Ring.inverse x := by rw [← hv, Ring.inverse_unit]
  rw [hv, hv'] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  have hmap := map_inverse ((induction (J [i])).mapEnd _)
    (shiftedPreDot D Sc m R₀ i H) (shiftedPreDot_even_isUnit D Sc m R₀ i hi H)
  change y ^ r * Ring.inverse x ^ (r + 1) = _
  rw [show Ring.inverse x = (induction (J [i])).mapEnd _
      (Ring.inverse (shiftedPreDot D Sc m R₀ i H)) from hmap.symm, ← map_pow]
  rfl

/-- The even cap/unit bend retains a constant negative coefficient in every term. -/
theorem evaluatedMixedBend_even_expansion (i : I) (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) (n : ℕ)
    (hn : diagonalPostDot D Sc m cutoff bound i H ^ n = 0) :
    evaluatedMixedBend D Sc m cutoff bound i hP H =
      ∑ r ∈ Finset.range n, (-1 : ℤ) •
        ((Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1)) ≫
          shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction (J [i])).unit.app (H.obj N₀) ≫
            evaluatedPostDot D Sc m cutoff bound i H ^ r) := by
  rw [evaluatedMixedBend, evaluatedMixedDiagonal_even_expansion D Sc m cutoff bound i hi H n hn]
  exact postBend_sum _ (contentAppendTo_supernatural D Sc cutoff bound rfl rfl (firstDot_parity D Sc i []))
    _ _ _ (shiftedPreCap_mem D Sc m R₀ i hP H)
    (fun r => Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1)) (fun _ => -1) n

end ProbeVacuumCap
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The ordered odd vacuum bend series

SwappedHomInversion §3 (4)–(5): the finite ordered series of prescribed
negative pre-caps and dotted post-units equals the evaluated A6 bend.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction
universe u
local instance bendSeriesHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I) {muP nuR : X} (edgeP : -ΛP + D.α i = -muP)
  (edgeR : -ΛR + D.α i = nuR) (β : I →₀ ℕ)
variable (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ elvWeightSpace D Sc cutoff bound ΛR (-ΛR))
local instance bendSeriesProbeDotIso [Fact Sc.PureNilpotent] : IsIso (((probeOldRouquierFamily D Sc m ΛP hcP)).dot i edgeP) :=
  (isUnit_iff_isIso _).mp (probeOldRouquierFamily_dot_isUnit D Sc m ΛP hcP i edgeP)

/-- The given chronological series keeps each negative pre-cap and
post-unit as the prescribed Hom maps before regular-probe evaluation. -/
def vacuumBendWordSum [Fact Sc.PureNilpotent] (N : ℕ) :=
  -∑ r ∈ Finset.range N, (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) •
    (((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP (r + 1) (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H) ≫
      SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR))

private theorem odd_coefficient (r : ℕ) :
    -((koszulSign (1 : ZMod 2) 1) ^ (r + 1)) = (-1 : ℤ) ^ r := by
  rw [koszulSign_one_one, pow_succ]
  ring

/-- At any given native reservoir nilpotence exponent, the actual
finite pre-cap/post-unit word sum is exactly the evaluated odd A6 bend.
The raw shifted pre-dot and raw reservoir unit/dot are retained. -/
theorem vacuumBendWordSum_odd [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1)
    (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D Sc m cutoff bound i (vacuumBendBlock D Sc m cutoff bound ΛR H) ^ n = 0) :
    vacuumBendWordSum D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H (2 * n) ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      ProbeVacuumCap.evaluatedMixedBend D Sc m cutoff bound i hP (vacuumBendBlock D Sc m cutoff bound ΛR H) := by
  rw [ProbeVacuumCap.evaluatedMixedBend_odd_expansion D Sc m cutoff bound i hi hP (vacuumBendBlock D Sc m cutoff bound ΛR H) n hn]
  simp only [vacuumBendWordSum, Preadditive.neg_comp, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [vacuumBendMonomial_eq D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H hP hi (r + 1) r]
  have hs : -((koszulSign (D.parity i) (D.parity i)) ^ (r + 1)) = (-1 : ℤ) ^ r := by
    rw [hi, odd_coefficient]
  rw [← neg_zsmul, hs]
  congr 1

/-- Even colour: at any given native reservoir nilpotence exponent `n`, the actual
finite pre-cap/post-unit word sum of length `n` is exactly the evaluated even A6 bend. -/
theorem vacuumBendWordSum_even [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0)
    (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D Sc m cutoff bound i (vacuumBendBlock D Sc m cutoff bound ΛR H) ^ n = 0) :
    vacuumBendWordSum D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H n ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      ProbeVacuumCap.evaluatedMixedBend D Sc m cutoff bound i hP (vacuumBendBlock D Sc m cutoff bound ΛR H) := by
  rw [ProbeVacuumCap.evaluatedMixedBend_even_expansion D Sc m cutoff bound i hi hP (vacuumBendBlock D Sc m cutoff bound ΛR H) n hn]
  simp only [vacuumBendWordSum, Preadditive.neg_comp, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [vacuumBendMonomial_even D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H hP hi (r + 1) r]
  have hs : -((koszulSign (D.parity i) (D.parity i)) ^ (r + 1)) = (-1 : ℤ) := by
    rw [hi, koszulSign_zero_left, one_pow]
  rw [← neg_zsmul, hs]
  congr 1

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
end

end

section

/-! # The padded Dx bend on the regular vacuum probe

SwappedHomInversion §3 (4)–(5) and SwappedVacuumCoordinates §4:
evaluate the specified padded mixed entry at the vacuum sector. Its
finite ordered expansion has the same raw dots, normalized pre-cap and
reservoir unit as the evaluated vacuum bend.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u
local instance paddedVacuumBendHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private theorem bendFunctorEnd_nilpotent_congr
    {C A : Type*} [Category C] [Preadditive C] [Category A] [Preadditive A]
    {E F : C ⥤ A} [E.Additive] [F.Additive] (h : E = F)
    {U : C} (a : End U) (ha : IsNilpotent (bendFunctorEnd E U a)) :
    IsNilpotent (bendFunctorEnd F U a) := by
  subst F
  exact ha

private theorem mapped_square {C A : Type*} [Category C] [Category A]
    (E : C ⥤ A) {X Y U V : C} {a : X ⟶ Y} {b : U ⟶ V}
    (s : X ≅ U) (t : Y ≅ V) (h : a ≫ t.hom = s.hom ≫ b) :
    E.map a ≫ (E.mapIso t).hom = (E.mapIso s).hom ≫ E.map b := by
  simpa only [Functor.map_comp, Functor.mapIso_hom] using congrArg E.map h

private theorem finite_weighted_sum_congr {M : Type*} [AddCommGroup M]
    (f g : ℕ → M) (q : ℤ) (N : ℕ) (h : ∀ r, f r = g r) :
    (-∑ r ∈ Finset.range N, q ^ (r + 1) • f r) =
      -∑ r ∈ Finset.range N, q ^ (r + 1) • g r := by
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro r hr
  exact congrArg (fun w => q ^ (r + 1) • w) (h r)

private theorem finite_series_charts {C : Type*} [Category C] [Preadditive C]
    {A B X Y U V : C} (s : A ≅ X) (t : B ≅ Y) (u : X ≅ U) (v : Y ≅ V)
    (a : ℕ → (X ⟶ Y)) (b : ℕ → (U ⟶ V)) (q : ℤ) (N : ℕ)
    (h : ∀ r, a r ≫ v.hom = u.hom ≫ b r) :
    (-∑ r ∈ Finset.range N, q ^ (r + 1) • (s.hom ≫ a r ≫ t.inv)) ≫ (t ≪≫ v).hom =
      (s ≪≫ u).hom ≫ (-∑ r ∈ Finset.range N, q ^ (r + 1) • b r) := by
  simp only [Iso.trans_hom, Preadditive.neg_comp, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_neg, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [h r]

private theorem finite_series_charts_attach {C : Type*} [Category C] [Preadditive C]
    {A B X Y U V U' V' : C} (s : A ≅ X) (t : B ≅ Y) (u : X ≅ U) (v : Y ≅ V)
    (e : U ≅ U') (f : V ≅ V') (a : ℕ → (X ⟶ Y)) (b : ℕ → (U ⟶ V))
    (q : ℤ) (N : ℕ) (h : ∀ r, a r ≫ v.hom = u.hom ≫ b r)
    (d : U' ⟶ V')
    (hb : (-∑ r ∈ Finset.range N, q ^ (r + 1) • b r) ≫ f.hom = e.hom ≫ d)
    (z : A ⟶ B)
    (hz : z = -∑ r ∈ Finset.range N, q ^ (r + 1) • (s.hom ≫ a r ≫ t.inv)) :
    z ≫ (t ≪≫ v ≪≫ f).hom = (s ≪≫ u ≪≫ e).hom ≫ d := by
  rw [hz]
  have hh := finite_series_charts s t u v a b q N h
  calc
    _ = ((-∑ r ∈ Finset.range N, q ^ (r + 1) • (s.hom ≫ a r ≫ t.inv)) ≫
        (t ≪≫ v).hom) ≫ f.hom := by simp only [Iso.trans_hom, Category.assoc]
    _ = ((s ≪≫ u).hom ≫ (-∑ r ∈ Finset.range N, q ^ (r + 1) • b r)) ≫ f.hom :=
      congrArg (fun w => w ≫ f.hom) hh
    _ = (s ≪≫ u ≪≫ e).hom ≫ d := by
      rw [Category.assoc, hb]
      simp only [Iso.trans_hom, Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance paddedVacuumZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β, elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

omit [Fintype I] in
private theorem probeWeight_zero : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP (((0, 0) : Sector I)) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
omit [Fintype I] in
private theorem reservoirWeight_zero : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM (((0, 0) : Sector I)) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

omit [Fintype I] in
private theorem homContentEvaluation_weight
    {a a' b b' : X} (h₁ : a = a') (h₂ : b = b')
    (M : (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-a')) (δ : WeightBlocks D ΛR b') :
    (SKM.homWeightEquivalence ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) h₁ h₂).functor ⋙
        homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR b' ((((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-a')) M δ =
      homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR b ((((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-a))
        ((Pi.eqToEquivalence (fun x : X => (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-x)) h₁).inverse.obj M)
        (⟨δ.1, δ.2.trans h₂.symm⟩ : WeightBlocks D ΛR b) := by
  subst a'
  subst b'
  rfl

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶ elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))

/-- The full given tensor input, through only its formal zero-sector weight chart. -/
def vacuumSectorInput : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).H (((0, 0) : Sector I)) := by
  exact ((SKM.homWeightEquivalence ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).inverse.obj (preCapInput D (parameterTwist D Sc) m ΛP hcP (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H)

private def normalVacuumEvaluation :
    SKM.homWeightSector ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T).obj ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W).obj ΛP (-ΛR) ⥤
      ContentModules D (parameterTwist D Sc) cutoff bound (0 : Multiset I) :=
  homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR (-ΛR)
    (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T).obj (-ΛP)) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)
private instance normalVacuumEvaluation_additive : ((normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).Additive :=
  homContentEvaluation_additive D (parameterTwist D Sc) cutoff bound ΛR (-ΛR)
    (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T).obj (-ΛP)) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)

/-- The evaluation retains all Hom maps before selecting the regular
probe and empty output block; its first factor only changes weight presentations. -/
def vacuumSectorEvaluation := ((SKM.homWeightEquivalence ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).functor ⋙ (normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)
instance vacuumSectorEvaluation_additive : ((vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).Additive := inferInstanceAs (((SKM.homWeightEquivalence ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).functor ⋙ (normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).Additive

def sectorRegular : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).T.obj (-((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP (((0, 0) : Sector I))) :=
  (Pi.eqToEquivalence (fun x : X => (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T)).obj (-x)) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)).inverse.obj (regularProbe D (parameterTwist D Sc) m ΛP)
def sectorEmpty : WeightBlocks D ΛR (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM (((0, 0) : Sector I))) :=
  ⟨0, (emptyBlock D ΛR).2.trans ((reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)).symm⟩

theorem vacuumSectorEvaluation_eq : (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) =
    elvProbeBendOutputEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR (((0, 0) : Sector I))
      (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)
      (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR) :=
  homContentEvaluation_weight D Sc m cutoff bound ΛP ΛR hcP hcR (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)

variable (i : I)

private theorem factorDotIso [Fact Sc.PureNilpotent] {a b : X} (h : a + D.α i = b) : IsIso (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).T.dot i h) :=
  (isUnit_iff_isIso _).mp
    (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hcP hcR i h)

/-- The source comparison includes the prescribed padded corner,
the weight equality chart and the literal normalized vacuum pre-cap chart. -/
def paddedVacuumSourceIso [Fact Sc.PureNilpotent] :=
  ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralSourceCornerIso i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨true, by trivial⟩ ≪≫
    ((normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).mapIso (SKM.homPreWeightPullbackIso ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) i (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP_preE i (((0, 0) : Sector I))) (preCapInput D (parameterTwist D Sc) m ΛP hcP (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H)) ≪≫
      vacuumPreBlockSourceIso D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP i ((show -ΛP + D.α i = -((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP (nextSector (true,i) true (((0, 0) : Sector I))) from (congrArg (fun x : X => -x + D.α i) ((probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).symm.trans (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP_preE i (((0, 0) : Sector I))))) H

/-- The target comparison includes the prescribed padded corner,
the weight equality chart and the literal reservoir unit/dot target chart. -/
def paddedVacuumTargetIso :=
  ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralTargetCornerIso i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨false, by trivial⟩ ≪≫
    ((normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR)).mapIso (SKM.homPostWeightPullbackIso ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T) ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W) (probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) (reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR) i (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM_postF i (((0, 0) : Sector I))) 0 (preCapInput D (parameterTwist D Sc) m ΛP hcP (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H)) ≪≫
      vacuumPostTarget D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i ((show -ΛR + D.α i = ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM (nextSector (false,i) false (((0, 0) : Sector I))) from (congrArg (fun x : X => x + D.α i) ((reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR))).symm.trans (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muM_postF i (((0, 0) : Sector I))))) 0 H

private theorem normalVacuumEvaluation_map
    {F G : SKM.homWeightSector
      (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).T.obj
      (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).W.obj ΛP (-ΛR)} (η : F ⟶ G) :
    (normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map η =
      η.total (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR) := rfl

variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)

private theorem paddedVacuumDx_odd_at [Fact Sc.PureNilpotent]
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D (parameterTwist D Sc) m cutoff bound i (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n = 0)
    (hDx : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).CentralPaddedDxSeparatedAt i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) (2 * n)) :
    ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  classical
  let P := elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
  let E := vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let E₀ := normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z := vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let ep := P.muP_preE i (0, 0)
  let er := P.muM_postF i (0, 0)
  let ep₀ := (congrArg (fun x : X => -x + D.α i) ha).symm.trans ep
  let er₀ := (congrArg (fun x : X => x + D.α i) hb).symm.trans er
  let : E.Additive := vacuumSectorEvaluation_additive D Sc m cutoff bound ΛP ΛR hcP hcR
  let := factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i ep
  let := factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i ep₀
  let s := P.centralSourceCornerIso i (0, 0) Z E ⟨true, by trivial⟩
  let t := P.centralTargetCornerIso i (0, 0) Z E ⟨false, by trivial⟩
  let u := E₀.mapIso (SKM.homPreWeightPullbackIso P.T P.W ha hb i ep Z₀)
  let v := E₀.mapIso (SKM.homPostWeightPullbackIso P.T P.W ha hb i er 0 Z₀)
  let e := vacuumPreBlockSourceIso D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP i ep₀ H
  let f := vacuumPostTarget D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i er₀ 0 H
  let a (r : ℕ) := E.map (SKM.homPreNegativeCap P.T P.W.obj i (P.muM (0, 0)) ep (r + 1) Z ≫
    SKM.homContentPostCup P.T.obj P.W i 0 (P.muP (0, 0)) er r Z)
  let b (r : ℕ) := E₀.map (SKM.homPreNegativeCap P.T P.W.obj i (-ΛR) ep₀ (r + 1) Z₀ ≫
    SKM.homContentPostCup P.T.obj P.W i 0 ΛP er₀ r Z₀)
  have hw (r : ℕ) : a r ≫ v.hom = u.hom ≫ b r := by
    have h := SKM.homCapCup_weight_pullback_square P.T P.W ha hb i ep er 0 Z₀
      (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (r + 1) r
    have hm := mapped_square E₀ _ _ h
    simpa only [a, b, u, v, E, Z, Z₀, vacuumSectorEvaluation, vacuumSectorInput,
      Functor.comp_map] using hm
  have hn := vacuumBendWordSum_odd D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR
    i ep₀ er₀ 0 H hP hi n hn
  have hn' : (-∑ r ∈ Finset.range (2 * n), (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) • b r) ≫
      f.hom = e.hom ≫ ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
    have hsum : (-∑ r ∈ Finset.range (2 * n), (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) • b r) =
        vacuumBendWordSum D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR
          i ep₀ er₀ 0 H (2 * n) := by
      dsimp only [vacuumBendWordSum]
      apply finite_weighted_sum_congr
      intro r
      dsimp only [b, E₀]
      exact normalVacuumEvaluation_map D Sc m cutoff bound ΛP ΛR hcP hcR _
    rw [hsum]
    exact hn
  have hs := finite_series_charts_attach s t u v e f a b
    (koszulSign (D.parity i) (D.parity i)) (2 * n) hw _ hn' _
    (P.centralPaddedDx_word_series i (0, 0) Z E
      (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i)
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) (2 * n) hDx)
  simpa only [s, t, u, v, e, f, E, E₀, Z, Z₀, P,
    paddedVacuumSourceIso, paddedVacuumTargetIso] using hs

/-- The prescribed padded Dx entry at the vacuum sector is the
evaluated odd vacuum bend through its displayed source and target charts.
Both finite-series bounds are constructed from nilpotence of the appended
dot for the twisted parameters; no endpoint, moment or bend compatibility is assumed. -/
theorem paddedVacuumDx_odd [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  let := (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP_preE i (((0, 0) : Sector I)))
  have hA := elvProbeDxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hcP hcR i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)
    (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR)
    hdot
  simp only [probeToReservoirBendCoefficientEvaluation, RingHom.comp_apply] at hA
  let : (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).Additive :=
    vacuumSectorEvaluation_additive D Sc m cutoff bound ΛP ΛR hcP hcR
  have hA' := bendFunctorEnd_nilpotent_congr
    (vacuumSectorEvaluation_eq D Sc m cutoff bound ΛP ΛR hcP hcR).symm _ hA
  obtain ⟨nA, hnA⟩ := hA' 
  obtain ⟨nB, _positive, hnB⟩ := ProbeVacuumCap.diagonalPostDot_pow_zero D (parameterTwist D Sc) m cutoff bound
    hdot i
  let n := max nA nB
  have ha' := pow_eq_zero_of_le (Nat.le_max_left nA nB) hnA
  have hb' := pow_eq_zero_of_le (Nat.le_max_right nA nB) (hnB (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
  have hD := probeToReservoirBend_odd_separated ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot)
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hcP hcR hdot) hi n ha'
  exact paddedVacuumDx_odd_at D Sc m cutoff bound ΛP ΛR hcP hcR H i hdot hP hi n hb'
    (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedDx_separated i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) (2 * n) hD)

private theorem paddedVacuumDx_even_at [Fact Sc.PureNilpotent]
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D (parameterTwist D Sc) m cutoff bound i (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n = 0)
    (hDx : ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).CentralPaddedDxSeparatedAt i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) n) :
    ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  classical
  let P := elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
  let E := vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let E₀ := normalVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z := vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := probeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := reservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let ep := P.muP_preE i (0, 0)
  let er := P.muM_postF i (0, 0)
  let ep₀ := (congrArg (fun x : X => -x + D.α i) ha).symm.trans ep
  let er₀ := (congrArg (fun x : X => x + D.α i) hb).symm.trans er
  let : E.Additive := vacuumSectorEvaluation_additive D Sc m cutoff bound ΛP ΛR hcP hcR
  let := factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i ep
  let := factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i ep₀
  let s := P.centralSourceCornerIso i (0, 0) Z E ⟨true, by trivial⟩
  let t := P.centralTargetCornerIso i (0, 0) Z E ⟨false, by trivial⟩
  let u := E₀.mapIso (SKM.homPreWeightPullbackIso P.T P.W ha hb i ep Z₀)
  let v := E₀.mapIso (SKM.homPostWeightPullbackIso P.T P.W ha hb i er 0 Z₀)
  let e := vacuumPreBlockSourceIso D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP i ep₀ H
  let f := vacuumPostTarget D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i er₀ 0 H
  let a (r : ℕ) := E.map (SKM.homPreNegativeCap P.T P.W.obj i (P.muM (0, 0)) ep (r + 1) Z ≫
    SKM.homContentPostCup P.T.obj P.W i 0 (P.muP (0, 0)) er r Z)
  let b (r : ℕ) := E₀.map (SKM.homPreNegativeCap P.T P.W.obj i (-ΛR) ep₀ (r + 1) Z₀ ≫
    SKM.homContentPostCup P.T.obj P.W i 0 ΛP er₀ r Z₀)
  have hw (r : ℕ) : a r ≫ v.hom = u.hom ≫ b r := by
    have h := SKM.homCapCup_weight_pullback_square P.T P.W ha hb i ep er 0 Z₀
      (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (r + 1) r
    have hm := mapped_square E₀ _ _ h
    simpa only [a, b, u, v, E, Z, Z₀, vacuumSectorEvaluation, vacuumSectorInput,
      Functor.comp_map] using hm
  have hn := vacuumBendWordSum_even D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR
    i ep₀ er₀ 0 H hP hi n hn
  have hn' : (-∑ r ∈ Finset.range n, (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) • b r) ≫
      f.hom = e.hom ≫ ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
    have hsum : (-∑ r ∈ Finset.range n, (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) • b r) =
        vacuumBendWordSum D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR
          i ep₀ er₀ 0 H n := by
      dsimp only [vacuumBendWordSum]
      apply finite_weighted_sum_congr
      intro r
      dsimp only [b, E₀]
      exact normalVacuumEvaluation_map D Sc m cutoff bound ΛP ΛR hcP hcR _
    rw [hsum]
    exact hn
  have hs := finite_series_charts_attach s t u v e f a b
    (koszulSign (D.parity i) (D.parity i)) n hw _ hn' _
    (P.centralPaddedDx_word_series i (0, 0) Z E
      (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i)
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) n hDx)
  simpa only [s, t, u, v, e, f, E, E₀, Z, Z₀, P,
    paddedVacuumSourceIso, paddedVacuumTargetIso] using hs

/-- Even colour: the prescribed padded Dx entry at the vacuum sector is the
evaluated even vacuum bend through its displayed source and target charts.
Both finite-series bounds are constructed from nilpotence of the appended
dot for the twisted parameters; no endpoint, moment or bend compatibility is assumed. -/
theorem paddedVacuumDx_even [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) :
    ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  let := (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).muP_preE i (((0, 0) : Sector I)))
  have hA := elvProbeDxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hcP hcR i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)
    (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR)
    hdot
  simp only [probeToReservoirBendCoefficientEvaluation, RingHom.comp_apply] at hA
  let : (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).Additive :=
    vacuumSectorEvaluation_additive D Sc m cutoff bound ΛP ΛR hcP hcR
  have hA' := bendFunctorEnd_nilpotent_congr
    (vacuumSectorEvaluation_eq D Sc m cutoff bound ΛP ΛR hcP hcR).symm _ hA
  obtain ⟨nA, hnA⟩ := hA' 
  obtain ⟨nB, _positive, hnB⟩ := ProbeVacuumCap.diagonalPostDot_pow_zero D (parameterTwist D Sc) m cutoff bound
    hdot i
  let n := max nA nB
  have ha' := pow_eq_zero_of_le (Nat.le_max_left nA nB) hnA
  have hb' := pow_eq_zero_of_le (Nat.le_max_right nA nB) (hnB (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
  have hD := probeToReservoirBend_even_separated ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)) i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot)
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hcP hcR hdot) hi n ha'
  exact paddedVacuumDx_even_at D Sc m cutoff bound ΛP ΛR hcP hcR H i hdot hP hi n hb'
    (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR)).centralPaddedDx_separated i (((0, 0) : Sector I)) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (factorDotIso D Sc m cutoff bound ΛP ΛR hcP hcR i) (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) n hD)

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
end

end

section

/-! # The padded reservoir cap rows on the regular vacuum probe

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. The cap rows of the positive two-sector matrix at the vacuum sector are
the prescribed padded reservoir caps `centralPaddedCap true n`: the raw
reservoir dot `n` times, followed by the normalized pre-Hom counit. This
file evaluates them on the regular probe. Through the same source chart as
the padded Dx entry (`paddedVacuumSourceIso`), and the weight, block and
regular-input charts of the target, the `n`-th cap row is the native
`x ^ n ≫ v`, where `x` is the shifted pre dot and `v` the shifted pre cap
(`paddedVacuumCap_eq`). No parity, moment or cap compatibility is
assumed.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u
local instance paddedVacuumCapHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Generic

private theorem total_pow_square {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F : Superfunctor k C A} (f : End F) (N : C) {B : A} (e : F.obj N ⟶ B) (y : End B)
    (h : f.total N ≫ e = e ≫ y) (n : ℕ) :
    (f ^ n).total N ≫ e = e ≫ (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, End.one_def, End.one_def]
    exact (congrArg (fun w => w ≫ e) (SuperNatTrans.id_total F.toFunctor N)).trans
      ((Category.id_comp e).trans (Category.comp_id e).symm)
  | succ n ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Superfunctor.comp_total,
      Category.assoc, ih, ← Category.assoc, h, Category.assoc]

/-- Chart bookkeeping for a cap row: a pulled-back square, a block
selection and a normalized native identity compose. -/
private theorem cap_charts_attach {C : Type*} [Category C]
    {A X U U₀ U' Y V V' : C} (s : A ≅ X) (u : X ≅ U) (hU : U = U₀) (e : U₀ ≅ U')
    (c : X ⟶ Y) (p : Y ⟶ V) (q : V ⟶ V') (c₀ : U ⟶ V) (c₁ : U₀ ⟶ V) (d : U' ⟶ V')
    (hsq : c ≫ p = u.hom ≫ c₀) (hE : c₀ = eqToHom hU ≫ c₁) (hn : c₁ ≫ q = e.hom ≫ d) :
    (s.hom ≫ c) ≫ p ≫ q = (s ≪≫ u ≪≫ (eqToIso hU ≪≫ e)).hom ≫ d := by
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [reassoc_of% hsq, hE, Category.assoc, hn]

private def reservoirRow {k : Type u} [CommRing k]
    {A B R : PiSCat.{u,u,u+1} k} (E : A ⟶ B) (F : B ⟶ A) (Z : A ⟶ R)
    (σ : ZMod 2) (z : ℤ) (f : E ⟶ E) (g : E ≫ F ⟶ 𝟙 A) :
    (SKM.homPre (k := k) E).obj ((SKM.homParityShift (k := k) (C := B ⟶ R) σ).obj (F ≫ Z)) ⟶ Z :=
  z • (E ◁ ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ Z)).hom ≫
    f ▷ (F ≫ Z) ≫ g ▷ Z)

private theorem reservoirCap_row
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (W : X → PiSCat.{u,u,u+1} k) (i : I) (x : X) {a b : X}
    (edge : -a + D.α i = -b) (n : ℕ) (Z : T.obj (-a) ⟶ W x) :
    SKM.homReservoirCap T W i x edge n Z =
      reservoirRow (R := W x) (T.E i edge) (T.F i edge) Z
        (SKM.leftAdjParity D i (-a))
        (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
        (SKM.rouquierPower (T.dot i edge) n)
        (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) := by
  rw [SKM.homReservoirCap_coordinates]
  unfold reservoirRow
  erw [PiSCat.associator_inv, PiSCat.leftUnitor_hom, Category.comp_id, Category.id_comp]

private theorem reservoirRow_block
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    {A B : PiSCat.{u,u,u+1} k} (E : A ⟶ B) (F : B ⟶ A)
    (Z : A ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : A)
    (σ : ZMod 2) (z : ℤ) (f : E ⟶ E) (g : E ≫ F ⟶ 𝟙 A)
    (hSrc : (((SKM.homPre (k := k) E).obj
        ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ x) σ).obj
          (F ≫ Z))).obj N) δ =
      ((SKM.homPre (k := k) E).obj
        ((SKM.homParityShift (k := k) (C := B ⟶ contentModuleTarget D Sc cutoff bound δ.1) σ).obj
          (F ≫ Z.comp (elvBlockEval D Sc cutoff bound Λ δ)))).obj N) :
    ((reservoirRow (R := elvWeightSpace D Sc cutoff bound Λ x) E F Z σ z f g).total N) δ =
      eqToHom hSrc ≫ (reservoirRow (R := contentModuleTarget D Sc cutoff bound δ.1) E F
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)) σ z f g).total N := by
  fin_cases σ
  all_goals
    have hh : hSrc = rfl := Subsingleton.elim _ _
    rw [hh]
    simp only [eqToHom_refl, Category.id_comp]
    rfl

/-- Selecting an output block of the whole weight space commutes with
every dotted reservoir cap, through the block source chart. -/
theorem reservoirCap_block
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (δ : WeightBlocks D Λ x)
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (i : I) {a b : X} (edge : -a + D.α i = -b)
    (Z : T.obj (-a) ⟶ elvWeightSpace D Sc cutoff bound Λ x) (N : T.obj (-a))
    (hSrc : (((SKM.homContentPreE T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj
        ((SKM.homContentPreF T (elvWeightSpace D Sc cutoff bound Λ) i x edge).obj Z)).obj N) δ =
      ((SKM.homContentPreE T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
        ((SKM.homContentPreF T (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge).obj
          (Z.comp (elvBlockEval D Sc cutoff bound Λ δ)))).obj N)
    (n : ℕ) :
    (SKM.homReservoirCap T (elvWeightSpace D Sc cutoff bound Λ) i x edge n Z).total N δ =
      eqToHom hSrc ≫ (SKM.homReservoirCap T
        (fun _ => contentModuleTarget D Sc cutoff bound δ.1) i x edge n
        (Z.comp (elvBlockEval D Sc cutoff bound Λ δ))).total N := by
  rw [reservoirCap_row, reservoirCap_row]
  exact reservoirRow_block D Sc cutoff bound Λ x δ (T.E i edge) (T.F i edge) Z N
    (SKM.leftAdjParity D i (-a))
    (koszulSign (SKM.leftAdjParity D i (-a)) (1 + (n : ZMod 2) * D.parity i))
    (SKM.rouquierPower (T.dot i edge) n)
    (((((T.leftAdjScalar i (-a))⁻¹ : kˣ) : k)) • T.leftCap i edge) hSrc

end Generic

section Regular

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
  (W : X → PiSCat.{u,u,u+1} k) (muM : X) (i : I) {muP : X}
  (h : -Λ + D.α i = -muP) (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W muM)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc
local notation "N₀" => regularProbe D Sc m Λ
local notation "Z" => preCapInput D Sc m Λ hc W muM H

/-- Every prescribed dotted reservoir cap on the regular probe is the native
`x ^ n ≫ v` through the normalized pre-cap source chart. No parity is used. -/
theorem vacuumPreReservoirCap_eq (hP : 0 < probeCutoff D m i) (n : ℕ) :
    (SKM.homReservoirCap T W i muM h n Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      (ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  rw [SKM.homReservoirCap, Superfunctor.comp_total, Category.assoc,
    vacuumPreCounit_eq D Sc m Λ hc W muM i h H hP, ← Category.assoc,
    total_pow_square _ _ _ _ (vacuumPreDot_source D Sc m Λ hc W muM i h H hP) n,
    Category.assoc]

end Regular

section Pullback

variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : SKM.Datum I X}
  (T W : SKM.RouquierFamily (k := k) (B := B) D)
  {a a' b b' : X} (ha : a = a') (hb : b = b')
  (Z' : SKM.homWeightSector T.obj W.obj a' b')

/-- A pulled-back input returns to itself under the weight equivalence. -/
def capPullbackSelfIso :
    (SKM.homWeightEquivalence T W ha hb).functor.obj
      ((SKM.homWeightEquivalence T W ha hb).inverse.obj Z') ≅ Z' := by
  subst a'
  subst b'
  exact Iso.refl _

/-- The dotted reservoir cap on a pulled-back input is the cap on the
normalized input, through the source pullback chart and the return chart. -/
theorem homReservoirCap_weight_pullback_square (i : I) {c : X}
    (hp : -a + D.α i = -c) (n : ℕ) :
    (SKM.homWeightEquivalence T W ha hb).functor.map
        (SKM.homReservoirCap T W.obj i b hp n
          ((SKM.homWeightEquivalence T W ha hb).inverse.obj Z')) ≫
      (capPullbackSelfIso T W ha hb Z').hom =
    (SKM.homPreWeightPullbackIso T W ha hb i hp Z').hom ≫
      SKM.homReservoirCap T W.obj i b' (show -a' + D.α i = -c from ha ▸ hp) n Z' := by
  subst a'
  subst b'
  change SKM.homReservoirCap T W.obj i b hp n Z' ≫ 𝟙 _ =
    𝟙 _ ≫ SKM.homReservoirCap T W.obj i b hp n Z'
  simp only [Category.comp_id, Category.id_comp]

end Pullback

section Padded

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance paddedCapZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR

omit [Fintype I] in
private theorem capProbeWeight_zero : (P).muP (((0, 0) : Sector I)) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
omit [Fintype I] in
private theorem capReservoirWeight_zero : (P).muM (((0, 0) : Sector I)) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

private def capVacuumEvaluation :
    SKM.homWeightSector (P).T.obj (P).W.obj ΛP (-ΛR) ⥤
      ContentModules D (parameterTwist D Sc) cutoff bound (0 : Multiset I) :=
  homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR (-ΛR)
    ((P).T.obj (-ΛP)) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))

/-- The cap target comparison: return the pulled-back vacuum input to the
normalized input, then apply the regular-input chart of the output block. -/
def paddedVacuumCapTargetIso :=
  (capVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).mapIso
      (capPullbackSelfIso (P).T (P).W
        (capProbeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)
        (capReservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR)
        (preCapInput D (parameterTwist D Sc) m ΛP hcP
          (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H)) ≪≫
    (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).toFunctor.mapIso
      (eqToIso (emptyProbe_regular D (parameterTwist D Sc) m ΛP))

/-- The prescribed padded reservoir cap row `n` at the vacuum sector is the
native `x ^ n ≫ v` of the output block, through the same source chart as the
padded Dx entry. No parity, moment or cap compatibility is assumed. -/
theorem paddedVacuumCap_eq [Fact Sc.PureNilpotent] (i : I) (hP : 0 < probeCutoff D m i) (n : ℕ) :
    (P).centralPaddedCap i (((0, 0) : Sector I))
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true n ≫
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom =
    (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
      (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := by
  classical
  let PR := elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
  let E₀ := capVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z := vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
  let E := vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := capProbeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := capReservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let ep := PR.muP_preE i (0, 0)
  let ep₀ : -ΛP + D.α i = -PR.muP (nextSector (true, i) true (((0, 0) : Sector I))) :=
    (congrArg (fun x : X => -x + D.α i) ha).symm.trans ep
  let B₀ := vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H
  let W₀ : X → PiSCat.{u,u,u+1} k :=
    fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)
  let N₀ := regularProbe D (parameterTwist D Sc) m ΛP
  let s := PR.centralSourceCornerIso i (0, 0) Z E ⟨true, by trivial⟩
  let u := E₀.mapIso (SKM.homPreWeightPullbackIso PR.T PR.W ha hb i ep Z₀)
  let e := vacuumPreSourceIso D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) i ep₀ B₀
  let c := E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map
    (SKM.homReservoirCap PR.T PR.W.obj i (PR.muM (0, 0)) ep n
      ((SKM.homWeightEquivalence PR.T PR.W ha hb).inverse.obj Z₀)))
  let p := E₀.map (capPullbackSelfIso PR.T PR.W ha hb Z₀).hom
  let q := B₀.toFunctor.map (eqToHom (emptyProbe_regular D (parameterTwist D Sc) m ΛP))
  let c₀ := E₀.map (SKM.homReservoirCap PR.T PR.W.obj i (-ΛR) ep₀ n Z₀)
  let c₁ := (SKM.homReservoirCap (probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hcP)
    W₀ i (-ΛR) ep₀ n (preCapInput D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) B₀)).total N₀
  let d := (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i B₀ ^ n) ≫
    ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
      (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP B₀
  have hsq : c ≫ p = u.hom ≫ c₀ := by
    have h := congrArg E₀.map
      (homReservoirCap_weight_pullback_square PR.T PR.W ha hb Z₀ i ep n)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hSrc : (((SKM.homContentPreE PR.T (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR)
        i (-ΛR) ep₀).obj ((SKM.homContentPreF PR.T
          (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) i (-ΛR) ep₀).obj Z₀)).obj
        N₀) (emptyBlock D ΛR) =
      ((SKM.homContentPreE PR.T W₀ i (-ΛR) ep₀).obj ((SKM.homContentPreF PR.T W₀ i (-ΛR) ep₀).obj
            (preCapInput D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) B₀))).obj N₀ := by
    simp only [SKM.homContentPreF, Functor.comp_obj, SKM.homParityShift]
    split_ifs <;> rfl
  have hE0 := reservoirCap_block D (parameterTwist D Sc) cutoff bound ΛR (-ΛR) (emptyBlock D ΛR)
      PR.T i ep₀ Z₀ N₀ hSrc n
  have hc₀ : c₀ = (SKM.homReservoirCap PR.T PR.W.obj
      i (-ΛR) ep₀ n Z₀).total N₀ (emptyBlock D ΛR) := by
    simp only [c₀, E₀, N₀, capVacuumEvaluation, homContentEvaluation, Functor.comp_map,
      Pi.eval_map, homTotalEvaluation]
  have hc₁ : (SKM.homReservoirCap PR.T
        (fun _ => contentModuleTarget D (parameterTwist D Sc) cutoff bound (emptyBlock D ΛR).1)
        i (-ΛR) ep₀ n
        (Z₀.comp (elvBlockEval D (parameterTwist D Sc) cutoff bound ΛR (emptyBlock D ΛR)))).total N₀
      = c₁ := rfl
  have hE : c₀ = eqToHom hSrc ≫ c₁ := by
    rw [hc₀, ← hc₁]
    exact hE0
  have hn : c₁ ≫ q = e.hom ≫ d :=
    vacuumPreReservoirCap_eq D (parameterTwist D Sc) m ΛP hcP W₀ (-ΛR) i ep₀ B₀ hP n
  have hs := cap_charts_attach s u hSrc e c p q c₀ c₁ d hsq hE hn
  have hcap : PR.centralPaddedCap i (((0, 0) : Sector I)) Z E true n = s.hom ≫ c := by
    unfold ProbeReservoir.centralPaddedCap
    rw [dite_eq_left_of_eq_true (eq_true (show StepValid (SKM.up i) true (((0, 0) : Sector I)) from
      by trivial))]
    rfl
  have hsrc : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (s ≪≫ u ≪≫ (eqToIso hSrc ≪≫ e)).hom := rfl
  have htgt : (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom = p ≫ q := rfl
  rw [hcap, htgt, hsrc]
  exact hs
end Padded

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
end

end

section

/-! # The chosen vacuum cap inverse in the native chart

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

At formal content zero and positive height, the actual positive augmented factor
matrix of the supported vacuum sector has a cap-window inverse
(`SupportedSectors.vacuumCapInverseData`). This file transports that inverse,
entry by entry, to the native chart of the regular vacuum probe: its principal map
becomes the evaluated A6 bend `evaluatedMixedBend` (odd colour, through
`paddedVacuumDx_odd`) and its windows become the native rows `x ^ n ≫ v`
(`paddedVacuumCap_eq`). The result `vacuumCapInverse_odd` is a cap
inverse of exactly the window used by `tensorVacuumCapInverse_odd_moments`.

The transport uses only additive evaluation (`IsCapInverse.map`), the corner
charts (`IsCapInverse.coordinates`) and a change of the common window target
(`IsCapInverse.target`). No inverse, moment or bubble value is assumed.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.SwappedAssembly

namespace ProbeWindow

variable {C : Type*} [Category C] [Preadditive C]
  {X Y O O' : C} {n : ℕ} {s : X ⟶ Y} {v : Fin n → (X ⟶ O)}
  {j : Y ⟶ X} {A : Fin n → (O ⟶ X)}

/-- An isomorphism of the common window target transports a cap inverse. -/
theorem IsCapInverse.target (H : IsCapInverse s v j A) (c : O ≅ O') :
    IsCapInverse s (fun r => v r ≫ c.hom) j (fun r => c.inv ≫ A r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨h1, fun r => ?_, fun r => ?_, fun r t => ?_, ?_⟩
  · rw [Category.assoc, h2 r, Limits.comp_zero]
  · rw [← Category.assoc, h3 r, Limits.zero_comp]
  · rw [Category.assoc, reassoc_of% (h4 r t)]
    split_ifs <;> simp
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h5

end ProbeWindow

namespace ProbeReservoir

open OddMath.SKM Classical
open scoped ZeroObject

universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
variable (P : ProbeReservoir k B D Sc)
variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  {C' : Type*} [Category C'] [Preadditive C'] [Limits.HasZeroObject C']

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u

local instance paddedVacuumCapInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance paddedVacuumCapInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
  (hwin : SupportedSectors.ReservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hcP hcR) (i : I)

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
end

end

section

/-! # The leftward vacuum cap inverse in the native chart

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

`vacuumCapInverse_odd` transports a cap inverse of the vacuum window to the
native chart, but only existentially. Here the inverse is the one given by any
leftward data satisfying the positive inverse equations at the vacuum sector
(`isCapInverse_centralPadded_of_posInverseAt`), evaluated directly by the vacuum
sector evaluation. Its columns are explicit: the dotted leftward cups, conjugated
by the source and cap-target charts (`vacuumLeftwardCapInverse_odd`).
Consequently every product of a column with a native cap row `x ^ N ≫ v` is the
conjugated evaluation of the left bubble entry `dcup n ≫ ε xᴺ`
(`vacuumLeftwardColumn_cap_eq`). No inverse, moment or bubble value is assumed.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u

local instance leftwardVacuumCapInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance leftwardVacuumCapInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (i : I)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

/-- The explicit native column `n` of the leftward vacuum cap inverse: the dotted
leftward cup, evaluated by the vacuum sector evaluation and conjugated by the
padded source, corner and cap-target charts. -/
def vacuumLeftwardColumn [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z) (n : ℕ) := by
  subst hZ
  exact (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
        (dc n (.nil _) p₀ ≫ ((P).centralSourceFactorIso i ν₀ ((0, 0) : Sector I)
          (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟨true, trivial⟩).inv) ≫
      ((P).centralSourceCornerIso i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨true, trivial⟩).inv ≫
    (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom

include hdot in
/-- **The leftward vacuum cap inverse in the native chart (odd colour).** Leftward
data satisfying the positive inverse equations at the vacuum sector give an
entrywise inverse of the native cap window `[bend; x ^ n ≫ v]_(n < h)` of the
evaluated A6 bend, whose columns are the explicit `vacuumLeftwardColumn`. -/
theorem vacuumLeftwardCapInverse_odd [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (HP : (P).PosInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ∃ j, ProbeWindow.IsCapInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (D.h i ν₀).toNat => (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ (n : ℕ)) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H)) j
        (fun n => vacuumLeftwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i Z hZ dc n) := by
  subst hZ
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by
    simp [StepValid]
  have h₁ := (P).isCapInverse_centralPadded_of_posInverseAt
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀ ((0, 0) : Sector I)
    (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) lc dc HP hu hd
  have h₃ := (h₁.coordinates (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm).target
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H)
  have hs : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i
        ((0, 0) : Sector I) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) :=
    (Iso.inv_comp_eq _).2 (paddedVacuumDx_odd D Sc m cutoff bound ΛP ΛR hcP hcR H i
      hdot hP hi)
  have hw : ∀ n : ℕ, (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedCap i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true n ≫
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom =
      (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := fun n =>
    (Iso.inv_comp_eq _).2 (paddedVacuumCap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i hP n)
  simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc, hs, hw] at h₃
  exact ⟨_, h₃⟩

/-- **Column moments are bubble entries.** The native column `n` of the leftward
vacuum cap inverse followed by the native cap row `x ^ N ≫ v` is the evaluated left
bubble entry `dcup n ≫ ε xᴺ`, conjugated by the cap-target chart. -/
theorem vacuumLeftwardColumn_cap_eq [Fact Sc.PureNilpotent]
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟶
        ((P).pathFunctor p).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H))
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (n N : ℕ) :
    vacuumLeftwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i _ rfl dc n ≫
        (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ N) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) =
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          (dc n (.nil _) p₀ ≫ (P).epsEntry cc i N ν₀ p₀ (.nil _)
            (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)) ≫
        (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom := by
  simp only [vacuumLeftwardColumn, Category.assoc]
  rw [← paddedVacuumCap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i hP N,
    (P).map_dcup_epsEntry_eq_padded cc i ν₀ ((0, 0) : Sector I)
      (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
      (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (dc n (.nil _) p₀) N]
  simp only [Category.assoc]

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
end

end

section

/-! # Odd moments of the leftward vacuum bubble entries

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

Leftward data satisfying the positive inverse equations at the vacuum sector give
an explicit cap inverse of the native cap window of the evaluated A6 bend
(`vacuumLeftwardCapInverse_odd`), whose column products with the native cap
rows are the conjugated evaluated left bubble entries `dcup n ≫ ε xᴺ`
(`vacuumLeftwardColumn_cap_eq`). At the tensor vacuum this inverse is one to
which `tensorVacuumCapInverse_odd_moments` applies, so the conjugated evaluated
left bubble entries `dcup (h - 1) ≫ ε x^(h - 1 + 2s)` and `dcup (h - 1) ≫ ε x^(h + 2s)`
are the columns with the substituted-series moments
(`tensorVacuum_leftward_odd_moments`). No inverse,
moment or bubble value is assumed.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
universe u

local instance leftwardVacuumMomentsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Pullback

/-- The return isomorphism of a pulled-back input is an `eqToHom`. -/
theorem capPullbackSelfIso_hom {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
    [∀ a b : B, PiSupercategory k (a ⟶ b)]
    {I X : Type*} [AddCommGroup X] {D : SKM.Datum I X}
    (T W : SKM.RouquierFamily (k := k) (B := B) D)
    {a a' b b' : X} (ha : a = a') (hb : b = b')
    (Z' : SKM.homWeightSector T.obj W.obj a' b') :
    (capPullbackSelfIso T W ha hb Z').hom = eqToHom (by subst a' b'; rfl) := by
  subst a' b'
  rfl

end Pullback

section Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (i : I)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

/-- The cap target comparison `paddedVacuumCapTargetIso` is an `eqToHom`. -/
theorem paddedVacuumCapTargetIso_hom_eq_eqToHom :
    ∃ h, (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom = eqToHom h := by
  rw [paddedVacuumCapTargetIso, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
    capPullbackSelfIso_hom, eqToIso.hom, eqToHom_map, eqToHom_map, eqToHom_trans]
  exact ⟨_, rfl⟩

include hdot in
/-- **Leftward vacuum cap inverse with bubble-entry columns.** For leftward data
satisfying the positive inverse equations at an input equal to the vacuum sector
input, the native cap window of the evaluated A6 bend has an entrywise inverse
whose column products with the native cap rows `x ^ N ≫ v` are the evaluated left
bubble entries `dcup n ≫ ε xᴺ`, conjugated by one isomorphism `c`. -/
theorem vacuumLeftwardCapInverse_bubbleEntries [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (HP : (P).PosInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ∃ (c : _ ≅ _) (j : _) (A : Fin (D.h i ν₀).toNat → _),
      (∃ h, c.hom = eqToHom h) ∧ ProbeWindow.IsCapInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (D.h i ν₀).toNat => (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ (n : ℕ)) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H)) j A ∧
      ∀ (n : Fin (D.h i ν₀).toNat) (N : ℕ),
        A n ≫ (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ N) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          (dc n (.nil _) p₀ ≫ (P).epsEntry cc i N ν₀ p₀ (.nil _) Z) ≫ c.hom := by
  subst hZ
  obtain ⟨j, hj⟩ := vacuumLeftwardCapInverse_odd D Sc m cutoff bound ΛP ΛR hcP hcR H
    hdot i _ rfl lc dc HP hP hi
  exact ⟨paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H, j, _,
    paddedVacuumCapTargetIso_hom_eq_eqToHom D Sc m cutoff bound ΛP ΛR hcP hcR H, hj,
    fun n N => vacuumLeftwardColumn_cap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i dc cc hP
      n N⟩

end Generic

section Tensor

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff
  (PowerWordContent.powerBound D cutoff L))
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "Zt" => (SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR).obj
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D
  (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

omit [Fintype I] in
private theorem odd_probeCutoff' (hi : D.parity i = 1) : probeCutoff D m i = 2 * m i := by
  simp [probeCutoff, probeDotExponent, hi]

include hdot in
/-- **Odd moments of the leftward vacuum bubble entries.** For an odd colour with
`0 < N_i < P_i` and `h = P_i - N_i`, leftward data satisfying the positive inverse
equations at the tensor vacuum give an entrywise inverse `(j, A)` of the native cap
window of the tensor vacuum bend such that every column product
`A n ≫ x ^ N ≫ v` is the evaluated left bubble entry `dcup n ≫ ε xᴺ` conjugated by
one isomorphism `c`, and the last column has the substituted-series moments: the
shift `h - 1 + 2s` decodes to multiplication by the `s`-th coefficient of the
substituted probe series and the shift `h + 2s` to that coefficient times the
reservoir odd coefficient. -/
theorem tensorVacuum_leftward_odd_moments [Fact Sc.PureNilpotent] (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (hlt : cutoff i < probeCutoff D m i)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Zt ⟶ ((P).pathFunctor p).obj Zt)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Zt ⟶ ((P).pathFunctor p).obj Zt)
    (HP : (P).PosInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Zt lc dc)
    (cc : (P).CrossCoeff) :
    ∃ (c : _ ≅ V) (j : _) (A : Fin (probeCutoff D m i - cutoff i) →
        (V ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)),
      (∃ h, c.hom = eqToHom h) ∧ ProbeWindow.IsCapInverse
        (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i (hN.trans hlt) H)
        (fun n : Fin (probeCutoff D m i - cutoff i) =>
          (shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^
              (n : ℕ)) ≫
            shiftedPreCap D (parameterTwist D Sc) m
              (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
              (hN.trans hlt) H) j A ∧
      (∀ (n : Fin (probeCutoff D m i - cutoff i)) (N : ℕ),
        A n ≫ (shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^ N) ≫
          shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (hN.trans hlt) H =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          (dc n (.nil _) p₀ ≫ (P).epsEntry cc i N ν₀ p₀ (.nil _) Zt) ≫ c.hom) ∧
      ∀ (s : ℕ) (z : (V).obj star),
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            ((A ⟨probeCutoff D m i - cutoff i - 1, by omega⟩ ≫
              (shiftedPreDot D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^
                (probeCutoff D m i - cutoff i - 1 + 2 * s)) ≫
              shiftedPreCap D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
                (hN.trans hlt) H).total star z) =
          polynomialToPower D cutoff L (PowerSeries.coeff s
              (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z ∧
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            ((A ⟨probeCutoff D m i - cutoff i - 1, by omega⟩ ≫
              (shiftedPreDot D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^
                (probeCutoff D m i - cutoff i + 2 * s)) ≫
              shiftedPreCap D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
                (hN.trans hlt) H).total star z) =
          ((-1 : k) ^ (cutoff i + 1) •
              coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
            (polynomialToPower D cutoff L (PowerSeries.coeff s
              (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
              tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z) := by
  classical
  have hP : 0 < probeCutoff D m i := hN.trans hlt
  have hlen := SupportedSectors.vacuum_positive_window_length D Sc m cutoff bound ΛP ΛR
    hcP hcR i
  have hex := vacuumLeftwardCapInverse_bubbleEntries D Sc m cutoff bound ΛP ΛR hcP hcR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) hdot i Zt
    (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hcP hcR).symm lc dc HP cc hP hi
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = H from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR, hlen] at hex
  obtain ⟨c, j, A, hceq, hA, hcap⟩ := hex
  have hhN : probeCutoff D m i - cutoff i + cutoff i = 2 * m i := by
    rw [← odd_probeCutoff' D m i hi]
    omega
  exact ⟨c, j, A, hceq, hA, hcap, fun s z =>
    tensorVacuumCapInverse_odd_moments D (parameterTwist D Sc) m cutoff L
      hdot i hi hP hN _ (by omega) hhN j A hA s z⟩

end Tensor

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
end

end

section

/-! # The even slide of the evaluated mixed bend

SwappedVacuumNonpositiveBubbles §1 (1), with moving parity zero.
The chosen even finite series telescopes on the actual probe/reservoir
carrier, retaining the prescribed cap and post unit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
section Series
variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}
private theorem inverse_power_cancel (x : End X) (hx : IsUnit x) (r : ℕ) :
    x ≫ Ring.inverse x ^ (r + 1) = Ring.inverse x ^ r := by
  change Ring.inverse x ^ (r + 1) * x = Ring.inverse x ^ r
  rw [pow_succ, mul_assoc, Ring.inverse_mul_cancel _ hx, mul_one]
private def evenSeries (x : End X) (y : End Y) (t : X ⟶ Y) (n : ℕ) : X ⟶ Y :=
  ∑ r ∈ Finset.range n, (-1 : ℤ) • ((Ring.inverse x ^ (r + 1)) ≫ t ≫ y ^ r)
private theorem evenSeries_boundary (x : End X) (hx : IsUnit x)
    (y : End Y) (t : X ⟶ Y) (n : ℕ) :
    evenSeries x y t n ≫ y - x ≫ evenSeries x y t n =
      t - ((Ring.inverse x ^ n) ≫ t ≫ y ^ n) := by
  induction n with
  | zero => simp only [evenSeries, Finset.sum_range_zero, pow_zero, End.one_def,
      Category.id_comp, Category.comp_id, sub_self, Limits.zero_comp, Limits.comp_zero]
  | succ n ih =>
    have hs : evenSeries x y t (n + 1) = evenSeries x y t n -
        ((Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ n) := by
      rw [evenSeries, Finset.sum_range_succ, neg_one_zsmul, sub_eq_add_neg]
      rfl
    have hY : ((Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ n) ≫ y =
        (Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ (n + 1) := by
      simp only [pow_succ' y n, End.mul_def, Category.assoc]
    have hX : x ≫ ((Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ n) =
        (Ring.inverse x ^ n) ≫ t ≫ y ^ n := by
      rw [← Category.assoc, ← Category.assoc, inverse_power_cancel x hx n]
      exact Category.assoc _ _ _
    rw [hs, Preadditive.sub_comp, Preadditive.comp_sub, hY, hX]
    calc
      _ = (evenSeries x y t n ≫ y - x ≫ evenSeries x y t n) +
          ((Ring.inverse x ^ n) ≫ t ≫ y ^ n) -
          ((Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ (n + 1)) := by abel
      _ = _ := by rw [ih]; abel
private theorem evenSeries_slide (x : End X) (hx : IsUnit x)
    (y : End Y) (t : X ⟶ Y) (n : ℕ) (hn : y ^ n = 0) :
    evenSeries x y t n ≫ y - x ≫ evenSeries x y t n = t := by
  rw [evenSeries_boundary x hx y t n, hn, Limits.comp_zero, Limits.comp_zero, sub_zero]
end Series
namespace ProbeVacuumCap
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m

/-- The parity-zero mate slide on the prescribed evaluated bend, with no slide premise. -/
theorem evaluatedMixedBend_even_slideOf
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (i : I) (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      koszulSign (D.parity i) (D.parity i) •
        (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫
        (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀) := by
  obtain ⟨n, _, hd⟩ := diagonalPostDot_pow_zero D Sc m cutoff bound hdot i
  obtain ⟨l, _, hy⟩ := evaluatedPostDot_pow_zero D Sc m cutoff bound hdot i
  have hd' : diagonalPostDot D Sc m cutoff bound i H ^ (n + l) = 0 :=
    pow_eq_zero_of_le (by omega) (hd H)
  have hy' : evaluatedPostDot D Sc m cutoff bound i H ^ (n + l) = 0 :=
    pow_eq_zero_of_le (by omega) (hy H)
  have he := evaluatedMixedBend_even_expansion D Sc m cutoff bound i hi hP H (n + l) hd'
  have hs : evaluatedMixedBend D Sc m cutoff bound i hP H =
      evenSeries (shiftedPreDot D Sc m R₀ i H) (evaluatedPostDot D Sc m cutoff bound i H)
        (shiftedPreCap D Sc m R₀ i hP H ≫
          (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀))
        (n + l) := by
    simpa only [evenSeries, Category.assoc] using he
  rw [hs, hi, koszulSign_zero_left, one_smul]
  exact evenSeries_slide _ (shiftedPreDot_even_isUnit D Sc m R₀ i hi H) _ _ _ hy'

/-- `evaluatedMixedBend_even_slideOf` with the even Koszul sign written as `1`. -/
theorem evaluatedMixedBend_even_slide_one
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (i : I) (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      (1 : k) • (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫
        (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀) := by
  have hs := evaluatedMixedBend_even_slideOf D Sc m cutoff bound hdot i hi hP H
  rw [one_smul]
  simpa only [hi, koszulSign_zero_left, one_smul] using hs

end ProbeVacuumCap
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The padded reservoir unit columns on the regular vacuum probe

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. The unit columns of the negative two-sector matrix at the vacuum sector
are the prescribed padded post-cups `centralPaddedUnit false n`. This file
evaluates them on the regular probe: through the cap-target chart
`paddedVacuumCapTargetIso` (the source of every column) and the target chart
of the padded Dx entry (`paddedVacuumTargetIso`), the `n`-th unit column is
the native unit followed by `n` canonical dots (`paddedVacuumUnit_eq`).
No parity, moment or unit compatibility is assumed.
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u
local instance paddedVacuumUnitHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Pullback

variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : SKM.Datum I X}
  (T W : SKM.RouquierFamily (k := k) (B := B) D)
  {a a' b b' : X} (ha : a = a') (hb : b = b')
  (Z' : SKM.homWeightSector T.obj W.obj a' b')

/-- The dotted post-cup on a pulled-back input is the post-cup on the
normalized input, through the return chart and the target pullback chart. -/
theorem homPostCup_weight_pullback_square (i : I) (β : I →₀ ℕ) {d : X}
    (hr : b + D.α i = d) (n : ℕ) :
    (SKM.homWeightEquivalence T W ha hb).functor.map
        (SKM.homContentPostCup T.obj W i β a hr n
          ((SKM.homWeightEquivalence T W ha hb).inverse.obj Z')) ≫
      (SKM.homPostWeightPullbackIso T W ha hb i hr β Z').hom =
    (capPullbackSelfIso T W ha hb Z').hom ≫
      SKM.homContentPostCup T.obj W i β a' (show b' + D.α i = d from hb ▸ hr) n Z' := by
  subst a'
  subst b'
  change SKM.homContentPostCup T.obj W i β a hr n Z' ≫ 𝟙 _ =
    𝟙 _ ≫ SKM.homContentPostCup T.obj W i β a hr n Z'
  simp only [Category.comp_id, Category.id_comp]

end Pullback

/-- Attach the target and cap-target charts to a pulled-back unit square. -/
private theorem unit_charts_attach {C : Type*} [Category C]
    {S T₀ T₁ T₂ T₃ S' S'' : C} (a : S ⟶ T₁) (t : T₀ ≅ T₁) (v : T₁ ≅ T₂) (f : T₂ ≅ T₃)
    (b : S ⟶ S') (a₀ : S ⟶ T₁) (c : S' ⟶ T₂) (q : S' ⟶ S'') (col : S'' ⟶ T₃)
    (hE : a = a₀) (hsq : a₀ ≫ v.hom = b ≫ c) (hn : c ≫ f.hom = q ≫ col) :
    (a ≫ t.inv) ≫ (t ≪≫ v ≪≫ f).hom = (b ≫ q) ≫ col := by
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hE, reassoc_of% hsq, hn]

section Padded

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR

omit [Fintype I] in
private theorem unitProbeWeight_zero : (P).muP (((0, 0) : Sector I)) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
omit [Fintype I] in
private theorem unitReservoirWeight_zero : (P).muM (((0, 0) : Sector I)) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

private def unitVacuumEvaluation :
    SKM.homWeightSector (P).T.obj (P).W.obj ΛP (-ΛR) ⥤
      ContentModules D (parameterTwist D Sc) cutoff bound (0 : Multiset I) :=
  homContentEvaluation D (parameterTwist D Sc) cutoff bound ΛR (-ΛR)
    ((P).T.obj (-ΛP)) (regularProbe D (parameterTwist D Sc) m ΛP) (emptyBlock D ΛR)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))

/-- **The padded unit column at the vacuum sector.** The prescribed padded
post-cup `n` is the native unit followed by `n` canonical dots, through the
cap-target chart and the target chart of the padded Dx entry. No parity,
moment or unit compatibility is assumed. -/
theorem paddedVacuumUnit_eq (i : I) (n : ℕ) :
    (P).centralPaddedUnit i (((0, 0) : Sector I))
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) false n ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
    (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom ≫
      unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
        (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
          (0 : Multiset I) i)
        ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
          (probeOldVacuumRegular D (parameterTwist D Sc) m)) n := by
  classical
  let PR := elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
  let E₀ := unitVacuumEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z := vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
  let E := vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
  let Z₀ := preCapInput D (parameterTwist D Sc) m ΛP hcP
    (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR) H
  let ha := unitProbeWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let hb := unitReservoirWeight_zero D Sc m cutoff bound ΛP ΛR hcP hcR
  let er := PR.muM_postF i (0, 0)
  let er₀ : -ΛR + D.α i = PR.muM (nextSector (false, i) false (((0, 0) : Sector I))) :=
    (congrArg (fun x : X => x + D.α i) hb).symm.trans er
  let tc := PR.centralTargetCornerIso i (0, 0) Z E ⟨false, by trivial⟩
  let cup := SKM.homContentPostCup PR.T.obj PR.W i 0 (PR.muP (0, 0)) er n Z
  let v := E₀.mapIso (SKM.homPostWeightPullbackIso PR.T PR.W ha hb i er 0 Z₀)
  let f := vacuumPostTarget D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i er₀ 0 H
  let back := E₀.map (capPullbackSelfIso PR.T PR.W ha hb Z₀).hom
  let cup₀ := SKM.homContentPostCup PR.T.obj PR.W i 0 ΛP er₀ n Z₀
  let q := (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).toFunctor.map
    (eqToHom (emptyProbe_regular D (parameterTwist D Sc) m ΛP))
  let col := unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound
      (0 : Multiset I) [i])
    (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound (0 : Multiset I) i)
    ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
      (probeOldVacuumRegular D (parameterTwist D Sc) m)) n
  have hunit : PR.centralPaddedUnit i (((0, 0) : Sector I)) Z E false n =
      E.map cup ≫ tc.inv := by
    unfold ProbeReservoir.centralPaddedUnit
    rw [dite_eq_left_of_eq_true (eq_true (show StepValid (SKM.dn i) false
      (((0, 0) : Sector I)) from by trivial))]
    rfl
  have hE : E.map cup = E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map cup) := by
    simp only [E, vacuumSectorEvaluation, Functor.comp_map]
    rfl
  have hsq : E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map cup) ≫ v.hom =
      back ≫ E₀.map cup₀ := by
    have h := congrArg E₀.map
      (homPostCup_weight_pullback_square PR.T PR.W ha hb Z₀ i 0 er n)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hc₀ : E₀.map cup₀ = cup₀.total (regularProbe D (parameterTwist D Sc) m ΛP)
      (emptyBlock D ΛR) := by
    simp only [cup₀, E₀, unitVacuumEvaluation, homContentEvaluation, Functor.comp_map,
      Pi.eval_map, homTotalEvaluation]
  have hn₁ := vacuumBendPostCup_eq D (parameterTwist D Sc) m cutoff bound ΛP ΛR hcP hcR i
    er₀ 0 H n
  have hn : E₀.map cup₀ ≫ f.hom = q ≫ col := by
    rw [hc₀]
    exact hn₁
  have hs := unit_charts_attach (E.map cup) tc v f back
    (E₀.map ((SKM.homWeightEquivalence PR.T PR.W ha hb).functor.map cup)) (E₀.map cup₀) q col
    hE hsq hn
  rw [hunit]
  exact hs

end Padded

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
end

end

section

/-! # The rightward vacuum cup inverse in the native chart

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

At negative height `h_i(ν₀) < 0` of the vacuum sector, leftward data satisfying the
negative inverse equations (1.14) give an entrywise inverse of the padded cup window
`[σ, w₀, …]` (`isCupInverse_centralPadded_of_negInverseAt`). Evaluated by the vacuum
sector evaluation and read in the native charts of the regular vacuum probe, its
principal map is the evaluated A6 bend (odd colour, `paddedVacuumDx_odd`) and its
windows are the native dotted units `unitDotColumn` (`paddedVacuumUnit_eq`). The
columns of the inverse are explicit: the evaluated dotted rightward caps `dcap n`,
conjugated by the target and cap-target charts (`vacuumRightwardColumn`).
No inverse, moment or bubble value is assumed.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

variable {C : Type*} [Category C] [Preadditive C]
  {X Y O O' : C} {n : ℕ} {s : X ⟶ Y} {u : Fin n → (O ⟶ Y)}
  {j : Y ⟶ X} {B : Fin n → (Y ⟶ O)}

/-- An isomorphism of the common window source transports a cup inverse. -/
theorem IsCupInverse.target (H : IsCupInverse s u j B) (c : O ≅ O') :
    IsCupInverse s (fun r => c.inv ≫ u r) j (fun r => B r ≫ c.hom) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨h1, fun r => ?_, fun r => ?_, fun r t => ?_, ?_⟩
  · rw [← Category.assoc, h2 r, Limits.zero_comp]
  · rw [Category.assoc, h3 r, Limits.comp_zero]
  · rw [Category.assoc, reassoc_of% (h4 r t)]
    split_ifs <;> simp
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h5

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u

local instance rightwardVacuumCupInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance rightwardVacuumCupInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (i : I)
local notation "q₀" => SPath.centralDnUp i (SKM.wt D ν₀ [SKM.up i]) ν₀ ((0, 0) : Sector I)
  ⟨false, trivial⟩

/-- The explicit native column `n` of the rightward vacuum cup inverse: the dotted
rightward cap, evaluated by the vacuum sector evaluation and conjugated by the
padded target, corner and cap-target charts. -/
def vacuumRightwardColumn (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z) (n : ℕ) := by
  subst hZ
  exact ((paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
    ((P).centralTargetCornerIso i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨false, trivial⟩).hom ≫
      (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
        (((P).centralTargetFactorIso i ν₀ ((0, 0) : Sector I)
          (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟨false, trivial⟩).hom ≫
          dc n q₀ (.nil _))) ≫
    (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom

include hdot in
/-- **The rightward vacuum cup inverse in the native chart (odd colour).** Leftward
data satisfying the negative inverse equations at the vacuum sector give an
entrywise inverse of the native cup window `[bend, unit ≫ xⁿ]_(n < -h)` of the
evaluated A6 bend, `h = h_i(ν₀)`, whose columns are the explicit
`vacuumRightwardColumn`. -/
theorem vacuumRightwardCupInverse_odd [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ∃ j, ProbeWindow.IsCupInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (-D.h i ν₀).toNat =>
          unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
              (probeOldVacuumRegular D (parameterTwist D Sc) m)) n) j
        (fun n => vacuumRightwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i Z hZ dc n) := by
  subst hZ
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by
    simp [StepValid]
  have h₁ := (P).isCupInverse_centralPadded_of_negInverseAt
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀ ((0, 0) : Sector I)
    (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) lc dc HN hu hd
  have h₃ := (h₁.coordinates (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm).target
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H)
  have hs : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i
        ((0, 0) : Sector I) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) :=
    (Iso.inv_comp_eq _).2 (paddedVacuumDx_odd D Sc m cutoff bound ΛP ΛR hcP hcR H i
      hdot hP hi)
  have hw : ∀ n : ℕ, (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
      (P).centralPaddedUnit i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) false n ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
        (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
          (0 : Multiset I) i)
        ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
          (probeOldVacuumRegular D (parameterTwist D Sc) m)) n := fun n =>
    (Iso.inv_comp_eq _).2 (paddedVacuumUnit_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i n)
  simp only [Iso.symm_hom, Iso.symm_inv] at h₃
  rw [hs] at h₃
  simp only [hw] at h₃
  exact ⟨_, h₃⟩

/-- The explicit native column, at the vacuum sector input itself. -/
theorem vacuumRightwardColumn_eq
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟶
        ((P).pathFunctor r).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H))
    (n : ℕ) :
    vacuumRightwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i _ rfl dc n =
      ((paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
        ((P).centralTargetCornerIso i ((0, 0) : Sector I)
            (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
            (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨false, trivial⟩).hom ≫
          (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
            (((P).centralTargetFactorIso i ν₀ ((0, 0) : Sector I)
              (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟨false, trivial⟩).hom ≫
              dc n q₀ (.nil _))) ≫
        (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom :=
  rfl

/-- **Native unit rows against the rightward columns.** The native dotted unit
`unit ≫ xᴺ` followed by the column `n` is the evaluated right bubble entry
`η xᴺ ≫ dcap n`, conjugated by the cap-target chart. -/
theorem vacuumRightwardColumn_unit (cc : (P).CrossCoeff)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟶
        ((P).pathFunctor r).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H))
    (n N : ℕ) :
    unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
        (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
          (0 : Multiset I) i)
        ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
          (probeOldVacuumRegular D (parameterTwist D Sc) m)) N ≫
      vacuumRightwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i _ rfl dc n =
    (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
      (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
        ((P).etaEntry cc i N ν₀ (.nil _) q₀
            (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ≫
          dc n q₀ (.nil _)) ≫
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom := by
  rw [vacuumRightwardColumn_eq, ← (Iso.inv_comp_eq _).2
    (paddedVacuumUnit_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i N),
    (P).map_etaEntry_dcap_eq_padded cc i ν₀ ((0, 0) : Sector I)
      (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
      (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (dc n q₀ (.nil _)) N]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

include hdot in
/-- **Rightward vacuum cup inverse with bubble-entry columns.** For leftward data
satisfying the negative inverse equations at an input equal to the vacuum sector
input, the native cup window of the evaluated A6 bend has an entrywise inverse
whose products with the native unit rows `unit ≫ xᴺ` are the evaluated right bubble
entries `η xᴺ ≫ dcap n`, conjugated by one isomorphism `c`, which is an `eqToHom`. -/
theorem vacuumRightwardCupInverse_bubbleEntries [Fact Sc.PureNilpotent] (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ∃ (c : _ ≅ _) (j : _) (B : Fin (-D.h i ν₀).toNat → _),
      ProbeWindow.IsCupInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (-D.h i ν₀).toNat =>
          unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
              (probeOldVacuumRegular D (parameterTwist D Sc) m)) n) j B ∧
      (∃ h, c.hom = eqToHom h) ∧
      ∀ (n : Fin (-D.h i ν₀).toNat) (N : ℕ),
        unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
              (probeOldVacuumRegular D (parameterTwist D Sc) m)) N ≫ B n =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          ((P).etaEntry cc i N ν₀ (.nil _) q₀ Z ≫ dc n q₀ (.nil _)) ≫ c.hom := by
  subst hZ
  obtain ⟨j, hj⟩ := vacuumRightwardCupInverse_odd D Sc m cutoff bound ΛP ΛR hcP hcR H
    hdot i _ rfl lc dc HN hP hi
  exact ⟨paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H, j, _, hj,
    paddedVacuumCapTargetIso_hom_eq_eqToHom D Sc m cutoff bound ΛP ΛR hcP hcR H,
    fun n N => vacuumRightwardColumn_unit D Sc m cutoff bound ΛP ΛR hcP hcR H i cc dc n N⟩

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
end

end
