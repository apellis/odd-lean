import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendDotCoordinates
import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowMonomials

/-! # Separated dotted-window series for the mixed bends

`SwappedHomInversion.md` §3 (4)–(6): evaluate the prescribed coefficient
charts and separate their finite series into negative probe windows and
nonnegative reservoir windows. The nilpotence bound is only required
after the specified output evaluation.
-/
noncomputable section
set_option quotPrecheck false
open scoped BigOperators
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
  (P : ProbeReservoir k B D Sc)

section ProbeToReservoir
variable (i : I) (t : Sector I) (Z : P.H t)
  {C : Type*} [Category C] [Preadditive C] (L : P.H t ⥤ C) [L.Additive]
  [IsIso (P.T.dot i (P.muP_preE i t))]
local notation "FP" => homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)
local notation "EP" => homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)
local notation "ER" => homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)
local notation "FR" => homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)
local notation "s" => nextSector (false, i) false t
local notation "h" => (by simp [StepValid, nextSector] : StepValid (true, i) false s)
local notation "U" =>
  ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ (FP).obj Z)
local notation "φ" => probeToReservoirBendCoefficientEvaluation P i t Z L
local notation "β" => probeToReservoirBendInsertion P i t Z L
local notation "x" => homPreDotAut P.T P.W i (P.muP_preE i t) ((FP).obj Z)
local notation "xR" => Functor.mapAut _ (ER) x
local notation "y" => homContentPostDot P.T.obj P.W i t.1 (P.muP t)
  (P.muM_postF i t) ((EP).obj ((FP).obj Z))

/-- Evaluation of the inner probe dot uses the transported raw probe
automorphism, before inverting it in the coefficient series. -/
theorem probeToReservoirBend_preDot_coordinate :
    φ (P.rpPreDot i s h U) = bendFunctorEnd ((FR) ⋙ L) _ (Aut.toEnd _ xR) := by
  change L.map ((FR).map ((P.probeToReservoirCoefficientIso i t ((FP).obj Z)).inv ≫
    P.rpPreDot i s h U ≫ (P.probeToReservoirCoefficientIso i t ((FP).obj Z)).hom)) = _
  rw [P.probeToReservoirCoefficientIso_preDot]
  rfl

omit [IsIso (P.T.dot i (P.muP_preE i t))] in
/-- The evaluated reservoir dot has the literal shifted post-dot coordinate. -/
theorem probeToReservoirBend_postDot_coordinate :
    φ (P.rpPostDot i s h U) = bendFunctorEnd ((FR) ⋙ L) _ y := by
  change L.map ((FR).map ((P.probeToReservoirCoefficientIso i t ((FP).obj Z)).inv ≫
    P.rpPostDot i s h U ≫ (P.probeToReservoirCoefficientIso i t ((FP).obj Z)).hom)) = _
  rw [P.probeToReservoirCoefficientIso_postDot]
  rfl

/-- The actual evaluated probe dot is a unit. Only the reservoir dot
will need a componentwise finite bound. -/
theorem probeToReservoirBend_preDot_isUnit : IsUnit (φ (P.rpPreDot i s h U)) := by
  rw [probeToReservoirBend_preDot_coordinate]
  exact (show IsUnit (Aut.toEnd _ xR) from
    ⟨(Aut.unitsEndEquivAut _).symm xR, rfl⟩).map (bendFunctorEnd ((FR) ⋙ L) _).toMonoidHom

/-- The coefficient's ordered monomial is the separated dotted cap/cup
on every input Hom object and at every additive output evaluation. -/
theorem probeToReservoirBend_monomial (r : ℕ) :
    β (Ring.inverse (φ (P.rpPreDot i s h U)) ^ (r+1) * φ (P.rpPostDot i s h U)^r) =
      L.map (homPreNegativeCap P.T P.W.obj i (P.muM t) (P.muP_preE i t) (r+1) Z) ≫
      L.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z) := by
  rw [probeToReservoirBend_preDot_coordinate, probeToReservoirBend_postDot_coordinate]
  refine (bend_evaluated_monomial (FR) L
    ((homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t)
      (P.muM_postF i t)).unit.app ((EP).obj ((FP).obj Z)))
    ((FR).map ((ER).map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
      (P.muM t) (P.muP_preE i t)).counit.app Z))) xR y (r+1) r).trans ?_
  have hp : autInverseEnd xR ^ (r+1) =
      (ER).map (homPreDotInverse P.T P.W.obj i (P.muM t) (P.muP_preE i t)
        ((FP).obj Z) ^ (r+1)) :=
    (map_pow (Functor.mapEnd _ (ER)) (autInverseEnd x) (r+1)).symm
  rw [hp]
  simpa only [Functor.map_comp] using congrArg L.map
    (homProbeToReservoir_monomial P.T P.W i t.1 (P.muP_preE i t) (P.muM_postF i t) r Z)

omit [Preadditive C] [L.Additive] in
/-- The evaluated negative probe cap is the precise Aut-power cap in
the residual comparison. -/
theorem probeToReservoirBend_negativeCap (r : ℕ) :
    L.map (homPreNegativeCap P.T P.W.obj i (P.muM t) (P.muP_preE i t) (r+1) Z) =
      (Functor.mapAut _ L x ^ (-(r : ℤ)-1)).hom ≫
        L.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
          (P.muM t) (P.muP_preE i t)).counit.app Z) := by
  rw [homPreNegativeCap_aut, L.map_comp, bend_map_aut_zpow]

/-- The separated even XP-to-YR series, with the literal leading minus. -/
theorem probeToReservoirBend_even_windows (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 0) (n : ℕ) (hn : φ (P.rpPostDot i s h U)^n = 0) :
    L.map (P.probeToReservoirBend c i t Z) =
      -∑ r ∈ Finset.range n,
        (Functor.mapAut _ L x ^ (-(r : ℤ)-1)).hom ≫
          L.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
            (P.muM t) (P.muP_preE i t)).counit.app Z) ≫
          L.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z) := by
  rw [probeToReservoirBend_even_expansion P i t Z L c hc hi
    (probeToReservoirBend_preDot_isUnit P i t Z L) n hn]
  simp only [probeToReservoirBend_monomial, probeToReservoirBend_negativeCap, Category.assoc]

/-- The separated odd XP-to-YR series has exactly the `-q^(r+1)`
convention of `CentralInverse/ResidualComparison.lean`. -/
theorem probeToReservoirBend_odd_windows (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 1) (n : ℕ) (hn : φ (P.rpPostDot i s h U)^n = 0) :
    L.map (P.probeToReservoirBend c i t Z) =
      -∑ r ∈ Finset.range (2*n), ((-1 : ℤ)^(r+1)) •
        ((Functor.mapAut _ L x ^ (-(r : ℤ)-1)).hom ≫
          L.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
            (P.muM t) (P.muP_preE i t)).counit.app Z) ≫
          L.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z)) := by
  rw [probeToReservoirBend_odd_expansion P i t Z L c hc hi
    (probeToReservoirBend_preDot_isUnit P i t Z L) n hn]
  simp only [mul_assoc]
  rw [bend_odd_probe_series]
  simp only [probeToReservoirBend_monomial, probeToReservoirBend_negativeCap, Category.assoc]

end ProbeToReservoir

section ReservoirToProbe
variable (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
  (hv : StepValid (true, i) false t) (Z : P.H t)
  {C : Type*} [Category C] [Preadditive C] (L : P.H t ⥤ C) [L.Additive]
  [IsIso (P.T.dot i (P.muP_preF i hb))]
local notation "EP" => homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)
local notation "FP" => homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)
local notation "ER" => homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)
local notation "FR" => homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)
local notation "s" => nextSector (false, i) true t
local notation "U" =>
  ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ (FR).obj Z)
local notation "φ" => reservoirToProbeBendCoefficientEvaluation P i t hb hv Z L
local notation "β" => reservoirToProbeBendInsertion P i t hb hv Z L
local notation "q" => koszulSign (D.parity i) (D.parity i)
local notation "x" => homPreDotAut P.T P.W i (P.muP_preF i hb) ((ER).obj ((FR).obj Z))
local notation "y" => (Functor.mapEnd _ (EP)) (homContentPostDot P.T.obj P.W i t.1 (P.muP t)
  (P.muM_postE i hv) ((FR).obj Z))
local notation "ξ" => bendFunctorEnd ((FP) ⋙ L) _
local notation "yP" => Functor.mapAut _ (FP) (homPreDotAut P.T P.W i (P.muP_preF i hb) Z)

/-- Both lowering and output evaluation retain the PR chart's sign. -/
theorem reservoirToProbeBend_preDot_coordinate :
    φ (P.rpPreDot i s hv U) = q • ξ (Aut.toEnd _ x) := by
  change L.map ((FP).map ((P.reservoirToProbeCoefficientChart i t hb hv ((FR).obj Z)).inv ≫
    P.rpPreDot i s hv U ≫ (P.reservoirToProbeCoefficientChart i t hb hv ((FR).obj Z)).hom)) = _
  rw [P.reservoirToProbeCoefficientChart_preDot]
  exact map_zsmul (ξ) q (Aut.toEnd _ x)

omit [IsIso (P.T.dot i (P.muP_preF i hb))] in
/-- The reservoir dot retains the same PR chart sign. -/
theorem reservoirToProbeBend_postDot_coordinate :
    φ (P.rpPostDot i s hv U) = q • ξ y := by
  change L.map ((FP).map ((P.reservoirToProbeCoefficientChart i t hb hv ((FR).obj Z)).inv ≫
    P.rpPostDot i s hv U ≫ (P.reservoirToProbeCoefficientChart i t hb hv ((FR).obj Z)).hom)) = _
  rw [P.reservoirToProbeCoefficientChart_postDot]
  simp only [Functor.map_zsmul]
  rfl

private theorem reservoirToProbeBend_unsigned_preDot_isUnit : IsUnit (ξ (Aut.toEnd _ x)) :=
  (show IsUnit (Aut.toEnd _ x) from
    ⟨(Aut.unitsEndEquivAut _).symm x, rfl⟩).map (ξ).toMonoidHom

/-- The signed evaluated probe dot is a unit at both parities. -/
theorem reservoirToProbeBend_preDot_isUnit : IsUnit (φ (P.rpPreDot i s hv U)) := by
  rw [reservoirToProbeBend_preDot_coordinate]
  have hx := reservoirToProbeBend_unsigned_preDot_isUnit P i t hb hv Z L
  have hq : q = 1 ∨ q = -1 := by unfold koszulSign; split <;> simp
  rcases hq with hq | hq
  · simpa only [hq, one_smul] using hx
  · simpa only [hq, neg_one_smul] using hx.neg

private theorem reservoirToProbeBend_unsigned_monomial (r : ℕ) :
    β (Ring.inverse (ξ (Aut.toEnd _ x)) ^ (r+1) * ξ y ^ r) =
      L.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) r Z) ≫
      L.map (homPreNegativeCup P.T P.W.obj i (P.muM t) (P.muP_preF i hb) (r+1) Z) := by
  refine (bend_evaluated_monomial (FP) L
    ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t)
      (P.muP_preF i hb)).unit.app ((ER).obj ((FR).obj Z)))
    ((FP).map ((EP).map ((homContentPostAdjunction P.T.obj P.W i t.1
      (P.muP t) (P.muM_postE i hv)).counit.app Z))) x y (r+1) r).trans ?_
  have hp : y^r =
      (EP).map (homContentPostDot P.T.obj P.W i t.1 (P.muP t)
        (P.muM_postE i hv) ((FR).obj Z) ^ r) :=
    (map_pow (Functor.mapEnd _ (EP))
      (homContentPostDot P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) ((FR).obj Z)) r).symm
  rw [hp]
  have hx : autInverseEnd x = homPreDotInverse P.T P.W.obj i (P.muM t)
      (P.muP_preF i hb) ((ER).obj ((FR).obj Z)) := rfl
  rw [hx]
  simpa only [Functor.map_comp] using congrArg L.map
    (homReservoirToProbe_monomial P.T P.W i t.1 (P.muP_preF i hb)
      (P.muM_postE i hv) r Z)

/-- The PR chart contributes exactly one `q`, since its two dot
exponents are consecutive. The bend's own minus is still separate. -/
theorem reservoirToProbeBend_monomial (r : ℕ) :
    β (Ring.inverse (φ (P.rpPreDot i s hv U)) ^ (r+1) * φ (P.rpPostDot i s hv U)^r) =
      q • (L.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) r Z) ≫
        L.map (homPreNegativeCup P.T P.W.obj i (P.muM t) (P.muP_preF i hb) (r+1) Z)) := by
  rw [reservoirToProbeBend_preDot_coordinate, reservoirToProbeBend_postDot_coordinate]
  have hq : q = 1 ∨ q = -1 := by unfold koszulSign; split <;> simp
  rcases hq with hq | hq
  · simpa only [hq, one_smul] using
      reservoirToProbeBend_unsigned_monomial P i t hb hv Z L r
  · simp only [hq, neg_one_smul]
    rw [bend_inverse_neg_monomial
      (reservoirToProbeBend_unsigned_preDot_isUnit P i t hb hv Z L), map_neg,
      reservoirToProbeBend_unsigned_monomial]

omit [Preadditive C] [L.Additive] in
/-- The evaluated negative probe cup uses the precise Aut-power
specified in the residual comparison. -/
theorem reservoirToProbeBend_negativeCup (r : ℕ) :
    L.map (homPreNegativeCup P.T P.W.obj i (P.muM t) (P.muP_preF i hb) (r+1) Z) =
      L.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
        (P.muM t) (P.muP_preF i hb)).unit.app Z) ≫
      (Functor.mapAut _ L yP ^ (-(r : ℤ)-1)).hom := by
  rw [homPreNegativeCup_aut, L.map_comp, bend_map_aut_zpow]
  simp only [Functor.comp_obj]

/-- The separated even XR-to-YP series includes cancellation of the
coefficient minus and the prescribed PR bend minus. -/
theorem reservoirToProbeBend_even_windows (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 0) (n : ℕ) (hn : φ (P.rpPostDot i s hv U)^n = 0) :
    L.map (P.reservoirToProbeBend c i t hb hv Z) =
      ∑ r ∈ Finset.range n,
        L.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) r Z) ≫
        L.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
          (P.muM t) (P.muP_preF i hb)).unit.app Z) ≫
        (Functor.mapAut _ L yP ^ (-(r : ℤ)-1)).hom := by
  rw [reservoirToProbeBend_even_expansion P i t hb hv Z L c hc hi
    (reservoirToProbeBend_preDot_isUnit P i t hb hv Z L) n hn]
  simp only [reservoirToProbeBend_monomial, hi, koszulSign_zero_left, one_smul]
  apply Finset.sum_congr rfl
  intro r _
  exact congrArg (fun f =>
    L.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) r Z) ≫ f)
    (reservoirToProbeBend_negativeCup P i t hb Z L r)

/-- The separated odd XR-to-YP series has the literal `q^(r+2)`
convention, retaining both the chart sign and the PR bend minus. -/
theorem reservoirToProbeBend_odd_windows (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 1) (n : ℕ) (hn : φ (P.rpPostDot i s hv U)^n = 0) :
    L.map (P.reservoirToProbeBend c i t hb hv Z) =
      ∑ r ∈ Finset.range (2*n), ((-1 : ℤ)^(r+2)) •
        (L.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) r Z) ≫
        L.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
          (P.muM t) (P.muP_preF i hb)).unit.app Z) ≫
        (Functor.mapAut _ L yP ^ (-(r : ℤ)-1)).hom) := by
  rw [reservoirToProbeBend_odd_expansion P i t hb hv Z L c hc hi
    (reservoirToProbeBend_preDot_isUnit P i t hb hv Z L) n hn]
  simp only [mul_assoc, bendInsertion_alternating]
  simp only [reservoirToProbeBend_monomial,
    hi, koszulSign_one_one, neg_one_smul, smul_neg, Finset.sum_neg_distrib,
    neg_neg]
  simp only [pow_add, neg_one_sq, mul_one]
  apply Finset.sum_congr rfl
  intro r _
  exact congrArg (fun f => ((-1 : ℤ)^r) •
    (L.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) r Z) ≫ f))
    (reservoirToProbeBend_negativeCup P i t hb Z L r)

end ReservoirToProbe
end OddMath.QuiverHecke.SwappedAssembly
