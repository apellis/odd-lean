import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendDotCoordinates
import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowMonomials

/-! # Separated dotted-window series for the mixed bends

`SwappedHomInversion.md` §3 (4)–(6): evaluate the prescribed coefficient
charts and separate their finite series into negative probe windows and
nonnegative reservoir windows. The nilpotence bound is only required
after the specified output evaluation.
-/
noncomputable section
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
  change bendInsertion _ _ _ = _
  rw [bend_evaluated_monomial]
  have hp : autInverseEnd xR ^ (r+1) =
      (ER).map (homPreDotInverse P.T P.W.obj i (P.muM t) (P.muP_preE i t)
        ((FP).obj Z) ^ (r+1)) :=
    (map_pow (Functor.mapEnd _ (ER)) (autInverseEnd x) (r+1)).symm
  rw [hp, homProbeToReservoir_monomial, L.map_comp]

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
end OddMath.QuiverHecke.SwappedAssembly
