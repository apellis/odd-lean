import OddMath.QuiverHecke.SwappedAssembly.Sigma.SeparatedBendSeries

/-! # The two separated mixed-window equations

These predicates name the literal `hDx` and `hCx` equations in
`CentralInverse/ResidualComparison.lean`, with the prescribed bend,
probe automorphism and normalized dotted windows as their entries.
The finite-series theorems supply them at both parities. Output
evaluation remains an arbitrary additive functor.
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
local notation "x" => homPreDotAut P.T P.W i (P.muP_preE i t) ((FP).obj Z)
local notation "s" => nextSector (false, i) false t
local notation "h" => (by simp [StepValid, nextSector] : StepValid (true, i) false s)
local notation "U" =>
  ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ (FP).obj Z)
local notation "φ" => probeToReservoirBendCoefficientEvaluation P i t Z L

/-- The XP-to-YR equation, with the exact `-q^(r+1)` convention and
negative powers of the raw probe-dot automorphism. -/
def ProbeToReservoirSeparatedAt (c : P.CrossCoeff) (N : ℕ) : Prop :=
  L.map (P.probeToReservoirBend c i t Z) =
    -∑ r ∈ Finset.range N, (koszulSign (D.parity i) (D.parity i))^(r+1) •
      ((Functor.mapAut _ L x ^ (-(r : ℤ)-1)).hom ≫
        L.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
          (P.muM t) (P.muP_preE i t)).counit.app Z) ≫
        L.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z))

/-- The even coefficient supplies the separated XP-to-YR equation. -/
theorem probeToReservoirBend_even_separated (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 0) (n : ℕ) (hn : φ (P.rpPostDot i s h U)^n = 0) :
    ProbeToReservoirSeparatedAt P i t Z L c n := by
  have hq : koszulSign (D.parity i) (D.parity i) = 1 := by rw [hi, koszulSign_zero_left]
  simpa only [ProbeToReservoirSeparatedAt, hq, one_pow, one_smul] using
    probeToReservoirBend_even_windows P i t Z L c hc hi n hn

/-- The signed odd coefficient supplies the same separated equation,
with twice the reservoir nilpotence exponent. -/
theorem probeToReservoirBend_odd_separated (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 1) (n : ℕ) (hn : φ (P.rpPostDot i s h U)^n = 0) :
    ProbeToReservoirSeparatedAt P i t Z L c (2*n) := by
  have hq : koszulSign (D.parity i) (D.parity i) = -1 := by rw [hi, koszulSign_one_one]
  simpa only [ProbeToReservoirSeparatedAt, hq] using
    probeToReservoirBend_odd_windows P i t Z L c hc hi n hn

end ProbeToReservoir

section ReservoirToProbe
variable (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
  (hv : StepValid (true, i) false t) (Z : P.H t)
  {C : Type*} [Category C] [Preadditive C] (L : P.H t ⥤ C) [L.Additive]
  [IsIso (P.T.dot i (P.muP_preF i hb))]
local notation "FP" => homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)
local notation "FR" => homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)
local notation "y" => Functor.mapAut _ (FP) (homPreDotAut P.T P.W i (P.muP_preF i hb) Z)
local notation "s" => nextSector (false, i) true t
local notation "U" =>
  ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ (FR).obj Z)
local notation "φ" => reservoirToProbeBendCoefficientEvaluation P i t hb hv Z L

/-- The XR-to-YP equation, with the exact `q^(r+2)` convention. Its
coefficient includes both the PR bend minus and the mixed-chart sign. -/
def ReservoirToProbeSeparatedAt (c : P.CrossCoeff) (N : ℕ) : Prop :=
  L.map (P.reservoirToProbeBend c i t hb hv Z) =
    ∑ r ∈ Finset.range N, (koszulSign (D.parity i) (D.parity i))^(r+2) •
      (L.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) r Z) ≫
        L.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
          (P.muM t) (P.muP_preF i hb)).unit.app Z) ≫
        (Functor.mapAut _ L y ^ (-(r : ℤ)-1)).hom)

/-- The even coefficient supplies the separated XR-to-YP equation. -/
theorem reservoirToProbeBend_even_separated (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 0) (n : ℕ) (hn : φ (P.rpPostDot i s hv U)^n = 0) :
    ReservoirToProbeSeparatedAt P i t hb hv Z L c n := by
  have hq : koszulSign (D.parity i) (D.parity i) = 1 := by rw [hi, koszulSign_zero_left]
  simpa only [ReservoirToProbeSeparatedAt, hq, one_pow, one_smul] using
    reservoirToProbeBend_even_windows P i t hb hv Z L c hc hi n hn

/-- The odd coefficient supplies the separated XR-to-YP equation. -/
theorem reservoirToProbeBend_odd_separated (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 1) (n : ℕ) (hn : φ (P.rpPostDot i s hv U)^n = 0) :
    ReservoirToProbeSeparatedAt P i t hb hv Z L c (2*n) := by
  have hq : koszulSign (D.parity i) (D.parity i) = -1 := by rw [hi, koszulSign_one_one]
  simpa only [ReservoirToProbeSeparatedAt, hq] using
    reservoirToProbeBend_odd_windows P i t hb hv Z L c hc hi n hn

end ReservoirToProbe
end OddMath.QuiverHecke.SwappedAssembly
