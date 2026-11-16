import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeToReservoirBend
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirToProbeBend
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExpansion

/-! # Finite coefficient expansions inside the prescribed mixed bends

`SwappedHomInversion.md` §3 (3)–(6): insert the ordered coefficient
series into the actual unit–coefficient–counit bends. The PR coefficient
is the negative conjugate of the RP coefficient. The output functor and
the coefficient bound are explicit intermediate inputs; the ELV
component construction supplies them content by content.
-/
noncomputable section
set_option quotPrecheck false
open scoped BigOperators
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams SKM BicategoryStruct Supercategory
universe u uB v w

section Category
variable {C : Type*} [Category C] [Preadditive C]

/-- Conjugation in the endomorphism ring, in chronological composition order. -/
def bendConjugation {U V : C} (e : U ≅ V) : End U →+* End V where
  toFun f := e.inv ≫ f ≫ e.hom
  map_zero' := by
    change e.inv ≫ (0 : U ⟶ U) ≫ e.hom = 0
    simp only [Limits.comp_zero, Limits.zero_comp]
  map_one' := by simp
  map_add' f g := by
    change e.inv ≫ (f + g) ≫ e.hom = (e.inv ≫ f ≫ e.hom) + (e.inv ≫ g ≫ e.hom)
    rw [Preadditive.add_comp, Preadditive.comp_add]
  map_mul' f g := by simp only [End.mul_def, Category.assoc, Iso.hom_inv_id_assoc]

/-- Inserting an evaluated coefficient between the prescribed unit and cap
is additive. This operation does not alter the coefficient order. -/
def bendInsertion {X U Y : C} (a : X ⟶ U) (b : U ⟶ Y) :
    End U →+ (X ⟶ Y) where
  toFun f := a ≫ f ≫ b
  map_zero' := by
    change a ≫ (0 : U ⟶ U) ≫ b = 0
    simp only [Limits.comp_zero, Limits.zero_comp]
  map_add' f g := by
    change a ≫ (f + g) ≫ b = (a ≫ f ≫ b) + (a ≫ g ≫ b)
    rw [Preadditive.add_comp, Preadditive.comp_add]

/-- The endomorphism ring map of an additive functor. -/
def bendFunctorEnd {E : Type*} [Category E] [Preadditive E]
    (F : C ⥤ E) [F.Additive] (U : C) : End U →+* End (F.obj U) where
  toFun := F.map
  map_zero' := F.map_zero U U
  map_one' := F.map_id U
  map_add' _ _ := F.map_add
  map_mul' f g := F.map_comp g f

end Category

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
  (P : ProbeReservoir k B D Sc)

section ProbeToReservoir
variable (i : I) (t : Sector I) (Z : P.H t)
local notation "F" => homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)
local notation "E" => homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)
local notation "ER" => homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)
local notation "FR" => homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)
local notation "γ" => P.probeToReservoirCoefficientIso i t ((F).obj Z)
local notation "s" => nextSector (false, i) false t
local notation "h" => (by simp [StepValid, nextSector] : StepValid (true, i) false s)
local notation "U" =>
  ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ (F).obj Z)
variable {C : Type*} [Category C] [Preadditive C] (L : P.H t ⥤ C) [L.Additive]

/-- The ring evaluation of the literal RP coefficient in the XP-to-YR bend. -/
def probeToReservoirBendCoefficientEvaluation :
    End (P.rpObj i i s h U) →+* End (L.obj ((FR).obj ((ER).obj ((E).obj ((F).obj Z))))) :=
  ((bendFunctorEnd L _).comp (bendFunctorEnd (FR) _)).comp (bendConjugation γ)

/-- The prescribed unit and cap surrounding the XP-to-YR coefficient,
after output evaluation. -/
def probeToReservoirBendInsertion :
    End (L.obj ((FR).obj ((ER).obj ((E).obj ((F).obj Z))))) →+
      (L.obj ((E).obj ((F).obj Z)) ⟶ L.obj ((FR).obj ((ER).obj Z))) :=
  bendInsertion
    (L.map ((homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t)
      (P.muM_postF i t)).unit.app _))
    (L.map ((FR).map ((ER).map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
      (P.muM t) (P.muP_preE i t)).counit.app Z))))

/-- This insertion is the actual bend, with both chosen adjunctions and
its fixed coefficient chart. -/
theorem map_probeToReservoirBend (c : P.CrossCoeff) :
    L.map (P.probeToReservoirBend c i t Z) =
      probeToReservoirBendInsertion P i t Z L
        (probeToReservoirBendCoefficientEvaluation P i t Z L (c.a i s h U)) := by
  dsimp only [ProbeReservoir.probeToReservoirBend,
    ProbeReservoir.probeToReservoirCoefficient, probeToReservoirBendInsertion,
    probeToReservoirBendCoefficientEvaluation, bendInsertion, bendConjugation, bendFunctorEnd,
    RingHom.comp_apply]
  dsimp
  simp only [Functor.map_comp]

local notation "φ" => probeToReservoirBendCoefficientEvaluation P i t Z L
local notation "β" => probeToReservoirBendInsertion P i t Z L

/-- Intermediate even expansion at a specified output evaluation. Only
the evaluated reservoir dot needs a finite bound. -/
theorem probeToReservoirBend_even_expansion (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 0) (hx : IsUnit (φ (P.rpPreDot i s h U)))
    (n : ℕ) (hn : φ (P.rpPostDot i s h U) ^ n = 0) :
    L.map (P.probeToReservoirBend c i t Z) =
      -∑ r ∈ Finset.range n,
        β (Ring.inverse (φ (P.rpPreDot i s h U)) ^ (r+1) *
          φ (P.rpPostDot i s h U) ^ r) := by
  rw [map_probeToReservoirBend,
    P.crossCoeff_even_evaluate c i s h U φ hc hi hx n hn, map_neg, map_sum]

/-- Intermediate odd expansion in its prescribed signed order. -/
theorem probeToReservoirBend_odd_expansion (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 1) (hx : IsUnit (φ (P.rpPreDot i s h U)))
    (n : ℕ) (hn : φ (P.rpPostDot i s h U) ^ n = 0) :
    L.map (P.probeToReservoirBend c i t Z) =
      ∑ r ∈ Finset.range (2*n),
        β ((-1 : End (L.obj ((FR).obj ((ER).obj ((E).obj ((F).obj Z)))))) ^ r *
          Ring.inverse (φ (P.rpPreDot i s h U)) ^ (r+1) *
          φ (P.rpPostDot i s h U) ^ r) := by
  rw [map_probeToReservoirBend,
    P.crossCoeff_odd_evaluate c i s h U φ hc hi hx n hn, map_sum]

end ProbeToReservoir

section ReservoirToProbe
variable (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
  (hv : StepValid (true, i) false t) (Z : P.H t)
local notation "EP" => homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)
local notation "FP" => homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)
local notation "ER" => homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)
local notation "FR" => homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)
local notation "γ" => P.reservoirToProbeCoefficientChart i t hb hv ((FR).obj Z)
local notation "s" => nextSector (false, i) true t
local notation "U" =>
  ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ (FR).obj Z)
variable {C : Type*} [Category C] [Preadditive C] (L : P.H t ⥤ C) [L.Additive]

/-- The ring evaluation before the specified negative PR conjugation. -/
def reservoirToProbeBendCoefficientEvaluation :
    End (P.rpObj i i s hv U) →+* End (L.obj ((FP).obj ((EP).obj ((ER).obj ((FR).obj Z))))) :=
  ((bendFunctorEnd L _).comp (bendFunctorEnd (FP) _)).comp (bendConjugation γ)

/-- The prescribed probe unit and reservoir cap, with their existing
normalizations, after output evaluation. -/
def reservoirToProbeBendInsertion :
    End (L.obj ((FP).obj ((EP).obj ((ER).obj ((FR).obj Z))))) →+
      (L.obj ((ER).obj ((FR).obj Z)) ⟶ L.obj ((FP).obj ((EP).obj Z))) :=
  bendInsertion
    (L.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t)
      (P.muP_preF i hb)).unit.app _))
    (L.map ((FP).map ((EP).map ((homContentPostAdjunction P.T.obj P.W i t.1
      (P.muP t) (P.muM_postE i hv)).counit.app Z))))

/-- The XR-to-YP insertion retains the negative conjugation required
by the PR coefficient. -/
theorem map_reservoirToProbeBend (c : P.CrossCoeff) :
    L.map (P.reservoirToProbeBend c i t hb hv Z) =
      -reservoirToProbeBendInsertion P i t hb hv Z L
        (reservoirToProbeBendCoefficientEvaluation P i t hb hv Z L (c.a i s hv U)) := by
  rw [ProbeReservoir.reservoirToProbeBend, ProbeReservoir.reservoirToProbeCoefficient_eq_neg]
  dsimp only [reservoirToProbeBendInsertion, reservoirToProbeBendCoefficientEvaluation,
    bendInsertion, bendConjugation, bendFunctorEnd, RingHom.comp_apply]
  dsimp
  simp only [Functor.map_comp, Functor.map_neg,
    Preadditive.comp_neg, Preadditive.neg_comp]

local notation "φ" => reservoirToProbeBendCoefficientEvaluation P i t hb hv Z L
local notation "β" => reservoirToProbeBendInsertion P i t hb hv Z L

/-- The even coefficient's negative series cancels the fixed PR minus. -/
theorem reservoirToProbeBend_even_expansion (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 0) (hx : IsUnit (φ (P.rpPreDot i s hv U)))
    (n : ℕ) (hn : φ (P.rpPostDot i s hv U) ^ n = 0) :
    L.map (P.reservoirToProbeBend c i t hb hv Z) =
      ∑ r ∈ Finset.range n,
        β (Ring.inverse (φ (P.rpPreDot i s hv U)) ^ (r+1) *
          φ (P.rpPostDot i s hv U) ^ r) := by
  rw [map_reservoirToProbeBend,
    P.crossCoeff_even_evaluate c i s hv U φ hc hi hx n hn,
    map_neg, neg_neg, map_sum]

/-- The odd finite series retains the fixed PR minus as well as the
ordered alternating coefficients. -/
theorem reservoirToProbeBend_odd_expansion (c : P.CrossCoeff) (hc : c.IsInverse)
    (hi : D.parity i = 1) (hx : IsUnit (φ (P.rpPreDot i s hv U)))
    (n : ℕ) (hn : φ (P.rpPostDot i s hv U) ^ n = 0) :
    L.map (P.reservoirToProbeBend c i t hb hv Z) =
      -∑ r ∈ Finset.range (2*n),
        β ((-1 : End (L.obj ((FP).obj ((EP).obj ((ER).obj ((FR).obj Z)))))) ^ r *
          Ring.inverse (φ (P.rpPreDot i s hv U)) ^ (r+1) *
          φ (P.rpPostDot i s hv U) ^ r) := by
  rw [map_reservoirToProbeBend,
    P.crossCoeff_odd_evaluate c i s hv U φ hc hi hx n hn, map_sum]

end ReservoirToProbe
end OddMath.QuiverHecke.SwappedAssembly
