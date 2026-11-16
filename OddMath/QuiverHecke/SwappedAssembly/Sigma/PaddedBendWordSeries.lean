import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWindowEquations
import OddMath.SKM.RouquierHomBendMonomials

/-! # The padded Dx series in negative-cap and post-unit words

SwappedHomInversion §3 (4)–(5): remove only the two prescribed padded
corner charts and retain the given negative pre-caps and dotted post-units.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace ProbeReservoir
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)
  {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  (i : I) (t : Sector I) (Z : P.H t) (L : P.H t ⥤ C) [L.Additive]
  (hdot : ∀ {a b : X} (h : a + D.α i = b), IsIso (P.T.dot i h))

omit [L.Additive] in
/-- A given separated padded Dx equation is exactly the sum of the
prescribed negative pre-cap/post-unit words in its two given corner
charts. The finite equation is the existing Dx input, rather than a
compatibility hypothesis identifying any endpoint or bend. -/
theorem centralPaddedDx_word_series (c : P.CrossCoeff) (N : ℕ)
    (hDx : P.CentralPaddedDxSeparatedAt i t Z L hdot c N) :
    P.centralPaddedSigma c i t Z L true false =
      -∑ r ∈ Finset.range N, (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) •
        ((P.centralSourceCornerIso i t Z L ⟨true, by trivial⟩).hom ≫
          L.map (letI := hdot (P.muP_preE i t)
            homPreNegativeCap P.T P.W.obj i (P.muM t) (P.muP_preE i t) (r + 1) Z ≫
              homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z) ≫
          (P.centralTargetCornerIso i t Z L ⟨false, by trivial⟩).inv) := by
  classical
  let := hdot (P.muP_preE i t)
  have hs : StepValid (up i) true t := by trivial
  have ht : StepValid (dn i) false t := by trivial
  rw [hDx]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  rw [centralPaddedProbeX, ProbeWindow.cornerAut_zpow_hom,
    centralPaddedCap, dite_eq_left hs, centralPaddedUnit, dite_eq_left ht]
  simp only [centralFactorCap, centralFactorUnit, homReservoirCap, pow_zero, End.one_def,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [homPreNegativeCap_aut]
  simp only [Functor.map_comp, Category.assoc]
  rw [← map_zpow]
  rfl

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
