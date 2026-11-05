import OddMath.QuiverHecke.CyclotomicAction.ELVPowerVacuumContentRows
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoordinates

/-! # The normalized inverse cap on the tensor vacuum

SwappedVacuumCoordinates §6: transport the prescribed regular power-vacuum
cap through the actual even tensor-vacuum isomorphism. Inverse-row
uniqueness identifies the result with the given native boundary inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u v w

private theorem inverseRow_even_iso
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C] [Preadditive C]
    [Linear k C] [Supercategory k C] {A₀ A₁ B Z₀ Z₁ : C}
    {g₀ : ℕ → (Z₀ ⟶ A₀)} {g₁ : ℕ → (Z₁ ⟶ A₁)}
    {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
    (J₀ : SKM.SuperSumInvFrom (k := k) (0 : B ⟶ A₀) g₀ p q n)
    (J₁ : SKM.SuperSumInvFrom (k := k) (0 : B ⟶ A₁) g₁ p q n)
    (a : A₀ ≅ A₁) (z : Z₀ ≅ Z₁)
    (hg : ∀ m, m < n → g₀ m ≫ a.hom = z.hom ≫ g₁ m)
    (r : ℕ) (hr : r < n) :
    J₀.g' r = a.hom ≫ J₁.g' r ≫ z.inv := by
  have h := J₀.row_intertwine J₁ a.hom (𝟙 B) z.hom 0
    (by simp only [Limits.zero_comp, Limits.comp_zero, smul_zero])
    (fun m hm => by simpa only [koszulSign_zero_right, one_smul] using hg m hm) r hr
  simp only [koszulSign_zero_right, one_smul] at h
  have hc := congrArg (fun f => f ≫ z.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc.symm

private theorem chronological_pow_intertwine
    {C : Type v} [Category.{w} C] {A B : C} (x : End A) (y : End B) (f : A ⟶ B)
    (h : x ≫ f = f ≫ y) (n : ℕ) : (x ^ n) ≫ f = f ≫ (y ^ n) := by
  induction n with
  | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
  | succ n ih =>
    calc
      (x ^ (n + 1)) ≫ f = x ≫ ((x ^ n) ≫ f) := by
        rw [pow_succ, End.mul_def, Category.assoc]
      _ = x ≫ (f ≫ (y ^ n)) := congrArg (fun g => x ≫ g) ih
      _ = (x ≫ f) ≫ (y ^ n) := (Category.assoc _ _ _).symm
      _ = (f ≫ y) ≫ (y ^ n) := congrArg (fun g => g ≫ (y ^ n)) h
      _ = f ≫ (y ^ (n + 1)) := by rw [pow_succ, End.mul_def, Category.assoc]

private theorem unitDotColumn_input_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {M P : Superfunctor k C (SVec k)} (f : M ⟶ P)
    (hf : f ∈ parity (R := k) M P 0) (n : ℕ) :
    unitDotColumn J hα M n ≫ (restriction J).map ((induction J).map f) =
      f ≫ unitDotColumn J hα P n := by
  have hd := (transformComponent_supernatural hα).naturality hf
  rw [mul_zero, sign_zero, one_smul] at hd
  change (induction J).map f ≫ dotEnd J hα P = dotEnd J hα M ≫ (induction J).map f at hd
  have hp := chronological_pow_intertwine (dotEnd J hα M) (dotEnd J hα P)
    ((induction J).map f) hd.symm n
  have hu := (adjunction J).unit.naturality f
  change f ≫ (adjunction J).unit.app P =
    (adjunction J).unit.app M ≫ (restriction J).map ((induction J).map f) at hu
  unfold unitDotColumn
  rw [Category.assoc, ← Functor.map_comp, hp, Functor.map_comp, ← Category.assoc, ← hu,
    Category.assoc]

private theorem inverseIso_cancel_right
    {C : Type v} [Category.{w} C] {A B V W : C} (a : V ≅ B) (f : A ⟶ W) (g : W ⟶ B) :
    (f ≫ g ≫ a.inv) ≫ a.hom = f ≫ g := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem unit_column_window_to_powers
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (ell : (restriction J).obj (induced J M) ⟶ M)
    (n : ℕ) (t : M ⟶ M) (h : unitDotColumn J hα M n ≫ ell = t) :
    (adjunction J).unit.app M ≫ (restrictedDotEnd J hα M ^ n) ≫ ell = t := by
  rw [← Category.assoc, ← unitDotColumn_eq_restrictedDotEnd J hα M n]
  exact h

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ) (i : I)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "W₀" => Functor.obj (restriction Q₀) WM
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D Sc m)
local notation "K" => contentAppendTo D Sc cutoff bound (0 : Multiset I) [i]
  ((0 : Multiset I) + ([i] : Multiset I)) (contentBlockCanonicalSum 0 [i])
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff bound 0 i
local notation "G" => induction K ⋙ restriction K
local notation "e" => VacuumTensor.probeVacuumIso D Sc m cutoff bound W₀

/-- The normalized cap on the exact tensor-vacuum carrier, using the even
evaluation isomorphism and the original regular power-vacuum cap. -/
def tensorPowerVacuumCap (hN : 0 < cutoff i) : (G).obj V ⟶ V :=
  (G).map (e).hom ≫ contentPowerVacuumCap D Sc cutoff i L hN ≫ (e).inv

/-- This transported cap is literally the final row of the constructed
native unit-column inverse on H(N0), rather than an arbitrary extractor. -/
theorem tensorPowerVacuumCap_eq_inverseRow (hN : 0 < cutoff i)
    (J : SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff bound (0 : Multiset I) ⟶ (G).obj V)
      (unitDotColumn K hDot V) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i 0)) :
    tensorPowerVacuumCap D Sc m cutoff L i hN = J.g' (cutoff i - 1) := by
  let JW := Classical.choice (contentAbsentUnitInverse_nonempty D Sc cutoff bound 0 i (by simp) W₀)
  have hr : cutoff i - 1 < contentUnitCount D cutoff i 0 := by
    simp only [contentUnitCount, contentCrossingHeight, Multiset.map_zero,
      Multiset.sum_zero, sub_zero, Int.toNat_natCast]
    omega
  have hc := inverseRow_even_iso J JW ((G).mapIso e) e
    (fun a _ => unitDotColumn_input_even K hDot (e).hom
      (VacuumTensor.probeVacuumIso_hom_mem D Sc m cutoff bound W₀) a) (cutoff i - 1) hr
  have hW := contentPowerVacuumCap_eq_inverseRow D Sc cutoff i L hN JW
  rw [← hW] at hc
  exact hc.symm

/-- The native inverse cap commutes with the genuine evaluation coordinate
as a whole module square. Thus its scalar decoding is the same literal-T
lambda already attached to the regular power vacuum. -/
theorem tensorPowerVacuumCap_compare (hN : 0 < cutoff i) :
    tensorPowerVacuumCap D Sc m cutoff L i hN ≫ (e).hom =
      (G).map (e).hom ≫ contentPowerVacuumCap D Sc cutoff i L hN :=
  inverseIso_cancel_right e ((G).map (e).hom) (contentPowerVacuumCap D Sc cutoff i L hN)

/-- The prescribed tensor-vacuum unit/dot columns have the exact normalized
cap window on every coefficient vector. -/
theorem tensorPowerVacuumCap_unitDotColumn (hN : 0 < cutoff i)
    (a : ℕ) (ha : a < cutoff i) :
    unitDotColumn K hDot V a ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 := by
  let J := Classical.choice (contentAbsentUnitInverse_nonempty D Sc cutoff bound 0 i (by simp) V)
  rw [tensorPowerVacuumCap_eq_inverseRow D Sc m cutoff L i hN J]
  have hc : contentUnitCount D cutoff i (0 : Multiset I) = cutoff i := by
    simp only [contentUnitCount, contentCrossingHeight, Multiset.map_zero,
      Multiset.sum_zero, sub_zero, Int.toNat_natCast]
  have hw := J.gg a (cutoff i - 1) (by omega) (by omega)
  exact hw.trans (if_congr (by omega) rfl rfl)

/-- The exact unit/dot/extractor window required by InverseCapMoments,
now on the same tensor-vacuum module as the evaluated mixed bend. -/
theorem tensorPowerVacuumCap_window (hN : 0 < cutoff i)
    (a : ℕ) (ha : a < cutoff i) :
    (adjunction K).unit.app V ≫ (restrictedDotEnd K hDot V ^ a) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 :=
  unit_column_window_to_powers K hDot V _ a _
    (tensorPowerVacuumCap_unitDotColumn D Sc m cutoff L i hN a ha)

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
