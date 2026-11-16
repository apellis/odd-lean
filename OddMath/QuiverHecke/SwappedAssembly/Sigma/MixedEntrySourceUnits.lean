import OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntry
import OddMath.SKM.RouquierHomDistinctSourceUnits

/-! # Distinct-colour entries from source polynomial units

BE2 (1.11), in the swapped construction: the mixed entry only needs the
source polynomial unit criterion. The ELV application must discharge this
criterion using contentwise transpose bounds, rather than a global
nilpotence hypothesis. This module is an intermediate reduction.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB vB wB
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{wB, vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

theorem isIso_homDistinctMixedMateDot_of_pow_sourceUnits {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d}
    {F' : d ⟶ c} (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
    {x : E ⟶ E} {y : E' ⟶ E'} {ex ey : ℕ}
    (hx : rouquierPower x ex ∈ parity (R := k) E E 0)
    (hy : rouquierPower y ey ∈ parity (R := k) E' E' 0)
    (hu : MixedPostSourceUnits E A κ H (rouquierPower x ex) (rouquierPower y ey)) (c : kˣ) (n : ℕ) {N}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ ex)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ ey)
      (fun _ => True) (fun _ => True) 1) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((c : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ (ex * n) +
        N)) := by
  have hX : mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ ex =
      mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') (rouquierPower x ex) :=
    whiskerRight_rouquierPower (k := k) x _ ex
  have hY : mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ ey =
      mixedPostTargetPostDot (k := k) E κ H (F' := F') (rouquierPower y ey) := by
    rw [whiskerLeft_rouquierPower (k := k), rouquierPower_eq_pow, ← map_rouquierPower,
      rouquierPower_eq_pow, whiskerLeft_rouquierPower (k := k)]
  rw [hX, hY] at hN
  rw [pow_mul, hX]
  exact homDistinctMixedMateDot_isIso_of_sourceUnits E A κ τ H hx hy hu c n hN

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
