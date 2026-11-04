import OddMath.SKM.RouquierHomDistinctMixedPostDotsIso

/-! # Source polynomial units for distinct-colour mixed mates

The source-polynomial step of the swapped distinct-colour inversion proof
(BE2 (1.11), SwappedDistinctMixedMates (13)–(15)) only needs units of its
source polynomials. This intermediate criterion permits componentwise
nilpotence on a product of content categories; it does not assert a single
nilpotence exponent on the whole weight category.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
  {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0) {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0)

/-- The source polynomials with positive post-dot remainder are units.
This is an intermediate input to distinct-colour inversion. -/
def MixedPostSourceUnits (x : E ⟶ E) (y : E' ⟶ E') : Prop :=
  ∀ (c : kˣ) (n : ℕ) (N : End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))),
    N ∈ admissibleMonomials (k := k)
      (mixedPostSourcePreDot (k := k) E κ H (F' := F') x)
      (mixedPostSourcePostDot (k := k) E κ H A y)
      (fun _ => True) (fun _ => True) 1 →
    IsUnit ((c : k) • mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ n + N)

include hx hy in
/-- The dotted mate is invertible from source-polynomial units; no global
nilpotence hypothesis on the postcomposed edge is required. -/
theorem homDistinctMixedMateDot_isIso_of_sourceUnits
    (hu : MixedPostSourceUnits E A κ H x y) (c : kˣ) (e : ℕ) {N}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y)
      (fun _ => True) (fun _ => True) 1) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((c : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ e + N)) := by
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_homDistinctMixedMateDot_eq E A κ τ H hx hy 1 hN
  have h0 := homDistinctMixedMateDot_pow_mul_pow E A κ τ H hx hy e 0
  simp only [pow_zero, mul_one] at h0
  rw [← homDistinctMixedMateDotLinear_apply, map_add, map_smul,
    homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply, h0, hΨe,
    ← Linear.smul_comp, ← Preadditive.add_comp]
  have : IsIso ((c : k) • mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ e + Ψ :
      End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) :=
    (isUnit_iff_isIso _).mp (hu c e Ψ hΨ)
  infer_instance

end Mate
end OddMath.SKM
