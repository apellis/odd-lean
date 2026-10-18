import OddMath.SKM.Rho.Coefficients
import OddMath.SKM.Lemma33

/-!
# Powers for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

theorem coeff_pow_even (t : k) (ht : t ^ 2 = -1) (p : ZMod 2) (n : ℕ)
    (hp : p * (n : ZMod 2) = 0) :
    psiCoeff t p ^ n = zsign k (p * (n / 2 : ℕ)) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp [psiCoeff, zsign]
  · simp only [one_mul] at hp ⊢
    have hn : n % 2 = 0 := by
      have : (n : ZMod 2).val = 0 := congrArg ZMod.val hp
      simpa using this
    have he : n = 2 * (n / 2) := by omega
    rw [psiCoeff_one, he, pow_mul, ht]
    simpa [zsign] using (zsign_natCast_mul (k := k) (n / 2) (1 : ZMod 2)).symm

theorem placed_dot_power (ν : X) (u v : List (Letter I)) (i : I) (a : k) (n : ℕ) :
    cpow (a • cl D Sc ν (u ++ [dn i] ++ v) (u ++ [dn i] ++ v)
        ((ddotL i).map (whL u v))) n =
      a ^ n • cl D Sc ν (u ++ [dn i] ++ v) (u ++ [dn i] ++ v)
        ((ddotsL i n).map (whL u v)) := by
  induction n with
  | zero => simp [cpow, ddotsL, cl_nil]
  | succ n ih =>
    rw [cpow_succ, ih, Linear.smul_comp, Linear.comp_smul, smul_smul,
      cl_comp ((sChain_ddotsL i n).wh u v rfl rfl) ((sChain_ddotL i).wh u v rfl rfl), pow_succ]
    congr 2
    simp only [ddotsL, List.replicate_succ', List.flatten_append, List.flatten_singleton, List.map_append]

end OddMath.SKM.RhoCoefficients
