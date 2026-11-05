/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerWords

/-!
# Signed polynomial transport through an intertwiner chain

The ordinary-polynomial part of `DeformedProjectiveResolution.md`, §1,
used by the proposed QP induction in `DeformedGlobalQP.md`, §3. The
underlying dot identities are KKO I, arXiv:1206.5933v2, (8.13).

Every polynomial in the moving dot or an old strand dot transports through
the actual `moveHom`, by substituting the appropriate signed dot. No
polynomial parity or monicity hypothesis is required. Coefficients here
are in the purely even commutative ground ring. This does not transport
odd ELV coefficients or construct the balanced QP induction.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private theorem signed_pow_comp {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A B : C} (x : End A) (y : End B) (g : A ⟶ B) (p : ZMod 2)
    (h : x ≫ g = SKM.zsign k p • (g ≫ y)) (m : ℕ) :
    (x ^ m : End A) ≫ g = SKM.zsign k (m • p) • (g ≫ (y ^ m : End B)) := by
  induction m with
  | zero => simp [End.one_def, SKM.zsign]
  | succ m ih =>
    rw [pow_succ, End.mul_def, Category.assoc, ih, Linear.comp_smul,
      ← Category.assoc, h, Linear.smul_comp, smul_smul, ← zsign_add_eq,
      pow_succ, End.mul_def, succ_nsmul, Category.assoc]

/-- The moving-strand dot transport, for every exponent including zero. -/
theorem dot_pow_comp_moveHom (i : I) (l ν : List I) (m : ℕ) :
    (dotE D Sc (l ++ i :: ν) l.length ^ m : End _) ≫ moveHom D Sc i l ν =
      SKM.zsign k (m • (D.parity i * wordSumParity D ν)) •
        (moveHom D Sc i l ν ≫
          (dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length) ^ m : End _)) := by
  exact signed_pow_comp _ _ _ _ (dot_comp_moveHom D Sc i l ν) m

end OddMath.QuiverHecke
