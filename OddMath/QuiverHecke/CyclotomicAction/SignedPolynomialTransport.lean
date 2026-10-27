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

private theorem zsign_nsmul (p : ZMod 2) (m : ℕ) :
    SKM.zsign k (m • p) = SKM.zsign k p ^ m := by
  induction m with
  | zero => simp [SKM.zsign]
  | succ m ih => rw [succ_nsmul, zsign_add_eq, ih, pow_succ]

private theorem end_smul_comp {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A B : C} (r : k) (x : End A) (g : A ⟶ B) :
    (r • x) ≫ g = r • (x ≫ g) := Linear.smul_comp _ _ _ r x g

private theorem comp_end_smul {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A B : C} (r : k) (g : A ⟶ B) (y : End B) :
    g ≫ (r • y) = r • (g ≫ y) := Linear.comp_smul _ _ _ g r y

private theorem polynomial_comp_of_signed_dot {C : Type*} [Category C]
    [Preadditive C] [Linear k C] {A B : C}
    (x : End A) (y : End B) (g : A ⟶ B) (p : ZMod 2)
    (h : x ≫ g = SKM.zsign k p • (g ≫ y)) (f : _root_.Polynomial k) :
    _root_.Polynomial.aeval x f ≫ g =
      g ≫ _root_.Polynomial.aeval (SKM.zsign k p • y) f := by
  simp only [_root_.Polynomial.aeval_eq_sum_range]
  change (∑ m ∈ Finset.range (f.natDegree + 1),
      f.coeff m • (x ^ m : A ⟶ A)) ≫ g =
    g ≫ (∑ m ∈ Finset.range (f.natDegree + 1),
      f.coeff m • ((SKM.zsign k p • y) ^ m : B ⟶ B))
  simp only [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [end_smul_comp, comp_end_smul, signed_pow_comp x y g p h,
    zsign_nsmul, smul_pow, comp_end_smul]

/-- Ordinary ground-ring polynomials transport by the signed dot substitution.
No support-parity restriction is imposed on the polynomial. -/
theorem polynomial_comp_moveHom (i : I) (l ν : List I) (f : _root_.Polynomial k) :
    _root_.Polynomial.aeval (dotE D Sc (l ++ i :: ν) l.length) f ≫ moveHom D Sc i l ν =
      moveHom D Sc i l ν ≫ _root_.Polynomial.aeval
        (SKM.zsign k (D.parity i * wordSumParity D ν) •
          dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length)) f :=
  polynomial_comp_of_signed_dot _ _ _ _ (dot_comp_moveHom D Sc i l ν) f

/-- The polynomial on any old strand has the total moving-chain sign,
not just the sign from its single adjacent crossing. -/
theorem polynomial_mem_comp_moveHom (i x : I) (v m l : List I)
    (f : _root_.Polynomial k) :
    _root_.Polynomial.aeval
        (dotE D Sc (l ++ i :: (m ++ x :: v)) (l.length + 1 + m.length)) f ≫
        moveHom D Sc i l (m ++ x :: v) =
      moveHom D Sc i l (m ++ x :: v) ≫ _root_.Polynomial.aeval
        (SKM.zsign k (D.parity x * (D.parity i * wordSumParity D (m ++ x :: v))) •
          dotE D Sc (l ++ (m ++ x :: v) ++ [i]) (l.length + m.length)) f :=
  polynomial_comp_of_signed_dot _ _ _ _
    (dot_mem_comp_moveHom D Sc i x v m l (m ++ x :: v) (by simp)) f

end OddMath.QuiverHecke
