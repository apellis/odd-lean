/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.BraidCorrection
import OddMath.QuiverHecke.CyclotomicAction.SuperCrossing

/-!
# Signed right operators for the three-strand braid

Ports the signed-operator input corresponding to
`Categorification/KLR/CyclotomicAction/Braid.lean`. The three crossing matrices
have their actual homogeneous degrees. On a graded regular module, reversing
three homogeneous right multipliers introduces a sign symmetric in their
three degrees. Thus the uncorrected braid remains valid as an equality of
signed operators. Identification with triple-superinduction remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- First-pair crossing parity on the actual triple-word corner. -/
theorem tripleCrossLeft_parity (i j c : I) {n : ℕ} (w : Word I n) :
    tripleCrossLeft D Sc i j c w ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
  unfold tripleCrossLeft cl
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, tripleWord, pl, PG.ld, Shape.parity]

/-- Last-pair crossing parity on the actual triple-word corner. -/
theorem tripleCrossRight_parity (i j c : I) {n : ℕ} (w : Word I n) :
    tripleCrossRight D Sc i j c w ∈ parity (R := k) _ _ (D.parity j * D.parity c) := by
  unfold tripleCrossRight cl
  apply Presentation.diag_mem_homDeg'
  have hle : w.1.length ≤ n + 1 := by omega
  simp [degree_parity_mkD, tripleWord, pl, PG.ld, Shape.parity, List.take_append,
    List.drop_append, List.take_of_length_le hle, List.drop_eq_nil_of_le hle]

variable [Fintype I]

theorem affineTripleLeft_parity (i j c : I) (n : ℕ) :
    affineTripleLeft D Sc i j c n ∈ affineParity D Sc (n + 3) (D.parity i * D.parity j) := by
  apply Submodule.sum_mem
  intro w _
  exact FiniteHomMatrix.single_mem_component _ _ (tripleCrossLeft_parity D Sc i j c w)

theorem affineTripleRight_parity (i j c : I) (n : ℕ) :
    affineTripleRight D Sc i j c n ∈ affineParity D Sc (n + 3) (D.parity j * D.parity c) := by
  apply Submodule.sum_mem
  intro w _
  exact FiniteHomMatrix.single_mem_component _ _ (tripleCrossRight_parity D Sc i j c w)

section Regular
variable {A : Type u} [Ring A] [Algebra k A]
  (G : ZMod 2 → Submodule k A) [GradedAlgebra G]

/-- Signed right multiplication on the existing graded regular module. -/
def regularSignedRight (p : ZMod 2) (a : A) :
    (SuperBimodule.regular G).toSVec ⟶ (SuperBimodule.regular G).toSVec :=
  SVec.ofHom ((SuperBimodule.regular G).toSVec.sgn p) ≫ (SuperBimodule.regular G).ract a

/-- Evaluation of signed right multiplication on a homogeneous element. -/
theorem regularSignedRight_apply (p : ZMod 2) (a x : A) {q : ZMod 2} (hx : x ∈ G q) :
    regularSignedRight G p a x = koszulSign q p • (x * a) := by
  change (show A from (SuperBimodule.regular G).toSVec.sgn p x) * a = _
  erw [SVec.sgn_apply_of_mem p ((SuperBimodule.mem_regularSVec_part_iff G).2 hx)]
  rw [smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

/-- The operator shifts the homogeneous degree by its multiplier degree. -/
theorem regularSignedRight_apply_mem {p q : ZMod 2} {a x : A}
    (ha : a ∈ G p) (hx : x ∈ G q) : regularSignedRight G p a x ∈ G (q + p) := by
  rw [regularSignedRight_apply G p a x hx]
  exact (G (q + p)).toAddSubgroup.zsmul_mem (SetLike.GradedMul.mul_mem hx ha) _

/-- The three-multiplier sign is invariant under reversing the degree list. -/
theorem regularSignedRight_triple_sign (p a b c : ZMod 2) :
    koszulSign (p + a + b) c * (koszulSign (p + a) b * koszulSign p a) =
      koszulSign (p + c + b) a * (koszulSign (p + c) b * koszulSign p c) := by
  revert p a b c
  decide

/-- Evaluate three homogeneous signed right multipliers, retaining their order. -/
theorem regularSignedRight_triple_apply {p q r s : ZMod 2} {a b c x : A}
    (ha : a ∈ G p) (hb : b ∈ G q) (hx : x ∈ G s) :
    regularSignedRight G r c (regularSignedRight G q b (regularSignedRight G p a x)) =
      (koszulSign (s + p + q) r * (koszulSign (s + p) q * koszulSign s p)) •
        (x * (a * (b * c))) := by
  rw [regularSignedRight_apply G r c _
    (regularSignedRight_apply_mem G hb (regularSignedRight_apply_mem G ha hx)),
    regularSignedRight_apply G q b _ (regularSignedRight_apply_mem G ha hx),
    regularSignedRight_apply G p a x hx]
  simp only [smul_mul_assoc, smul_smul, mul_assoc]

/-- A braid relation on homogeneous elements gives a braid of signed regular operators. -/
theorem regularSignedRight_braid {p q r s : ZMod 2} {a b c a' b' c' x : A}
    (ha : a ∈ G p) (hb : b ∈ G q) (ha' : a' ∈ G r) (hb' : b' ∈ G q)
    (hx : x ∈ G s) (hbraid : a * (b * c) = a' * (b' * c')) :
    regularSignedRight G r c (regularSignedRight G q b (regularSignedRight G p a x)) =
      regularSignedRight G p c' (regularSignedRight G q b' (regularSignedRight G r a' x)) := by
  rw [regularSignedRight_triple_apply G ha hb hx,
    regularSignedRight_triple_apply G ha' hb' hx, hbraid,
    regularSignedRight_triple_sign]

/-- The repeated-outside-colour sign separates the total degree and the crossing degree. -/
theorem regularSignedRight_correction_sign (s d e : ZMod 2) :
    koszulSign (s + d + e) d * (koszulSign (s + d) e * koszulSign s d) =
      koszulSign d d * koszulSign s e := by
  revert s d e
  decide

/-- The signed repeated-colour operator difference retains its super-opposite factor. -/
theorem regularSignedRight_braid_correction {d e s : ZMod 2} {a b c a' b' c' z x : A}
    (ha : a ∈ G d) (hb : b ∈ G e) (ha' : a' ∈ G d) (hb' : b' ∈ G e)
    (hx : x ∈ G s) (hbraid : a * (b * c) - a' * (b' * c') = z) :
    regularSignedRight G d c (regularSignedRight G e b (regularSignedRight G d a x)) -
      regularSignedRight G d c' (regularSignedRight G e b' (regularSignedRight G d a' x)) =
        koszulSign d d • regularSignedRight G e z x := by
  rw [regularSignedRight_triple_apply G ha hb hx,
    regularSignedRight_triple_apply G ha' hb' hx, ← smul_sub]
  change (koszulSign (s + d + e) d * (koszulSign (s + d) e * koszulSign s d)) •
    ((x * (a * (b * c)) - x * (a' * (b' * c'))) : A) =
      koszulSign d d • (show A from regularSignedRight G e z x)
  rw [← mul_sub, hbraid, regularSignedRight_correction_sign,
    regularSignedRight_apply G e z x hx, smul_smul]

end Regular

/-- The concrete cyclotomic braid as an equality of signed regular-module operators. -/
theorem cyclotomicSignedTriple_braid (i j c : I) (hb : ¬ (i = c ∧ i ≠ j))
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    {s : ZMod 2} (x : CyclotomicAlgebra D Sc a (n + 2))
    (hx : x ∈ cyclotomicParity D Sc a ha (n + 2) s) :
    regularSignedRight (cyclotomicParity D Sc a ha (n + 2)) (D.parity i * D.parity j)
      (cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc i j c n))
      (regularSignedRight (cyclotomicParity D Sc a ha (n + 2)) (D.parity i * D.parity c)
        (cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc j i c n))
        (regularSignedRight (cyclotomicParity D Sc a ha (n + 2)) (D.parity j * D.parity c)
          (cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc j c i n)) x)) =
      regularSignedRight (cyclotomicParity D Sc a ha (n + 2)) (D.parity j * D.parity c)
        (cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc i j c n))
        (regularSignedRight (cyclotomicParity D Sc a ha (n + 2)) (D.parity i * D.parity c)
          (cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc i c j n))
          (regularSignedRight (cyclotomicParity D Sc a ha (n + 2)) (D.parity i * D.parity j)
            (cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc c i j n)) x)) := by
  apply regularSignedRight_braid _
    (cyclotomicMk_parity D Sc a ha (n + 2) (affineTripleLeft_parity D Sc j c i n))
    (cyclotomicMk_parity D Sc a ha (n + 2) (affineTripleRight_parity D Sc j i c n))
    (cyclotomicMk_parity D Sc a ha (n + 2) (affineTripleRight_parity D Sc c i j n))
    (cyclotomicMk_parity D Sc a ha (n + 2) (affineTripleLeft_parity D Sc i c j n)) hx
  exact cyclotomicTriple_braid D Sc i j c hb a n

/-- The concrete signed repeated-colour braid, with its explicit polynomial correction. -/
theorem cyclotomicSignedTriple_braid_correction (i j : I) (hij : i ≠ j)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    {s : ZMod 2} (x : CyclotomicAlgebra D Sc a (n + 2))
    (hx : x ∈ cyclotomicParity D Sc a ha (n + 2) s) :
    let L := fun i j c => cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc i j c n)
    let R := fun i j c => cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc i j c n)
    let T := regularSignedRight (cyclotomicParity D Sc a ha (n + 2))
    let d := D.parity i * D.parity j
    let e := D.parity i * D.parity i
    T d (L i j i) (T e (R j i i) (T d (L j i i) x)) -
        T d (R i j i) (T e (L i i j) (T d (R i i j) x)) =
      koszulSign d d • T e (cyclotomicMk D Sc a (n + 2)
        (affineTripleBraidCorrection D Sc i j n)) x := by
  dsimp only
  apply regularSignedRight_braid_correction _
    (by simpa only [mul_comm] using
      cyclotomicMk_parity D Sc a ha (n + 2) (affineTripleLeft_parity D Sc j i i n))
    (cyclotomicMk_parity D Sc a ha (n + 2) (affineTripleRight_parity D Sc j i i n))
    (cyclotomicMk_parity D Sc a ha (n + 2) (affineTripleRight_parity D Sc i i j n))
    (cyclotomicMk_parity D Sc a ha (n + 2) (affineTripleLeft_parity D Sc i i j n)) hx
  exact cyclotomicTriple_braid_correction D Sc i j hij a n

end OddMath.QuiverHecke
