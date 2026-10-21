import OddMath.SKM.K0Inversion
import OddMath.SKM.K0Shifts
import OddMath.SKM.CoveringDatum
import OddMath.CoveringQuantum.UDot.Basic

/-!
# The covering commutator on completed SKM weight blocks

BE2 Lemma 11.6, first relation, in the coefficient convention of
`CoveringQuantum.UDot.Rel.comm`. The positive and negative weight cases
are consequences of inversion (1.13) and (1.14), not assumptions.
-/

noncomputable section
namespace OddMath.SKM.K0Relations
open CategoryTheory StringDiagrams LaurentPolynomial CoveringQuantum

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] (Sc : Scalars D k) (sy : Symmetrizer D)
  (hc : Sc.Homogeneous)

attribute [local instance] homModule

/-- A single covering parity parameter acts by its parity shift. -/
theorem piCoeff_blockClass (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (m : ℤ) (a p : ZMod 2) :
    piCoeff p • blockClass Sc sy hc μ ν s hs m a =
      blockClass Sc sy hc μ ν s hs m (a + p) := by
  simpa only [piCoeff, ZMod.natCast_zmod_val] using pi_pow_blockClass Sc sy hc μ ν s hs m a p.val

/-- The quantum integer identity needed by negative-weight inversion. -/
theorem qpInt_negative (d : ℤ) (p : ZMod 2) (m : ℕ) :
    -(piCoeff p * qpNat (qUnit (-d)) (piCoeff p) m) =
      qpInt (qUnit d) (piCoeff p) (-(m : ℤ)) := by
  have hi : qUnit (-d) = (qUnit d)⁻¹ := by ext; rfl
  rw [hi, ← qpInt_ofNat, qpInt_inv_eq_neg (piCoeff_sq p), mul_neg, neg_neg,
    ← mul_assoc, ← pow_two, piCoeff_sq, one_mul]

private theorem commutator_of_positive {R A : Type*} [CommRing R] [AddCommGroup A]
    [Module R A] (e f u : A) (p c : R) (h : e = p • f + c • u) :
    e - p • f = c • u := by rw [h]; abel

private theorem commutator_of_negative {R A : Type*} [CommRing R] [AddCommGroup A]
    [Module R A] (e f u : A) (p c : R) (hp : p ^ 2 = 1) (h : f = p • e + c • u) :
    e - p • f = -(p * c) • u := by
  rw [h, smul_add, smul_smul, smul_smul, ← pow_two, hp, one_smul, neg_smul]
  abel

/-- Lemma 11.6, same colour, with the covering quantum integer coefficient. -/
theorem comm_same (i : I) (ν : X) :
    blockClass Sc sy hc ν ν [up i, dn i] (by simp [wt, sh]) 0 0 -
      piCoeff (D.parity i) • blockClass Sc sy hc ν ν [dn i, up i] (by simp [wt, sh]) 0 0 =
      qpInt (qUnit (sy.d i)) (piCoeff (D.parity i)) (D.h i ν) •
        blockClass Sc sy hc ν ν [] rfl 0 0 := by
  by_cases hh : 0 ≤ D.h i ν
  · have h := mixed_nonneg Sc sy hc i ν 0 hh
    change blockClass Sc sy hc ν ν [up i, dn i] _ 0 0 =
      blockClass Sc sy hc ν ν [dn i, up i] _ 0 (D.parity i + 0) +
      ∑ n : Fin (D.h i ν).toNat, blockClass Sc sy hc ν ν [] rfl
        (sy.d i * (D.h i ν - 1 - 2 * n.val)) (n.val * D.parity i + 0) at h
    simp only [add_zero] at h
    have hs := qpNat_blockClass Sc sy hc ν ν [] rfl (sy.d i) (D.parity i) (D.h i ν).toNat
    simp only [Int.toNat_of_nonneg hh] at hs
    have hr := Fin.sum_univ_eq_sum_range (fun n => blockClass Sc sy hc ν ν [] rfl
      (sy.d i * (D.h i ν - 1 - 2 * n)) (n * D.parity i)) (D.h i ν).toNat
    have he := piCoeff_blockClass Sc sy hc ν ν [dn i, up i] (by simp [wt, sh]) 0 0 (D.parity i)
    simp only [zero_add] at he
    have hcq : qpNat (qUnit (sy.d i)) (piCoeff (D.parity i)) (D.h i ν).toNat =
        qpInt (qUnit (sy.d i)) (piCoeff (D.parity i)) (D.h i ν) := by
      conv_rhs => rw [← Int.toNat_of_nonneg hh, qpInt_ofNat]
    exact commutator_of_positive (R := LaurentPolynomial Zπ) _ _ _ _ _
      (h.trans (congrArg₂ (· + ·) he.symm
        ((hr.trans hs.symm).trans (congrArg (fun c => c • blockClass Sc sy hc ν ν [] rfl 0 0) hcq))))
  · have hh' : D.h i ν ≤ 0 := le_of_lt (lt_of_not_ge hh)
    have h := mixed_nonpos Sc sy hc i ν 0 hh'
    change blockClass Sc sy hc ν ν [dn i, up i] _ 0 0 =
      blockClass Sc sy hc ν ν [up i, dn i] _ 0 (D.parity i + 0) +
      ∑ n : Fin (-D.h i ν).toNat, blockClass Sc sy hc ν ν [] rfl
        (sy.d i * (D.h i ν + 1 + 2 * n.val)) (n.val * D.parity i + 0) at h
    simp only [add_zero] at h
    have hs : (∑ n : Fin (-D.h i ν).toNat, blockClass Sc sy hc ν ν [] rfl
        (sy.d i * (D.h i ν + 1 + 2 * n.val)) (n.val * D.parity i)) =
      qpNat (qUnit (-sy.d i)) (piCoeff (D.parity i)) (-D.h i ν).toNat •
        blockClass Sc sy hc ν ν [] rfl 0 0 := by
      rw [qpNat_blockClass, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -D.h i ν)]
      ring
    have he := piCoeff_blockClass Sc sy hc ν ν [up i, dn i] (by simp [wt, sh]) 0 0 (D.parity i)
    simp only [zero_add] at he
    have hhneg := commutator_of_negative (R := LaurentPolynomial Zπ) _ _ _ _ _ (piCoeff_sq (D.parity i))
      (h.trans (congrArg₂ (· + ·) he.symm hs))
    have hw : D.h i ν = -(((-D.h i ν).toNat : ℕ) : ℤ) := by omega
    have hcoeff := qpInt_negative (sy.d i) (D.parity i) (-D.h i ν).toNat
    rw [← hw] at hcoeff
    exact hhneg.trans (congrArg (fun c => c • blockClass Sc sy hc ν ν [] rfl 0 0) hcoeff)

/-- Lemma 11.6, distinct colours, with the covering parity coefficient. -/
theorem comm_ne (i j : I) (ν μ : X)
    (hs : wt D ν [up i, dn j] = μ) (ht : wt D ν [dn j, up i] = μ) (hij : i ≠ j) :
    blockClass Sc sy hc μ ν [up i, dn j] hs 0 0 -
      piCoeff (D.parity i * D.parity j) •
        blockClass Sc sy hc μ ν [dn j, up i] ht 0 0 = 0 := by
  rw [piCoeff_blockClass, zero_add, sub_eq_zero]
  exact K₀.mk_eq_mk_of_iso
    ((inclusion Sc sy hc μ ν).mapIso (mixedIso Sc sy hc i j ν μ hs ht hij))

/-- The proved weight and mixed-relation part of the well-definedness argument for
Theorem 11.7. The mixed equations are stated in their completed weight blocks;
weight multiplication uses `Grothendieck`, the opposite ring convention of BE2.
No Serre or divided-power relation is an assumption of this statement. This is
not the descended homomorphism, whose remaining presentation relations are separate. -/
theorem weight_mixed_relations :
    WeightRelations Sc sy hc ∧
    (∀ i j ν μ hs ht, i ≠ j →
      blockClass Sc sy hc μ ν [up i, dn j] hs 0 0 -
        piCoeff (D.parity i * D.parity j) •
          blockClass Sc sy hc μ ν [dn j, up i] ht 0 0 = 0) ∧
    (∀ i ν, blockClass Sc sy hc ν ν [up i, dn i] (by simp [wt, sh]) 0 0 -
      piCoeff (D.parity i) • blockClass Sc sy hc ν ν [dn i, up i] (by simp [wt, sh]) 0 0 =
      qpInt (qUnit (sy.d i)) (piCoeff (D.parity i)) (D.h i ν) •
        blockClass Sc sy hc ν ν [] rfl 0 0) :=
  ⟨weight_relations Sc sy hc, comm_ne Sc sy hc, comm_same Sc sy hc⟩

/-- The `qᵢ` coefficient is the one used in `CoveringQuantum.UDot`. -/
theorem root_qi (Q : RootDatum I X) (i : I) :
    Q.qi (k := LaurentPolynomial Zπ) (qUnit 1) i = qUnit (Q.d i) := by
  apply Units.ext
  simp [SuperCartanDatum.qi, qUnit, T_pow]

/-- Same-colour commutation with precisely the coefficient API in
`CoveringQuantum.UDot.Rel.comm`, on the shared covering root datum. -/
theorem covering_comm_same (Q : RootDatum I X) (S : Scalars Q.toSKM k)
    (hS : S.Homogeneous) (i : I) (ν : X) :
    blockClass S Q.skmSymmetrizer hS ν ν [up i, dn i] (by simp [wt, sh]) 0 0 -
      Q.pii (C Zπ.π) i •
        blockClass S Q.skmSymmetrizer hS ν ν [dn i, up i] (by simp [wt, sh]) 0 0 =
      qpInt (Q.qi (qUnit 1) i) (Q.pii (C Zπ.π) i) (Q.h i ν) •
        blockClass S Q.skmSymmetrizer hS ν ν [] rfl 0 0 := by
  rw [root_qi]
  exact comm_same S Q.skmSymmetrizer hS i ν

end OddMath.SKM.K0Relations
