/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.EndpointNormPolynomial

/-! # Evaluation of the ordered monic endpoint norm

Parity-supported old-dot powers commute with the moving dot even when the
individual dots do not. Evaluation therefore recovers the independent chain
norm times its explicit inverse leading unit, for arbitrary words.
-/
noncomputable section
namespace OddMath.QuiverHecke
open Polynomial IntertwinerMeet
universe u v
variable {I k : Type u} {L : Type v} [AddCommGroup L]
  (D : SKM.Datum I L) [CommRing k] (Sc : SKM.Scalars D k)
variable {B : Type*} [Ring B] [Algebra k B]

def NormCoeffCommute (x : B) (p : Polynomial B) : Prop :=
  ∀ n, Commute (p.coeff n) x

namespace NormCoeffCommute
variable {x : B} {p q : Polynomial B}
theorem const {a : B} (h : Commute a x) : NormCoeffCommute x (C a) := by
  intro n
  by_cases hn : n = 0 <;> simp [coeff_C, hn, h]
theorem X : NormCoeffCommute x (Polynomial.X : Polynomial B) := by
  intro n
  by_cases hn : 1 = n <;> simp [coeff_X, hn]
theorem add (hp : NormCoeffCommute x p) (hq : NormCoeffCommute x q) :
    NormCoeffCommute x (p + q) := by
  intro n
  simpa using (hp n).add_left (hq n)
theorem neg (hp : NormCoeffCommute x p) : NormCoeffCommute x (-p) := by
  intro n
  simpa using (hp n).neg_left
theorem sub (hp : NormCoeffCommute x p) (hq : NormCoeffCommute x q) :
    NormCoeffCommute x (p - q) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg
theorem mul (hp : NormCoeffCommute x p) (hq : NormCoeffCommute x q) :
    NormCoeffCommute x (p * q) := by
  intro n
  rw [coeff_mul]
  apply Commute.sum_left
  intro a ha
  exact (hp a.1).mul_left (hq a.2)
theorem pow (hp : NormCoeffCommute x p) (n : ℕ) : NormCoeffCommute x (p ^ n) := by
  induction n with
  | zero => simpa using (const (Commute.one_left x))
  | succ n ih => simpa only [pow_succ] using ih.mul hp
theorem eval_mul (hq : NormCoeffCommute x q) :
    (p * q).eval₂ (RingHom.id B) x =
      p.eval₂ (RingHom.id B) x * q.eval₂ (RingHom.id B) x :=
  eval₂_mul_noncomm _ _ hq
theorem eval_pow (hp : NormCoeffCommute x p) (n : ℕ) :
    (p ^ n).eval₂ (RingHom.id B) x = (p.eval₂ (RingHom.id B) x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, hp.eval_mul, ih, pow_succ]
end NormCoeffCommute

theorem eval₂_qLeft (u x : B) (d e : ℕ) (t₁ t₂ : k) (s : ℕ → ℕ → k) :
    (qLeft (C u) (X : Polynomial B) d e t₁ t₂ s).eval₂ (RingHom.id B) x =
      qLeft u x d e t₁ t₂ s := by
  have hx : (X ^ e : Polynomial B).eval x = x ^ e := eval₂_X_pow _ _
  simp [qLeft, eval₂_finsetSum, ← map_pow, hx]

theorem eval₂_endpointNormFactor (j i : I) (u x : B)
    (hodd : Commute (u ^ 2) x) (heven : D.parity j ≠ 1 → Commute u x) :
    (endpointNormFactor D Sc j i (C u) (X : Polynomial B)).eval₂ (RingHom.id B) x =
      endpointNormFactor D Sc j i u x := by
  unfold endpointNormFactor
  split_ifs with hji hp hd
  · have hc : NormCoeffCommute x ((C u : Polynomial B) ^ 2) := by
      simpa only [← map_pow] using NormCoeffCommute.const hodd
    have hx := (NormCoeffCommute.X (x := x)).pow 2
    rw [eval₂_neg, (hc.add hx).eval_mul, (hx.sub hc).eval_pow]
    simp [← map_pow]
  · rw [eval₂_neg, ((NormCoeffCommute.X (x := x)).sub
      (NormCoeffCommute.const (heven hp))).eval_pow]
    simp
  · simp [Polynomial.algebraMap_apply]
  · exact eval₂_qLeft u x _ _ _ _ _

theorem eval₂_normalizedEndpointNormFactor (j i : I) (u x : B)
    (hodd : Commute (u ^ 2) x) (heven : D.parity j ≠ 1 → Commute u x) :
    (normalizedEndpointNormFactor D Sc j i u).eval₂ (RingHom.id B) x =
      algebraMap k B ((endpointNormLeadingUnit D Sc j i)⁻¹ : kˣ) *
        endpointNormFactor D Sc j i u x := by
  unfold normalizedEndpointNormFactor
  rw [← Polynomial.algebraMap_apply, ← Algebra.smul_def, eval₂_id, eval_smul, ← eval₂_id,
    eval₂_endpointNormFactor D Sc j i u x hodd heven, Algebra.smul_def]

theorem NormCoeffCommute.smul {x : B} {p : Polynomial B}
    (hp : NormCoeffCommute x p) (a : k) : NormCoeffCommute x (a • p) := by
  intro n
  change Commute (a • p.coeff n) x
  rw [Algebra.smul_def]
  exact (Algebra.commute_algebraMap_left a x).mul_left (hp n)

theorem NormCoeffCommute.sum {x : B} {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial B) (h : ∀ a ∈ s, NormCoeffCommute x (f a)) :
    NormCoeffCommute x (∑ a ∈ s, f a) := by
  intro n
  rw [finsetSum_coeff]
  apply Commute.sum_left
  intro a ha
  exact h a ha n

theorem endpointNormFactor_coeffCommute (j i : I) (u x : B)
    (hpow : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 → Commute (u ^ n) x) :
    NormCoeffCommute x (endpointNormFactor D Sc j i (C u) (X : Polynomial B)) := by
  have hc (n : ℕ) (hn : (n : ZMod 2) * D.parity j = 0) :
      NormCoeffCommute x ((C u : Polynomial B) ^ n) := by
    simpa only [← map_pow] using NormCoeffCommute.const (hpow n hn)
  have hx := NormCoeffCommute.X (x := x)
  unfold endpointNormFactor
  split_ifs with hji hp hd
  · have hc2 := hc 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul])
    exact (((hx.pow 2).sub hc2).pow 2 |>.mul (hc2.add (hx.pow 2))).neg
  · have hc1 : NormCoeffCommute x (C u) := by
      simpa using hc 1 (by rw [parity_eq_zero_of_ne_one hp, mul_zero])
    exact ((hx.sub hc1).pow 2).neg
  · rw [Polynomial.algebraMap_apply]
    exact NormCoeffCommute.const (Algebra.commutes _ _)
  · unfold qLeft
    apply NormCoeffCommute.add
    · apply NormCoeffCommute.sum
      intro p hp
      apply NormCoeffCommute.sum
      intro q hq
      by_cases hs : Sc.s j i p q = 0
      · simp only [hs, zero_smul]
        simpa using (NormCoeffCommute.const (Commute.zero_left x))
      · apply NormCoeffCommute.smul
        apply NormCoeffCommute.mul _ (hx.pow q)
        exact hc p (zmod_two_eq_zero_of_ne_one fun h => hs (Sc.s_eq_zero j i p q h))
    · exact ((hc _ (dn_mul_parity D j i)).smul _).add ((hx.pow _).smul _)

theorem normalizedEndpointNormFactor_coeffCommute (j i : I) (u x : B)
    (hpow : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 → Commute (u ^ n) x) :
    NormCoeffCommute x (normalizedEndpointNormFactor D Sc j i u) := by
  exact (NormCoeffCommute.const (Algebra.commutes _ _)).mul
    (endpointNormFactor_coeffCommute D Sc j i u x hpow)

theorem norm_mul_pow_signed (a b : B) (e : k) (h : a * b = e • (b * a))
    (n : ℕ) : a * b ^ n = e ^ n • (b ^ n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h,
      mul_smul_comm, ← mul_assoc, smul_smul, ← pow_succ, ← pow_succ]

open CategoryTheory in
theorem norm_oldDot_pow_commute (l m : List I) (j i : I) (n : ℕ)
    (hn : (n : ZMod 2) * D.parity j = 0) :
    Commute (dotE D Sc (l ++ [j] ++ m ++ [i]) l.length ^ n)
      (dotE D Sc (l ++ [j] ++ m ++ [i]) (l.length + 1 + m.length)) := by
  have hs := genE_interchange D Sc l m [] (.dot j) (.dot i) rfl rfl
    (w := l ++ [j] ++ m ++ [i]) (by simp [Shape.dom]) (p := l.length)
    (q := l.length + 1 + m.length) rfl (by simp only [Shape.dom, List.length_append, List.length_singleton])
  simp only [Shape.parity, PG.ofShape] at hs
  have h := norm_mul_pow_signed _ _ _ hs n
  rw [zsign_pow, ← mul_assoc, hn, zero_mul] at h
  simp [SKM.zsign] at h
  exact h.symm

theorem normalizedEndpointNormPolynomial_coeffCommute (i : I) (xs : List (I × B)) (x : B)
    (h : ∀ z ∈ xs, ∀ n : ℕ, (n : ZMod 2) * D.parity z.1 = 0 → Commute (z.2 ^ n) x) :
    NormCoeffCommute x (normalizedEndpointNormPolynomial D Sc i xs) := by
  induction xs with
  | nil => exact NormCoeffCommute.const (Commute.one_left x)
  | cons z zs ih =>
    exact (normalizedEndpointNormFactor_coeffCommute D Sc z.1 i z.2 x
      (h z (by simp))).mul (ih fun a ha => h a (by simp [ha]))

theorem eval₂_normalizedEndpointNormPolynomial (i : I) (xs : List (I × B)) (x : B)
    (h : ∀ z ∈ xs, ∀ n : ℕ, (n : ZMod 2) * D.parity z.1 = 0 → Commute (z.2 ^ n) x) :
    (normalizedEndpointNormPolynomial D Sc i xs).eval₂ (RingHom.id B) x =
      algebraMap k B (((xs.map fun z => (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
        (xs.map fun z => endpointNormFactor D Sc z.1 i z.2 x).prod := by
  induction xs with
  | nil => simp [normalizedEndpointNormPolynomial]
  | cons z zs ih =>
    have ht := fun a ha => h a (List.mem_cons_of_mem z ha)
    rw [normalizedEndpointNormPolynomial,
      (normalizedEndpointNormPolynomial_coeffCommute D Sc i zs x ht).eval_mul,
      eval₂_normalizedEndpointNormFactor D Sc z.1 i z.2 x
        (h z (by simp) 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]))
        (fun hp => by simpa using h z (by simp) 1 (by rw [parity_eq_zero_of_ne_one hp, mul_zero])),
      ih ht]
    simp only [List.map_cons, List.prod_cons, Units.val_mul, map_mul]
    rw [mul_assoc, ← mul_assoc (endpointNormFactor D Sc z.1 i z.2 x),
      ← Algebra.commutes, ← mul_assoc, ← mul_assoc]
    exact mul_assoc _ _ _

open CategoryTheory

def endpointOldDotEntries (w : List I) : ℕ → List I → List (I × End ((pres D Sc).obj (ob D w)))
  | _, [] => []
  | p, j :: ν => (j, dotE D Sc w p) :: endpointOldDotEntries w (p + 1) ν

theorem endpointOldDotEntries_pow_commute (i : I) (ν l : List I) :
    ∀ z ∈ endpointOldDotEntries D Sc (l ++ ν ++ [i]) l.length ν,
      ∀ n : ℕ, (n : ZMod 2) * D.parity z.1 = 0 →
        Commute (z.2 ^ n) (dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length)) := by
  induction ν generalizing l with
  | nil => simp [endpointOldDotEntries]
  | cons j ν ih =>
    intro z hz n hn
    simp only [endpointOldDotEntries, List.mem_cons] at hz
    rcases hz with rfl | hz
    · have hh := norm_oldDot_pow_commute D Sc l ν j i n hn
      have hw : l ++ [j] ++ ν ++ [i] = l ++ (j :: ν) ++ [i] := by simp
      rw [hw] at hh
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ν.length] using hh
    · have hh := ih (l ++ [j])
      have hw : (l ++ [j]) ++ ν ++ [i] = l ++ (j :: ν) ++ [i] := by simp
      rw [hw] at hh
      simp only [List.length_append, List.length_singleton] at hh
      have hc := hh z hz n hn
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ν.length] using hc

theorem endpointOldDotEntries_eval_prod (i : I) (w : List I) (moving old : ℕ) (ν : List I) :
    ((endpointOldDotEntries D Sc w old ν).map fun z =>
      endpointNormFactor D Sc z.1 i z.2 (dotE D Sc w moving)).prod =
      endpointNormAux D Sc i w moving old ν := by
  induction ν generalizing old with
  | nil => rfl
  | cons j ν ih =>
    simp only [endpointOldDotEntries, List.map_cons, List.prod_cons, endpointNormAux, ih]

theorem eval₂_actual_normalizedEndpointNormPolynomial (i : I) (l ν : List I) :
    let xs := endpointOldDotEntries D Sc (l ++ ν ++ [i]) l.length ν
    (normalizedEndpointNormPolynomial D Sc i xs).eval₂ (RingHom.id _)
        (dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length)) =
      algebraMap k _ (((xs.map fun z => (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
        endpointNorm D Sc i l ν := by
  dsimp only
  rw [eval₂_normalizedEndpointNormPolynomial D Sc _ _ _
    (endpointOldDotEntries_pow_commute D Sc i ν l), endpointOldDotEntries_eval_prod]
  rfl

end OddMath.QuiverHecke
