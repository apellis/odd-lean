/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.CapDecoratedNormalization
import OddMath.SKM.LeftCupFamilyCoefficients

/-! Finite cap-class coefficients in BE2, arXiv:1701.04133v2,
Theorem 10.3 Claim 5. The constructed decorated-family correspondence
separates the cap count from independently serialized shorter labels.
The convolution is indexed by the finite image of the affine degree fiber,
not an arbitrary truncation or a sum of an unsupported infinite family. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators

/-- A parity-valued dot count specializes to a natural power. -/
theorem parity_pow_nat_mul (σ : ℚ) (hσ : σ ^ 2 = 1) (n : ℕ) (p : ZMod 2) :
    σ ^ ((n : ZMod 2) * p).val = (σ ^ p.val) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, parity_pow_add σ hσ, ih, pow_succ]

private theorem fibre_sum_equiv {J K : Type*} {d : J → ℤ} {e : K → ℤ}
    (F : J ≃ K) (z : ℤ) (hf : Set.Finite {t | d t = z})
    (hg : Set.Finite {u | e u = z})
    (G : {t // d t = z} ≃ {u // e u = z}) (hG : ∀ t, (G t).val = F t.val)
    (f : J → ℚ) (g : K → ℚ) (hw : ∀ t, f t = g (F t)) :
    (∑ t ∈ hf.toFinset, f t) = ∑ u ∈ hg.toFinset, g u := by
  classical
  refine Finset.sum_bij (fun t ht => (G ⟨t, hf.mem_toFinset.mp ht⟩).val) ?_ ?_ ?_ ?_
  · intro t ht
    exact hg.mem_toFinset.mpr (G ⟨t, hf.mem_toFinset.mp ht⟩).property
  · intro t ht s hs he
    exact congrArg Subtype.val (G.injective (Subtype.ext he))
  · intro u hu
    let t := G.symm ⟨u, hg.mem_toFinset.mp hu⟩
    exact ⟨t.val, hf.mem_toFinset.mpr t.property,
      congrArg Subtype.val (G.apply_symm_apply ⟨u, hg.mem_toFinset.mp hu⟩)⟩
  · intro t ht
    rw [hG]
    exact hw t

/-- Split a finite affine pair fiber by its occurring cap counts.
Every inner sum is the entire shorter degree fiber at the shifted degree. -/
theorem affine_fibre_convolution {K : Type*} (e : K → ℤ) (δ v z : ℤ)
    (hg : Set.Finite {u : ℕ × K | e u.2 + δ + v * u.1 = z})
    (he : ∀ w : ℤ, Set.Finite {u | e u = w}) (β : ℚ) (w : K → ℚ) :
    (∑ u ∈ hg.toFinset, β ^ u.1 * w u.2) =
      ∑ n ∈ hg.toFinset.image Prod.fst,
        β ^ n * ∑ u ∈ (he (z - δ - v * n)).toFinset, w u := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := hg.toFinset) (t := hg.toFinset.image Prod.fst) (g := Prod.fst)
    (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) (fun u : ℕ × K => β ^ u.1 * w u.2)]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun u _ => u.2) ?_ ?_ ?_ ?_
  · intro u hu
    obtain ⟨hu, hn⟩ := Finset.mem_filter.mp hu
    have hd := hg.mem_toFinset.mp hu
    apply (he _).mem_toFinset.mpr
    change e u.2 + δ + v * u.1 = z at hd
    change e u.2 = z - δ - v * n
    rw [hn] at hd
    omega
  · intro u hu v hv h
    exact Prod.ext ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm) h
  · intro u hu
    have hd := (he _).mem_toFinset.mp hu
    refine ⟨(n, u), Finset.mem_filter.mpr ⟨hg.mem_toFinset.mpr ?_, rfl⟩, rfl⟩
    change e u = z - δ - v * n at hd
    change e u + δ + v * n = z
    omega
  · intro u hu
    rw [(Finset.mem_filter.mp hu).2]

variable {I X : Type*} [AddCommGroup X]
section Family
variable {a b : List (Letter I)} {ε : Bool} {i : I}
variable {M N : Set (List (TMove (Letter I)))}
variable (hM : ∀ R ∈ M, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R ∧
  StrictReduced₂ (a ++ (ε, i) :: (!ε, i) :: b) R)
variable (hN : ∀ S ∈ N, IsMatching₂ (a ++ b) [] S ∧ StrictReduced₂ (a ++ b) S)
variable (q : {R : List (TMove (Letter I)) | R ∈ M ∧
  Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)} → ℕ → ℕ × ℕ)
variable (r : N → ℕ → ℕ × ℕ)
variable (hq : ∀ R j, j ∈ leftEnds₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val →
  OnStrand₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val j (q R j))
variable (hr : ∀ S j, j ∈ leftEnds₂ (a ++ b) S.val → OnStrand₂ (a ++ b) S.val j (r S j))
variable (τ : ∀ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}), (MatchingStrand (a
        ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) → List (DTMove I))
variable (υ : ∀ S : N, (MatchingStrand (a ++ b) S.val → ℕ) → List (DTMove I))
variable (hτ : ∀ R c, Decorates₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val (q R) (strandCounts c) (τ R
  c))
variable (hυ : ∀ S c, Decorates₂ (a ++ b) S.val (r S) (strandCounts c) (υ S c))

include hM hN hq hr hτ hυ

/-- Cap-class weighted affine fibers and their finite convolution.
Geometry precedes grading, and grading precedes every square-one specialization.
All degree fibers and the cap-count support are constructed, not assumed. -/
theorem cap_labelled_family_coefficients
    (hMrep : ∀ R, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R → StrictReduced₂ (a ++ (ε, i) ::
      (!ε, i) :: b) R →
      ∃ S ∈ M, Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) S) (pairing₂ (a ++ (ε, i) :: (!ε, i) ::
        b) R))
    (hNrep : ∀ R, IsMatching₂ (a ++ b) [] R → StrictReduced₂ (a ++ b) R →
      ∃ S ∈ N, Iso (pairing₂ (a ++ b) S) (pairing₂ (a ++ b) R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) (pairing₂ (a ++ (ε,
      i) :: (!ε, i) :: b) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N,
      Iso (pairing₂ (a ++ b) R) (pairing₂ (a ++ b) S) → R = S) :
    ∃ F : (Σ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}), MatchingStrand (a
        ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) ≃ ℕ × (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ),
      (∀ t, (F t).1 =
        t.2 (capStrand (hM t.1 t.1.property.1).1.pairing_properties.1 t.1.property.2)) ∧
      ∀ (D : Datum I X) (sy : Symmetrizer D) (μ : X),
      let d := fun t : (Σ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}), MatchingStrand (a
        ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) => tableDegree D sy μ (dLay (a ++ (ε, i) :: (!ε, i)
        :: b) (τ t.1 t.2))
      let e := fun u : (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ) => tableDegree D sy μ (dLay (a
        ++ b) (υ u.1 u.2))
      let p := fun t : (Σ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}), MatchingStrand (a
        ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) => xpar D μ (dLay (a ++ (ε, i) :: (!ε, i) :: b) (τ
        t.1 t.2))
      let p' := fun u : (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ) => xpar D μ (dLay (a ++ b) (υ
        u.1 u.2))
      let δ := sy.d i * (1 + if !ε then D.h i (wt D μ b) else -D.h i (wt D μ b))
      ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
        (hg : ∀ z : ℤ, Set.Finite {u : ℕ × (Σ S : N, MatchingStrand (a ++ b) S.val → ℕ) |
          e u.2 + δ + 2 * sy.d i * u.1 = z})
        (he : ∀ z : ℤ, Set.Finite {u | e u = z}),
        (∀ t, d t = e (F t).2 + δ + 2 * sy.d i * (F t).1 ∧
          p t = p' (F t).2 + cupPar D (wt D μ b) (!ε, i) + (F t).1 * D.parity i) ∧
        ∀ (σ : ℚ), σ ^ 2 = 1 → ∀ (z : ℤ),
          (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) =
            σ ^ (cupPar D (wt D μ b) (!ε, i)).val *
              ∑ u ∈ (hg z).toFinset, (σ ^ (D.parity i).val) ^ u.1 * σ ^ (p' u.2).val ∧
          (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) =
            σ ^ (cupPar D (wt D μ b) (!ε, i)).val *
              ∑ n ∈ (hg z).toFinset.image Prod.fst,
                (σ ^ (D.parity i).val) ^ n *
                  ∑ u ∈ (he (z - δ - 2 * sy.d i * n)).toFinset, σ ^ (p' u).val := by
  obtain ⟨F, hcap, hF⟩ := cap_labelled_family_degree_fibres (X := X)
    hM hN q r hq hr τ υ hτ hυ hMrep hNrep hMuniq hNuniq
  refine ⟨F, hcap, ?_⟩
  intro D sy μ
  dsimp only at hF ⊢
  obtain ⟨h, hfin⟩ := hF D sy μ
  let hf := fun z => (hfin z).1
  let hg := fun z => (hfin z).2.1
  have he := mixed_labelled_degree_finite D sy μ (a ++ b) [] N
    (fun S hS => (hN S hS).1) hNuniq r hr υ hυ
  refine ⟨hf, hg, he, h, ?_⟩
  intro σ hσ z
  obtain ⟨G, hG⟩ := (hfin z).2.2
  have hs := fibre_sum_equiv F z (hf z) (hg z) G hG
    (fun t => σ ^ (xpar D μ (dLay (a ++ (ε, i) :: (!ε, i) :: b) (τ t.1 t.2))).val)
    (fun u => σ ^ (cupPar D (wt D μ b) (!ε, i)).val *
      ((σ ^ (D.parity i).val) ^ u.1 *
        σ ^ (xpar D μ (dLay (a ++ b) (υ u.2.1 u.2.2))).val)) (fun t => by
      rw [(h t).2, parity_pow_add σ hσ, parity_pow_add σ hσ, parity_pow_nat_mul σ hσ]
      ring)
  rw [← Finset.mul_sum] at hs
  refine ⟨hs, hs.trans ?_⟩
  congr 1
  exact affine_fibre_convolution _ _ _ _ (hg z) he (σ ^ (D.parity i).val)
    (fun u => σ ^ (xpar D μ (dLay (a ++ b) (υ u.1 u.2))).val)

end Family
end OddMath.SKM
