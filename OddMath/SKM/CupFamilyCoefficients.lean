import OddMath.SKM.DecoratedNormalization
import OddMath.SKM.MixedFibres
import OddMath.SKM.MatchingBending

/-! # Strand-labelled right-cup coefficient transport

The graphical right-cup step of BE2, arXiv:1701.04133v2, Theorem 10.3,
Claim 2. Representative families have coverage and uniqueness. Points and
serializers are fixed before the datum, sign and degree. The coefficient
headline proves both degree fibers finite from matching, uniqueness and positive
dot weights. It is the graphical step, not the algebraic comparison of Claim 2.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
variable {I X : Type*} [AddCommGroup X]

/-- Lift an endpoint-preserving representative equivalence by precomposition
on the existing strand-label functions. No matching or morphism quotient is used. -/
def strandLabelledEquiv {A B : List (Letter I)}
    {M N : Set (List (TMove (Letter I)))}
    (E : {R // R ∈ M} ≃ {S // S ∈ N})
    (hE : ∀ R, Iso (pairing₂ A R.val) (pairing₂ B (E R).val)) :
    (Σ R : {R // R ∈ M}, MatchingStrand A R.val → ℕ) ≃
      (Σ S : {S // S ∈ N}, MatchingStrand B S.val → ℕ) :=
  Equiv.sigmaCongr E (fun R =>
    Equiv.arrowCongr (matchingStrandEquivOfIso (hE R)) (Equiv.refl ℕ))

@[simp] theorem strandLabelledEquiv_apply {A B : List (Letter I)}
    {M N : Set (List (TMove (Letter I)))}
    (E : {R // R ∈ M} ≃ {S // S ∈ N})
    (hE : ∀ R, Iso (pairing₂ A R.val) (pairing₂ B (E R).val))
    (R : {R // R ∈ M}) (c : MatchingStrand A R.val → ℕ) :
    strandLabelledEquiv E hE ⟨R, c⟩ =
      ⟨E R, c ∘ (matchingStrandEquivOfIso (hE R)).symm⟩ := rfl

/-- Restrict a shifted equivalence to its degree fibers. -/
def degreeShiftFiberEquiv {T U : Type*} (F : T ≃ U)
    (d : T → ℤ) (e : U → ℤ) (δ : ℤ) (hd : ∀ t, e (F t) = d t + δ) (z : ℤ) :
    {t // d t = z - δ} ≃ {u // e u = z} :=
  F.subtypeEquiv (fun t => by rw [hd]; omega)

/-- Finite weighted sums transport across a degree shift. This assumes one
finite fiber only; it does not assert finiteness for a family of diagrams. -/
theorem degreeShift_finite_sum {T U k : Type*} [AddCommMonoid k]
    (F : T ≃ U) (d : T → ℤ) (e : U → ℤ) (v : T → k) (w : U → k)
    (δ : ℤ) (hd : ∀ t, e (F t) = d t + δ) (hv : ∀ t, w (F t) = v t)
    (z : ℤ) (hf : Set.Finite {t | d t = z - δ}) :
    ∃ hg : Set.Finite {u | e u = z},
      (∑ u ∈ hg.toFinset, w u) = ∑ t ∈ hf.toFinset, v t := by
  classical
  have hg : Set.Finite {u | e u = z} := by
    have h := hf.image F
    apply h.subset
    intro u hu
    refine ⟨F.symm u, ?_, F.apply_symm_apply u⟩
    have := hd (F.symm u)
    simp only [Equiv.apply_symm_apply] at this
    change e u = z at hu
    change d (F.symm u) = z - δ
    omega
  refine ⟨hg, Eq.symm ?_⟩
  apply Finset.sum_bij (fun t _ => F t)
  · intro t ht
    apply hg.mem_toFinset.mpr
    have := hf.mem_toFinset.mp ht
    change d t = z - δ at this
    change e (F t) = z
    rw [hd, this]
    omega
  · intro t _ u _ h
    exact F.injective h
  · intro u hu
    refine ⟨F.symm u, hf.mem_toFinset.mpr ?_, F.apply_symm_apply u⟩
    have := hd (F.symm u)
    simp only [Equiv.apply_symm_apply] at this
    have hu' : e u = z := hg.mem_toFinset.mp hu
    change d (F.symm u) = z - δ
    omega
  · intro t _
    exact (hv t).symm

section RightCup
variable {i : I} {a b : List (Letter I)}
variable {M N : Set (List (TMove (Letter I)))}
variable (hM : ∀ R ∈ M, IsMatching₂ ((true, i) :: a) b R ∧ StrictReduced₂ ((true, i) :: a) R)
variable (hN : ∀ S ∈ N, IsMatching₂ a ((false, i) :: b) S ∧ StrictReduced₂ a S)
variable (q : {R // R ∈ M} → ℕ → ℕ × ℕ)
variable (r : {S // S ∈ N} → ℕ → ℕ × ℕ)
variable (hq : ∀ R j, j ∈ leftEnds₂ ((true, i) :: a) R.val →
  (q R j).1 ≤ R.val.length ∧ OnStrand₂ ((true, i) :: a) R.val j (q R j))
variable (hr : ∀ S j, j ∈ leftEnds₂ a S.val → OnStrand₂ a S.val j (r S j))
variable (τ : ∀ R : {R // R ∈ M}, (MatchingStrand ((true, i) :: a) R.val → ℕ) → List (DTMove I))
variable (υ : ∀ S : {S // S ∈ N}, (MatchingStrand a S.val → ℕ) → List (DTMove I))
variable (hτ : ∀ R c, Decorates₂ ((true, i) :: a) R.val (q R) (strandCounts c) (τ R c))
variable (hυ : ∀ S c, Decorates₂ a S.val (r S) (strandCounts c) (υ S c))

include hM hN hq hr hτ hυ

/-- The lifted representative bijection has the degree and parity dictated by
the literal generator table, for independently fixed valid serializations. -/
theorem rightCup_labelled_degree_parity
    (E : {R // R ∈ M} ≃ {S // S ∈ N})
    (hE : ∀ R, Iso (pairing₂ ((true, i) :: a) R.val) (pairing₂ a (E R).val))
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (t : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ)) :
    let u := strandLabelledEquiv E hE t
    tableDegree D sy μ (dLay a (υ u.1 u.2)) =
      tableDegree D sy μ (dLay ((true, i) :: a) (τ t.1 t.2)) + sy.d i * (1 + D.h i (wt D μ a)) ∧
    xpar D μ (dLay a (υ u.1 u.2)) = xpar D μ (dLay ((true, i) :: a) (τ t.1 t.2)) := by
  rcases t with ⟨R, c⟩
  exact cupAttach_normalized_decorated_degree_parity D sy μ
    (hM R R.property).1 (hM R R.property).2.1
    (hN (E R) (E R).property).1 (hN (E R) (E R).property).2.1 (hE R)
    (q R) (r (E R)) (hq R) (hr (E R)) c _ _ (hτ R c) (hυ _ _)

/-- The source representative-family construction, including coverage and
uniqueness, lifts to all natural strand labels. The equivalence is selected
before all gradings and signs. Degree fibers and their weighted sums shift
by the numerical right-cup degree. Finiteness of the source fiber remains an
explicit intermediate premise, and no algebraic form identity is claimed. -/
theorem rightCup_labelled_family_transport
    (hMrep : ∀ R, IsMatching₂ ((true, i) :: a) b R → StrictReduced₂ ((true, i) :: a) R →
      ∃ S ∈ M, Iso (pairing₂ ((true, i) :: a) S) (pairing₂ ((true, i) :: a) R))
    (hNrep : ∀ R, IsMatching₂ a ((false, i) :: b) R → StrictReduced₂ a R →
      ∃ S ∈ N, Iso (pairing₂ a S) (pairing₂ a R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ ((true, i) :: a) R) (pairing₂ ((true, i) :: a) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N, Iso (pairing₂ a R) (pairing₂ a S) → R = S) :
    ∃ F : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ) ≃ (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ), ∀ (D : Datum I X) (sy : Symmetrizer D) (μ : X),
      let d := fun t : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ) => tableDegree D sy μ (dLay ((true, i) :: a) (τ t.1 t.2))
      let e := fun u : (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ) => tableDegree D sy μ (dLay a (υ u.1 u.2))
      let p := fun t : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ) => xpar D μ (dLay ((true, i) :: a) (τ t.1 t.2))
      let p' := fun u : (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ) => xpar D μ (dLay a (υ u.1 u.2))
      let δ := sy.d i * (1 + D.h i (wt D μ a))
      (∀ t, e (F t) = d t + δ ∧ p' (F t) = p t) ∧
      (∀ z, Nonempty ({t // d t = z - δ} ≃ {u // e u = z})) ∧
      ∀ (σ : ℚ) (z : ℤ) (hf : Set.Finite {t | d t = z - δ}),
        ∃ hg : Set.Finite {u | e u = z},
          (∑ u ∈ hg.toFinset, σ ^ (p' u).val) = ∑ t ∈ hf.toFinset, σ ^ (p t).val := by
  obtain ⟨E, hE⟩ := bending_representatives_equiv (true, i) a b M N
    hM hN hMrep hNrep hMuniq hNuniq
  let hE' := fun R => (hE R).symm
  refine ⟨strandLabelledEquiv E hE', ?_⟩
  intro D sy μ
  dsimp only
  have h := rightCup_labelled_degree_parity hM hN q r hq hr τ υ hτ hυ E hE' D sy μ
  refine ⟨h, ?_, ?_⟩
  · intro z
    exact ⟨degreeShiftFiberEquiv _ _ _ _ (fun t => (h t).1) z⟩
  · intro σ z hf
    exact degreeShift_finite_sum _ _ _ _ _ _ (fun t => (h t).1)
      (fun t => congrArg (fun p : ZMod 2 => σ ^ p.val) (h t).2) z hf

/-- Right-cup transport of the graphical coefficients in BE2 Theorem 10.3,
Claim 2. Both degree fibers are finite by geometric uniqueness and positive dot
weights, not by a finiteness premise. The strand-labelled equivalence is chosen
before every datum, weight, degree and rational parity specialization. Source and
target points and serializers are independent. This does not assert the algebraic
form identity or its coefficientwise equivalence. -/
theorem rightCup_labelled_family_coefficients
    (hMrep : ∀ R, IsMatching₂ ((true, i) :: a) b R → StrictReduced₂ ((true, i) :: a) R →
      ∃ S ∈ M, Iso (pairing₂ ((true, i) :: a) S) (pairing₂ ((true, i) :: a) R))
    (hNrep : ∀ R, IsMatching₂ a ((false, i) :: b) R → StrictReduced₂ a R →
      ∃ S ∈ N, Iso (pairing₂ a S) (pairing₂ a R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ ((true, i) :: a) R) (pairing₂ ((true, i) :: a) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N, Iso (pairing₂ a R) (pairing₂ a S) → R = S) :
    ∃ F : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ) ≃
        (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ),
      ∀ (D : Datum I X) (sy : Symmetrizer D) (μ : X),
      let d := fun t : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ) =>
        tableDegree D sy μ (dLay ((true, i) :: a) (τ t.1 t.2))
      let e := fun u : (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ) =>
        tableDegree D sy μ (dLay a (υ u.1 u.2))
      let p := fun t : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ) =>
        xpar D μ (dLay ((true, i) :: a) (τ t.1 t.2))
      let p' := fun u : (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ) =>
        xpar D μ (dLay a (υ u.1 u.2))
      let δ := sy.d i * (1 + D.h i (wt D μ a))
      ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
        (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
        (∀ t, e (F t) = d t + δ ∧ p' (F t) = p t) ∧
        (∀ z, Nonempty ({t // d t = z - δ} ≃ {u // e u = z})) ∧
        ∀ (σ : ℚ) (z : ℤ),
          (∑ u ∈ (hg z).toFinset, σ ^ (p' u).val) =
            ∑ t ∈ (hf (z - δ)).toFinset, σ ^ (p t).val := by
  obtain ⟨F, hF⟩ := rightCup_labelled_family_transport (X := X) hM hN q r hq hr τ υ hτ hυ
    hMrep hNrep hMuniq hNuniq
  refine ⟨F, ?_⟩
  intro D sy μ
  dsimp only
  have hf := mixed_labelled_degree_finite D sy μ ((true, i) :: a) b M
    (fun R hR => (hM R hR).1) hMuniq q (fun R j hj => (hq R j hj).2) τ hτ
  have hg := mixed_labelled_degree_finite D sy μ a ((false, i) :: b) N
    (fun S hS => (hN S hS).1) hNuniq r hr υ hυ
  refine ⟨hf, hg, (hF D sy μ).1, (hF D sy μ).2.1, ?_⟩
  intro σ z
  obtain ⟨_, heq⟩ := (hF D sy μ).2.2 σ z (hf _)
  exact heq

end RightCup
end OddMath.SKM
