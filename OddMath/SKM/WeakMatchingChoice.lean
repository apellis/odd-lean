import OddMath.SKM.MatchingChoiceTransition

/-!
# Comparing weakly reduced realizations with strict matching choices

The literal inverse mates needed in BE2's upward-to-oriented reduction need
not satisfy the critical-point condition. Their weak reducedness is enough
for the signed filtered comparison with a strict matching choice.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation StringDiagrams.Chord DTMove
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- A weakly reduced realization of each matching class of `F`, retaining
literal strand points and serializers. Coverage is recorded by the pairing
isomorphism; no strictness of the realized words is required. -/
structure WeakMatchingChoice {a b : List (Letter I)} (F : MatchingBasisChoice a b) where
  representative : F.members → List (TMove (Letter I))
  matching : ∀ R, IsMatching₂ a b (representative R)
  reduced : ∀ R, Reduced₂ a (representative R)
  pairing : ∀ R, Iso (pairing₂ a (representative R)) (pairing₂ a R.val)
  points : (R : F.members) → ℕ → ℕ × ℕ
  onStrand : ∀ R j, j ∈ leftEnds₂ a (representative R) →
    OnStrand₂ a (representative R) j (points R j)
  serialize : (R : F.members) → (MatchingStrand a (representative R) → ℕ) → List (DTMove I)
  decorates : ∀ R n, Decorates₂ a (representative R) (points R) (strandCounts n) (serialize R n)

/-- A strict choice is in particular a weak realization of itself. -/
def MatchingBasisChoice.toWeak {a b : List (Letter I)} (F : MatchingBasisChoice a b) :
    WeakMatchingChoice F where
  representative := Subtype.val
  matching R := (F.matching R.val R.property).1
  reduced R := (F.matching R.val R.property).2.1
  pairing _ := Iso.refl _
  points := F.points
  onStrand := F.onStrand
  serialize := F.serialize
  decorates := F.decorates

namespace WeakMatchingChoice
variable {a b : List (Letter I)} {F : MatchingBasisChoice a b}
  (W : WeakMatchingChoice F) (cs : CScalars Sc) (μ : X)

def counts (t : F.Labels) : MatchingStrand a (W.representative t.1) → ℕ :=
  t.2 ∘ matchingStrandEquivOfIso (W.pairing t.1)

def layers (t : F.Labels) : List (XLayer I) := dLay a (W.serialize t.1 (W.counts t))

theorem layers_chain (t : F.Labels) : XChain a (W.layers t) b := by
  have hR := W.matching t.1
  obtain ⟨hmv, -⟩ := W.decorates t.1 (W.counts t)
  obtain ⟨hfit, -⟩ := matching_bent_spec hR
  obtain ⟨-, hchain, -, -⟩ := shiftD_spec (dualW a) a.length (length_dualW a)
    (W.serialize t.1 (W.counts t)) (tStart_letters a)
    (by rw [tmoves_map_shiftD, hmv]; exact hfit)
  simpa only [hmv, hR.2, layers] using hchain

theorem bendF_layers (t : F.Labels) :
    bendF cs μ a b (xev cs μ a b (W.layers t)) =
      xev cs μ [] (dualW a ++ b) (cupA (dualW a) ++ dLay (dualW a ++ a)
        ((W.serialize t.1 (W.counts t)).map (shiftD a.length))) := by
  have hR := W.matching t.1
  obtain ⟨hmv, -⟩ := W.decorates t.1 (W.counts t)
  obtain ⟨hfit, -⟩ := matching_bent_spec hR
  obtain ⟨hshift, -, -, -⟩ := shiftD_spec (dualW a) a.length (length_dualW a)
    (W.serialize t.1 (W.counts t)) (tStart_letters a)
    (by rw [tmoves_map_shiftD, hmv]; exact hfit)
  rw [bendF_xev cs μ (W.layers_chain t), hshift]
  rfl

/-- Weak syntax has exactly the same signed leading decorated matching and
strictly lower crossing/dot terms in the strict target family. -/
theorem filtered_signRel (t : F.Labels) :
    SignRel ((Finsupp.supported (SYM D k) k
      {u | F.dotBound (ncr₂ t.1.val) (F.openDots t) u}).map (F.expansion cs μ))
      (xev cs μ a b (W.layers t)) (xev cs μ a b (F.layers t)) := by
  let s := pairing₂ a t.1.val
  obtain ⟨hR, hred⟩ := F.matching t.1.val t.1.property
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  have hc : ncr (canon s) = ncr₂ t.1.val :=
    (reduced₂_bent_normal_form cs μ hR hred.1).2.1.symm
  obtain ⟨is, his, hn, hlen⟩ := exists_canonical_strand_dots hv (Iso.refl _) t.2
  let σ : (ℕ → ℕ) → List (DTMove I) := fun n => W.serialize t.1 (fun j => n j.val)
  have hσ (n) : Decorates₂ a (W.representative t.1) (W.points t.1) n (σ n) :=
    (decorates₂_strandCounts_iff _ n _).mp (W.decorates t.1 _)
  have he : σ (fun j => (is.map (lEnd s)).count j) = W.serialize t.1 (W.counts t) := by
    dsimp only [σ]
    congr 1
    funext j
    exact hn (matchingStrandEquivOfIso (W.pairing t.1) j)
  have h1 := F.canonical_filtered_signRel cs μ (ncr₂ t.1.val)
    (W.representative t.1) (W.matching t.1) (W.reduced t.1)
    (W.points t.1) (W.onStrand t.1) σ hσ hv hl hs hc (W.pairing t.1) is his
  rw [he, ← W.bendF_layers cs μ t] at h1
  have h2 := F.label_canonical_filtered_signRel cs μ F t _ hv hl hs hc (Iso.refl _) is his hn
  obtain ⟨p, hp⟩ := h1.symm.trans h2
  rw [hlen] at hp
  simp only [Submodule.mem_comap, map_sub, map_smul,
    bendG_bendF_xev cs μ (W.layers_chain t),
    bendG_bendF_xev cs μ (F.layers_chain t)] at hp
  let pW := pairPar D μ (dualW a) + cupsPar D μ (dualW a) * xpar D μ (W.layers t)
  let pF := pairPar D μ (dualW a) + cupsPar D μ (dualW a) * xpar D μ (F.layers t)
  refine ⟨pW + (p + pF), ?_⟩
  have h := Submodule.smul_mem _ (zsign k pW) hp
  simpa only [MatchingBasisChoice.openDots, pW, pF, smul_sub, smul_smul, zsign_mul_self', one_smul, ← zsign_add] using h


def coefficientMap (t : F.Labels) :
    SYM D k →ₗ[k] ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) where
  toFun p := bubAt D Sc μ a (betaSYM cs μ p) ≫ xev cs μ a b (W.layers t)
  map_add' p q := by simp only [map_add, Preadditive.add_comp]
  map_smul' r p := by simp only [map_smul, Linear.smul_comp, RingHom.id_apply]

def expansion : (F.Labels →₀ SYM D k) →ₗ[k]
    ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Finsupp.lsum k (W.coefficientMap cs μ)

@[simp] theorem expansion_single (t : F.Labels) (p : SYM D k) :
    W.expansion cs μ (Finsupp.single t p) =
      MatchingBasisChoice.rightAction cs μ (xev cs μ a b (W.layers t)) p :=
  Finsupp.lsum_single k (W.coefficientMap cs μ) t p

theorem exists_signed_column (t : F.Labels) :
    ∃ (p : ZMod 2) (r : F.Labels →₀ SYM D k),
      (∀ u ∈ r.support, F.dotBound (ncr₂ t.1.val) (F.openDots t) u) ∧
      xev cs μ a b (W.layers t) = zsign k p • xev cs μ a b (F.layers t) +
        F.expansion cs μ r := by
  obtain ⟨p, r, hr, he⟩ := W.filtered_signRel cs μ t
  refine ⟨p, r, (Finsupp.mem_supported k r).mp hr, ?_⟩
  rw [he]
  abel

def columnData (t : F.Labels) : ZMod 2 × (F.Labels →₀ SYM D k) :=
  let h := W.exists_signed_column cs μ t
  ⟨h.choose, h.choose_spec.choose⟩

theorem columnData_spec (t : F.Labels) :
    (∀ u ∈ (W.columnData cs μ t).2.support, F.dotBound (ncr₂ t.1.val) (F.openDots t) u) ∧
      xev cs μ a b (W.layers t) = zsign k (W.columnData cs μ t).1 •
        xev cs μ a b (F.layers t) + F.expansion cs μ (W.columnData cs μ t).2 :=
  (W.exists_signed_column cs μ t).choose_spec.choose_spec

def unitColumn (t : F.Labels) : F.Labels →₀ SYM D k :=
  zsign k (W.columnData cs μ t).1 • Finsupp.single t 1 + (W.columnData cs μ t).2

theorem unitColumn_eval (t : F.Labels) :
    F.expansion cs μ (W.unitColumn cs μ t) = xev cs μ a b (W.layers t) := by
  rw [unitColumn, map_add, map_smul, F.expansion_single]
  change zsign k (W.columnData cs μ t).1 •
    MatchingBasisChoice.rightAction cs μ (xev cs μ a b (F.layers t)) 1 + _ = _
  rw [MatchingBasisChoice.rightAction_one]
  exact (W.columnData_spec cs μ t).2.symm

theorem columnData_diagonal (t : F.Labels) : (W.columnData cs μ t).2 t = 0 := by
  by_contra h
  have hlt := (W.columnData_spec cs μ t).1 _ (Finsupp.mem_support_iff.mpr h)
  simp only [MatchingBasisChoice.dotBound, lt_self_iff_false, true_and, or_self] at hlt

theorem unitColumn_diagonal (t : F.Labels) :
    W.unitColumn cs μ t t = zsign k (W.columnData cs μ t).1 • 1 := by
  classical
  simp [unitColumn, W.columnData_diagonal cs μ t]

theorem unitColumn_lower (i j : F.Labels) (hij : i ≠ j)
    (h : W.unitColumn cs μ j i ≠ 0) :
    ncr₂ i.1.val < ncr₂ j.1.val ∨
      (ncr₂ i.1.val = ncr₂ j.1.val ∧ F.openDots i < F.openDots j) := by
  classical
  have hr : (W.columnData cs μ j).2 i ≠ 0 := by
    simpa only [unitColumn, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne hij, smul_zero, zero_add] using h
  exact (W.columnData_spec cs μ j).1 _ (Finsupp.mem_support_iff.mpr hr)

def transition : (F.Labels →₀ SYM D k) →ₗ[k] (F.Labels →₀ SYM D k) :=
  MatchingTransition.transition (k := k) (W.unitColumn cs μ)


theorem transition_injective : Function.Injective (W.transition cs μ) := by
  apply MatchingTransition.transition_injective (Equiv.refl F.Labels)
    (fun t => ncr₂ t.1.val) F.openDots (W.unitColumn cs μ) (W.unitColumn_lower cs μ)
  intro i p hp
  rw [Equiv.refl_apply, W.unitColumn_diagonal cs μ i, smul_mul_assoc, one_mul] at hp
  have h := congrArg (fun q : SYM D k => zsign k (W.columnData cs μ i).1 • q) hp
  simpa only [smul_smul, zsign_mul_self', one_smul, smul_zero] using h

theorem transition_surjective : Function.Surjective (W.transition cs μ) := by
  apply MatchingTransition.transition_surjective (Equiv.refl F.Labels)
    (fun i j => ncr₂ i.1.val < ncr₂ j.1.val ∨
      (ncr₂ i.1.val = ncr₂ j.1.val ∧ F.openDots i < F.openDots j))
    (MatchingTransition.crossingDot_wellFounded (fun t => ncr₂ t.1.val) F.openDots)
    (W.unitColumn cs μ) (fun i => zsign k (W.columnData cs μ i).1 • 1)
    (W.unitColumn_lower cs μ)
  intro i
  simp only [Equiv.refl_apply, W.unitColumn_diagonal cs μ i, smul_mul_assoc, one_mul,
    smul_smul, zsign_mul_self', one_smul]

theorem transition_evaluation (v : F.Labels →₀ SYM D k) :
    F.expansion cs μ (W.transition cs μ v) = W.expansion cs μ v := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single i p =>
    change F.expansion cs μ (MatchingTransition.transition (W.unitColumn cs μ)
      (Finsupp.single i p)) = _
    rw [MatchingTransition.transition_single, F.expansion_rightColumn,
      W.unitColumn_eval cs μ i, W.expansion_single]


/-- A strict independent family also detects every complete weak realization. -/
theorem expansion_injective_of_strict (hF : Function.Injective (F.expansion cs μ)) :
    Function.Injective (W.expansion cs μ) := by
  intro v w h
  apply W.transition_injective cs μ
  apply hF
  simpa only [W.transition_evaluation cs μ] using h

/-- Independence of a complete weak realization implies independence of the
strict family. Surjectivity of the finite triangular transition is essential
here; no strictness of the weak realization is used. -/
theorem strict_expansion_injective (hW : Function.Injective (W.expansion cs μ)) :
    Function.Injective (F.expansion cs μ) := by
  intro v w h
  obtain ⟨v', rfl⟩ := W.transition_surjective cs μ v
  obtain ⟨w', rfl⟩ := W.transition_surjective cs μ w
  exact congrArg (W.transition cs μ) (hW (by
    simpa only [W.transition_evaluation cs μ] using h))

end WeakMatchingChoice
end OddMath.SKM
