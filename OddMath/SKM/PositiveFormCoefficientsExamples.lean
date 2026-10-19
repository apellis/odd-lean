import OddMath.SKM.PositiveFormCoefficients
import OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples

/-! Non-vacuity checks for the positive modified-form coefficient comparison.
The existing one-odd-root datum supplies both empty words and a repeated-colour
canonical family with crossing degree -2, at each of the two π signs. -/

noncomputable section
namespace OddMath.SKM.PositiveFormCoefficientsExamples
open CoveringQuantum StringDiagrams StringDiagrams.Chord
open PositiveDecoratedFamilyCoefficientsExamples
open scoped BigOperators

/-- The one-odd-root datum satisfies the form's bar-consistency hypothesis. -/
theorem odd_barConsistent : oddDatum.toSuperCartanDatum.BarConsistent := fun _ => rfl

/-- The existing modified form on a repeated odd word, expanded after evaluation. -/
def repeatedForm (σ : ℚ) (hσ : σ ^ 2 = 1) (n : ℕ) : LaurentSeries ℚ :=
  signLaurent σ hσ (UDot.GenericTensor.sesquilinearForm oddDatum odd_barConsistent
    (UDot.positiveHalf oddDatum Coefficients.q Coefficients.pi 0
      (oddDatum.toSerreF Coefficients.q Coefficients.pi
        (PreF.monomial Coefficients.Ring (List.ofFn (fun _ : Fin n => ())).reverse)))
    (UDot.positiveHalf oddDatum Coefficients.q Coefficients.pi 0
      (oddDatum.toSerreF Coefficients.q Coefficients.pi
        (PreF.monomial Coefficients.Ring (List.ofFn (fun _ : Fin n => ())).reverse))))

/-- The empty-word value has only its degree-zero coefficient. -/
theorem empty_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (repeatedForm σ hσ 0).coeff z = if z = 0 then 1 else 0 := by
  rw [repeatedForm, UDot.GenericTensor.sesquilinearForm_positive_words_coeff]
  simp only [Fin.forall_fin_zero, ite_true, Fintype.sum_unique, Finset.univ_eq_empty,
    Finset.sum_empty, sub_zero, SuperCartanDatum.dotSeries_empty, PowerSeries.coeff_one,
    ZMod.val_zero, pow_zero, one_mul]
  by_cases hz : z = 0
  · subst z
    simp
  · by_cases hn : 0 ≤ z
    · have hp : ¬z ≤ 0 := by omega
      simp [hz, hn, hp]
    · simp [hz, hn]

private theorem perm_two (e : Equiv.Perm (Fin 2)) :
    e = Equiv.refl _ ∨ e = Equiv.swap 0 1 := by
  have hn : e 0 ≠ e 1 := fun h => Fin.zero_ne_one (e.injective h)
  generalize h0 : e 0 = x
  generalize h1 : e 1 = y
  fin_cases x <;> fin_cases y
  · exact False.elim (hn (h0.trans h1.symm))
  · left
    ext r
    fin_cases r <;> simp [h0, h1]
  · right
    ext r
    fin_cases r <;> simp [h0, h1]
  · exact False.elim (hn (h0.trans h1.symm))

/-- The odd transposition is the sole contribution at its negative crossing degree. -/
theorem repeated_negative_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) :
    (repeatedForm σ hσ 2).coeff (-2) = σ ∧
      (repeatedForm σ hσ 2).coeff (-3) = 0 := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {Equiv.refl _, Equiv.swap 0 1} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact perm_two w
  have h (z : ℤ) := UDot.GenericTensor.sesquilinearForm_positive_words_coeff
    oddDatum odd_barConsistent σ hσ 0 2 (fun _ => ()) (fun _ => ()) z
  change ∀ z, (repeatedForm σ hσ 2).coeff z = _ at h
  simp only [hu, Finset.sum_pair (by decide : (Equiv.refl (Fin 2)) ≠ Equiv.swap 0 1),
    Finset.sum_filter, Fin.sum_univ_two] at h
  have hmin := h (-2)
  have hbelow := h (-3)
  norm_num [oddDatum, SuperCartanDatum.dot] at hmin hbelow
  have hconst : PowerSeries.coeff 0
      (oddDatum.toSuperCartanDatum.dotSeries σ (fun _ : Fin 2 => ())) = 1 := by
    simp [SuperCartanDatum.dotSeries, PreF.DotSeries.strands, Fin.prod_univ_two,
      PowerSeries.coeff_mul, PreF.DotSeries.coeff_factor, oddDatum]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff] at hmin
  change (repeatedForm σ hσ 2).coeff (-2) = σ ^ (1 : ZMod 2).val *
    PowerSeries.coeff 0 (oddDatum.toSuperCartanDatum.dotSeries σ (fun _ : Fin 2 => ())) at hmin
  rw [hconst] at hmin
  simpa only [show (1 : ZMod 2).val = 1 from rfl, pow_one, mul_one] using And.intro hmin hbelow

/-- The negative crossing coefficient is realized by a finite fiber of the existing
canonical family, with all representative and root-datum hypotheses discharged. -/
theorem repeated_family (σ : ℚ) (hσ : σ ^ 2 = 1) :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ repeatedWord repeatedFamily
         (fun R c => topDotMoves repeatedWord R
           (topPositionExtension repeatedFamily p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain repeatedWord (L D) repeatedWord),
         (∀ D, (L D).map ofL = D.val) ∧
         ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = -2},
           (∑ D ∈ hf.toFinset, σ ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm σ hσ 2).coeff (-2) ∧
           (∑ D ∈ hf.toFinset, σ ^ (xpar oddDatum.toSKM 0 D.val).val) = σ) := by
  obtain ⟨p, hp, L, hL, hm, h⟩ := positive_decorated_family_form_coeff oddDatum
    odd_barConsistent 0 σ hσ (fun _ : Fin 2 => ()) (fun _ => ())
    repeatedFamily family_matching family_coverage family_unique
  obtain ⟨hf, hc⟩ := h (-2)
  exact ⟨p, hp, L, hL, hm, hf, hc, hc.trans (repeated_negative_coeff σ hσ).1⟩


/-- The empty canonical family realizes the empty modified-form coefficient. -/
theorem empty_family (σ : ℚ) (hσ : σ ^ 2 = 1) :
    ∃ p : ∀ R : {R : List (TMove (Letter Unit)) // R ∈ ({[]} : Set _)},
        MatchingStrand [] R.val ≃ Fin 0,
      (∀ R (j : MatchingStrand [] R.val),
        OnStrand₂ [] R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ [] ({[]} : Set _)
         (fun R c => topDotMoves [] R (topPositionExtension {[]} p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain [] (L D) []),
         (∀ D, (L D).map ofL = D.val) ∧
         ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = z},
           (∑ D ∈ hf.toFinset, σ ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm σ hσ 0).coeff z ∧
           (∑ D ∈ hf.toFinset, σ ^ (xpar oddDatum.toSKM 0 D.val).val) =
             if z = 0 then 1 else 0) := by
  let a : Fin 0 → Unit := Fin.elim0
  have hm : IsMatching₂ [] ([] : List (Letter Unit)) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ ([] : List (Letter Unit)) [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  obtain ⟨p, hp, L, hL, hmap, h⟩ := positive_decorated_family_form_coeff oddDatum
    odd_barConsistent 0 σ hσ a a {[]}
    (by intro R hR; obtain rfl := Set.mem_singleton_iff.mp hR; exact ⟨hm, hr⟩)
    (by
      intro R hR _
      refine ⟨[], Set.mem_singleton _, ?_⟩
      have hs := hR.pairing_properties.2.2
      have he : pairing₂ [] R = [] := by simpa using hs
      change Iso [] (pairing₂ [] R)
      rw [he]
      exact Iso.refl _)
    (by
      intro R hR S hS _
      exact (Set.mem_singleton_iff.mp hR).trans (Set.mem_singleton_iff.mp hS).symm)
  refine ⟨p, hp, L, hL, hmap, ?_⟩
  intro z
  obtain ⟨hf, hc⟩ := h z
  have he : a = fun _ : Fin 0 => () := funext fun r => Fin.elim0 r
  rw [he] at hc
  exact ⟨hf, hc, hc.trans (empty_coeff σ hσ z)⟩

example (z : ℤ) : (repeatedForm 1 (by norm_num) 0).coeff z = if z = 0 then 1 else 0 :=
  empty_coeff 1 (by norm_num) z
example (z : ℤ) : (repeatedForm (-1) (by norm_num) 0).coeff z = if z = 0 then 1 else 0 :=
  empty_coeff (-1) (by norm_num) z
example : (repeatedForm 1 (by norm_num) 2).coeff (-2) = 1 ∧
    (repeatedForm 1 (by norm_num) 2).coeff (-3) = 0 := repeated_negative_coeff 1 (by norm_num)
example : (repeatedForm (-1) (by norm_num) 2).coeff (-2) = -1 ∧
    (repeatedForm (-1) (by norm_num) 2).coeff (-3) = 0 := repeated_negative_coeff (-1) (by norm_num)

example :
    ∃ p : ∀ R : {R : List (TMove (Letter Unit)) // R ∈ ({[]} : Set _)},
        MatchingStrand [] R.val ≃ Fin 0,
      (∀ R (j : MatchingStrand [] R.val),
        OnStrand₂ [] R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ [] ({[]} : Set _)
         (fun R c => topDotMoves [] R (topPositionExtension {[]} p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain [] (L D) []),
         (∀ D, (L D).map ofL = D.val) ∧
         ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = z},
           (∑ D ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm 1 (by norm_num) 0).coeff z ∧
           (∑ D ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             if z = 0 then 1 else 0) :=
  empty_family 1 (by norm_num)

example :
    ∃ p : ∀ R : {R : List (TMove (Letter Unit)) // R ∈ ({[]} : Set _)},
        MatchingStrand [] R.val ≃ Fin 0,
      (∀ R (j : MatchingStrand [] R.val),
        OnStrand₂ [] R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ [] ({[]} : Set _)
         (fun R c => topDotMoves [] R (topPositionExtension {[]} p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain [] (L D) []),
         (∀ D, (L D).map ofL = D.val) ∧
         ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = z},
           (∑ D ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm (-1) (by norm_num) 0).coeff z ∧
           (∑ D ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             if z = 0 then 1 else 0) :=
  empty_family (-1) (by norm_num)

example :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ repeatedWord repeatedFamily
         (fun R c => topDotMoves repeatedWord R
           (topPositionExtension repeatedFamily p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain repeatedWord (L D) repeatedWord),
         (∀ D, (L D).map ofL = D.val) ∧
         ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = -2},
           (∑ D ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm 1 (by norm_num) 2).coeff (-2) ∧
           (∑ D ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) = 1) :=
  repeated_family 1 (by norm_num)

example :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ repeatedWord repeatedFamily
         (fun R c => topDotMoves repeatedWord R
           (topPositionExtension repeatedFamily p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain repeatedWord (L D) repeatedWord),
         (∀ D, (L D).map ofL = D.val) ∧
         ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = -2},
           (∑ D ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (repeatedForm (-1) (by norm_num) 2).coeff (-2) ∧
           (∑ D ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0 D.val).val) = (-1)) :=
  repeated_family (-1) (by norm_num)

end OddMath.SKM.PositiveFormCoefficientsExamples
