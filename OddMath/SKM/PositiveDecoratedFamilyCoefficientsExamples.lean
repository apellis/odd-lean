import OddMath.SKM.PositiveDecoratedFamilyCoefficients

/-! Concrete canonical-family coefficients supporting [BE2, arXiv:1701.04133v2,
Theorem 10.3, proof of Claim 1]. Both repeated-colour representatives contribute;
all matching, coverage, uniqueness and root-datum hypotheses are proved. -/

noncomputable section
namespace OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open CoveringQuantum StringDiagrams StringDiagrams.Chord
open scoped BigOperators

/-- One odd simple root, with Cartan entry two and symmetrizer one. -/
def oddDatum : RootDatum Unit ℤ where
  a := Matrix.of fun _ _ => 2
  isGCM :=
    { diag := fun _ => rfl
      offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ => Iff.rfl }
  d := fun _ => 1
  d_pos := fun _ => one_pos
  d_mul_symm := fun _ _ => rfl
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two
  cd :=
    { root := fun _ => 2
      coroot := fun _ => LinearMap.id
      coroot_root_self := fun _ => rfl }
  coroot_root _ _ := rfl

abbrev repeatedWord : List (Letter Unit) := [(true, ()), (true, ())]
abbrev repeatedFamily : Set (List (TMove (Letter Unit))) := {[], [.mv (.cross 0)]}

private theorem identity_matching : IsMatching₂ repeatedWord repeatedWord [] := ⟨trivial, rfl⟩
private theorem identity_reduced : StrictReduced₂ repeatedWord [] :=
  ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩

private theorem swap_matching :
    IsMatching₂ repeatedWord repeatedWord [.mv (.cross 0)] := by
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

private theorem swap_reduced : StrictReduced₂ repeatedWord [.mv (.cross 0)] := by
  refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
  intro z hz
  change z ∈ [_] at hz
  obtain rfl := List.mem_singleton.mp hz
  change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
  decide

theorem family_matching : ∀ R ∈ repeatedFamily,
    IsMatching₂ repeatedWord repeatedWord R ∧ StrictReduced₂ repeatedWord R := by
  intro R hR
  rcases hR with rfl | hR
  · exact ⟨identity_matching, identity_reduced⟩
  · obtain rfl := Set.mem_singleton_iff.mp hR
    exact ⟨swap_matching, swap_reduced⟩

private theorem identity_pairs : ∀ r : Fin 2, Same (pairing₂ repeatedWord [])
    (2 - 1 - r.val) (2 + r.val) := by
  intro r
  fin_cases r <;> unfold Same <;> decide

private theorem swap_pairs : ∀ r : Fin 2,
    Same (pairing₂ repeatedWord [.mv (.cross 0)])
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
  intro r
  fin_cases r <;> unfold Same <;> decide

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

private theorem iso_of_positive_pairs {I : Type*} {n : ℕ} (a b : Fin n → I)
    {s t : List (ℕ × Letter I)} (hv : Valid s) (hv' : Valid t)
    (hs : s.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun r => (true, b r))
    (ht : t.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun r => (true, b r)) (e : Equiv.Perm (Fin n))
    (he : ∀ r, Same s (n - 1 - r.val) (n + (e r).val))
    (he' : ∀ r, Same t (n - 1 - r.val) (n + (e r).val)) : Iso s t := by
  have hlen : s.length = n + n := by
    have h := congrArg List.length hs
    simpa [length_dualW] using h
  have hlen' : t.length = n + n := by
    have h := congrArg List.length ht
    simpa [length_dualW] using h
  have partners (i : ℕ) (hi : i < n + n) : ∃ j, Same s i j ∧ Same t i j := by
    by_cases hin : i < n
    · let r : Fin n := ⟨n - 1 - i, by omega⟩
      have hr : n - 1 - r.val = i := by dsimp [r]; omega
      exact ⟨n + (e r).val, hr ▸ he r, hr ▸ he' r⟩
    · let r : Fin n := ⟨i - n, by omega⟩
      have hr : n + r.val = i := by dsimp [r]; omega
      refine ⟨n - 1 - (e.symm r).val, ?_, ?_⟩
      · simpa only [e.apply_symm_apply, hr] using (he (e.symm r)).symm
      · simpa only [e.apply_symm_apply, hr] using (he' (e.symm r)).symm
  refine ⟨hs.trans ht.symm, fun i j => ?_⟩
  constructor
  · intro h
    obtain ⟨k, hk, hk'⟩ := partners i (by simpa [hlen] using h.lt_left)
    exact (hv.unique hk h) ▸ hk'
  · intro h
    obtain ⟨k, hk, hk'⟩ := partners i (by simpa [hlen'] using h.lt_left)
    exact (hv'.unique hk' h) ▸ hk

theorem family_coverage : ∀ R', IsMatching₂ repeatedWord repeatedWord R' →
    StrictReduced₂ repeatedWord R' →
    ∃ R ∈ repeatedFamily, Iso (pairing₂ repeatedWord R) (pairing₂ repeatedWord R') := by
  intro R' hR' _
  obtain ⟨hv, hl, hs⟩ := hR'.pairing_properties
  obtain ⟨e, he, _⟩ := positive_pairing_equiv (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) hv hl hs
  rcases perm_two e with rfl | rfl
  · refine ⟨[], by simp [repeatedFamily], ?_⟩
    exact iso_of_positive_pairs (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ())
      identity_matching.pairing_properties.1 hv identity_matching.pairing_properties.2.2 hs
      (Equiv.refl _) identity_pairs he.2
  · refine ⟨[.mv (.cross 0)], by simp [repeatedFamily], ?_⟩
    exact iso_of_positive_pairs (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ())
      swap_matching.pairing_properties.1 hv swap_matching.pairing_properties.2.2 hs
      (Equiv.swap 0 1) swap_pairs he.2

private theorem identity_not_iso_swap :
    ¬ Iso (pairing₂ repeatedWord []) (pairing₂ repeatedWord [.mv (.cross 0)]) := by
  intro h
  have hp := (h.2 1 2).1 (identity_pairs 0)
  have hn : ¬ Same (pairing₂ repeatedWord [.mv (.cross 0)]) 1 2 := by unfold Same; decide
  exact hn hp

theorem family_unique : ∀ R ∈ repeatedFamily, ∀ S ∈ repeatedFamily,
    Iso (pairing₂ repeatedWord R) (pairing₂ repeatedWord S) → R = S := by
  intro R hR S hS h
  have hr : R = [] ∨ R = [.mv (.cross 0)] := by simpa [repeatedFamily] using hR
  have hs : S = [] ∨ S = [.mv (.cross 0)] := by simpa [repeatedFamily] using hS
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · rfl
  · exact False.elim (identity_not_iso_swap h)
  · exact False.elim (identity_not_iso_swap h.symm)
  · rfl


private abbrev word : Fin 2 → Unit := fun _ => ()

/-- The identity contribution and the odd crossing of degree -2, in one family. -/
theorem repeated_coeff :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ repeatedWord repeatedFamily
         (fun R c => topDotMoves repeatedWord R
           (topPositionExtension repeatedFamily p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain repeatedWord (L D) repeatedWord),
         (∀ D, (L D).map ofL = D.val) ∧
         ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = z},
           (∑ D ∈ hf.toFinset, (-1 : ℤ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (if 0 ≤ z then PowerSeries.coeff z.toNat
               (oddDatum.toSuperCartanDatum.dotSeries (-1 : ℤ) word) else 0) -
             (if -2 ≤ z then PowerSeries.coeff (z + 2).toNat
               (oddDatum.toSuperCartanDatum.dotSeries (-1 : ℤ) word) else 0)) := by
  obtain ⟨p, hp, L, hL, hm, h⟩ := positive_decorated_family_coeff oddDatum 0 (-1 : ℤ)
    (by norm_num) word word repeatedFamily family_matching family_coverage family_unique
  refine ⟨p, hp, L, hL, hm, ?_⟩
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {Equiv.refl _, Equiv.swap 0 1} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact perm_two w
  intro z
  obtain ⟨hf, hc⟩ := h z
  refine ⟨hf, hc.trans ?_⟩
  rw [hu, Finset.sum_pair (by decide)]
  simp only [Finset.sum_filter, Fin.sum_univ_two]
  norm_num [word, oddDatum, SuperCartanDatum.dot]
  have hv : (1 : ZMod 2).val = 1 := rfl
  simp only [hv, pow_one, neg_one_mul]
  split_ifs <;> simp [sub_eq_add_neg]

/-- Degree -3 is below every shift; degrees 0 and 4 receive both matching contributions. -/
theorem repeated_coeff_values :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      (let G := {D // D ∈ decoratedFamily₂ repeatedWord repeatedFamily
         (fun R c => topDotMoves repeatedWord R
           (topPositionExtension repeatedFamily p R) (fun j => c j))}
       ∃ (L : G → List (LayerData Unit)) (hL : ∀ D, SChain repeatedWord (L D) repeatedWord),
         (∀ D, (L D).map ofL = D.val) ∧
         ∀ t : Fin 4, ∃ hf : Set.Finite {D : G |
           Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
             (mkD oddDatum.toSKM 0 (L D) (hL D)) = (![-3, -2, 0, 4] : Fin 4 → ℤ) t},
           (∑ D ∈ hf.toFinset, (-1 : ℤ) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             (![0, -1, 3, 7] : Fin 4 → ℤ) t) := by
  obtain ⟨p, hp, L, hL, hm, h⟩ := repeated_coeff
  refine ⟨p, hp, L, hL, hm, ?_⟩
  have hcoeff (m : ℕ) : PowerSeries.coeff m
      (oddDatum.toSuperCartanDatum.dotSeries (-1 : ℤ) word) =
      PowerSeries.coeff m
        (PreF.DotSeries.factor (-1 : ℤ) 2 (by decide) *
          PreF.DotSeries.factor (-1 : ℤ) 2 (by decide)) := by
    congr 1
    simp only [SuperCartanDatum.dotSeries, PreF.DotSeries.strands, Fin.prod_univ_two]
    rfl
  intro t
  obtain ⟨hf, hc⟩ := h ((![-3, -2, 0, 4] : Fin 4 → ℤ) t)
  refine ⟨hf, hc.trans ?_⟩
  fin_cases t <;>
    norm_num [hcoeff, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
      PreF.DotSeries.coeff_factor]

/-- Empty boundaries over a coefficient ring with zero divisors. -/
theorem empty_coeff :
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
           (∑ D ∈ hf.toFinset, (-1 : ZMod 4) ^ (xpar oddDatum.toSKM 0 D.val).val) =
             if z = 0 then 1 else 0) := by
  let a : Fin 0 → Unit := Fin.elim0
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  obtain ⟨p, hp, L, hL, hmap, h⟩ := positive_decorated_family_coeff oddDatum 0 (-1 : ZMod 4)
    (by decide) a a {[]}
    (by intro R hR; obtain rfl := Set.mem_singleton_iff.mp hR; exact ⟨hm, hr⟩)
    (by
      intro R hR _
      refine ⟨[], Set.mem_singleton _, ?_⟩
      exact iso_of_positive_pairs a a hm.pairing_properties.1 hR.pairing_properties.1
        hm.pairing_properties.2.2 hR.pairing_properties.2.2 (Equiv.refl _)
        (fun r => Fin.elim0 r) (fun r => Fin.elim0 r))
    (by
      intro R hR S hS _
      exact (Set.mem_singleton_iff.mp hR).trans (Set.mem_singleton_iff.mp hS).symm)
  refine ⟨p, hp, L, hL, hmap, ?_⟩
  intro z
  obtain ⟨hf, hc⟩ := h z
  refine ⟨hf, hc.trans ?_⟩
  simp only [Fin.forall_fin_zero, ite_true, Fintype.sum_unique, Finset.univ_eq_empty,
    Finset.sum_empty, sub_zero, SuperCartanDatum.dotSeries_empty, PowerSeries.coeff_one]
  by_cases hz : z = 0
  · subst z
    simp
  · by_cases hn : 0 ≤ z
    · have hp : ¬z ≤ 0 := by omega
      simp [hz, hn, hp]
    · simp [hz, hn]

/-- Nonuniform top counts in the same canonical family distinguish both representatives
and the allocations `![1, 2]` and `![2, 1]`. -/
theorem repeated_nonuniform :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      let f := fun z : {R // R ∈ repeatedFamily} × (Fin 2 → ℕ) =>
        dLay repeatedWord (topDotMoves repeatedWord z.1.val
          (fun j => (p z.1 j).val) (fun j => z.2 (p z.1 j)))
      let R : {R // R ∈ repeatedFamily} := ⟨[], by simp [repeatedFamily]⟩
      let S : {R // R ∈ repeatedFamily} := ⟨[.mv (.cross 0)], by simp [repeatedFamily]⟩
      f (R, ![1, 2]) ≠ f (S, ![1, 2]) ∧ f (S, ![1, 2]) ≠ f (S, ![2, 1]) := by
  obtain ⟨p, hp, _⟩ := repeated_coeff
  have hi := positive_topDotMoves_joint_injective word word repeatedFamily family_matching p
  refine ⟨p, hp, ?_, ?_⟩
  · intro h
    have hr := congrArg (fun z => z.1.val) (hi h)
    cases hr
  · intro h
    have hc := congrArg (fun z => z.2 0) (hi h)
    norm_num at hc

end OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
