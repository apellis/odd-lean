import OddMath

/-!
# Non-vacuity checks for the headline theorems

Each `example` below applies a headline theorem to a concrete datum and discharges every
hypothesis by proof. If a later change makes a hypothesis set unsatisfiable for these data, or
breaks the statement's shape, this file stops compiling and CI fails.

The library has no built-in concrete data, so this file builds two small fixtures, both with a
single **odd** simple root (so the super signs are not vacuous):

* `oddSl2 : SuperCartanDatum Unit`, the covering datum of rank one with `a = 2`, `d = 1` and
  parity `1` (bar-consistent), with the root datum `oddSl2Root` on `Y = ℤ` (coroot `1`, root
  `μ ↦ 2μ`);
* `osp12 : SKM.Datum Unit ℤ`, the super Kac–Moody datum of `𝔬𝔰𝔭(1|2)`: weights `ℤ`, simple root
  `2`, coroot `⟨h, μ⟩ = μ`, the simple root odd; with scalars over `ℂ` (all `tᵢⱼ = 1`,
  `sᵢⱼ^{pq} = 0`), the symmetrizer `d = 1` and the units `c_{λ;i} = 1`.

Ellis–Qi Theorems 3.18 and 4.17 are applied over `ℚ`, with the derived categories chosen by
dg-lean's `HasDerivedCategory.small`.
-/

open CategoryTheory

noncomputable section

namespace NonVacuity

/-! ### The covering datum of rank one with an odd simple root -/

open OddMath.CoveringQuantum

/-- The covering Cartan datum of rank one with `a = 2`, `d = 1` and an odd simple root. -/
def oddSl2 : SuperCartanDatum Unit where
  a := Matrix.of fun _ _ ↦ 2
  isGCM :=
    { diag := fun _ ↦ rfl
      offDiag_nonpos := fun i j h ↦ absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ ↦ Iff.rfl }
  d := fun _ ↦ 1
  d_pos := fun _ ↦ one_pos
  d_mul_symm := fun _ _ ↦ rfl
  parity := fun _ ↦ 1
  even_of_odd := fun _ _ _ ↦ even_two

theorem oddSl2_barConsistent : oddSl2.BarConsistent := fun _ ↦ Nat.cast_one

/-- The root datum of `oddSl2` on `Y = ℤ`: simple coroot `1`, simple root `μ ↦ 2μ`. -/
def oddSl2Root : oddSl2.lusztigDatum.RootDatum ℤ where
  coroot _ := 1
  root _ := 2 • AddMonoidHom.id ℤ
  root_coroot i j := by
    rw [SuperCartanDatum.lusztigDatum_cartanMatrix]
    rfl

theorem oddSl2_root_linearIndependent : LinearIndependent ℤ (oddSl2.rootDatumOf oddSl2Root).α := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun f : ℤ →+ ℤ ↦ f 1) hg
  simp [oddSl2Root] at h
  simpa using h

theorem oddSl2_coroot_linearIndependent : LinearIndependent ℤ oddSl2Root.coroot := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  simpa [oddSl2Root] using hg

/-! ### Brundan–Ellis, Super Kac–Moody 2-categories, Theorem 10.1 (nondegeneracy) -/

open scoped Classical in
example : ∀ x, (∀ y, UDot.GenericTensor.sesquilinearForm (oddSl2.rootDatumOf oddSl2Root)
    oddSl2_barConsistent x y = 0) → x = 0 :=
  UDot.sesquilinearForm_nondegenerate oddSl2Root oddSl2_barConsistent
    oddSl2_root_linearIndependent oddSl2_coroot_linearIndependent

/-! ### The super Kac–Moody datum of `𝔬𝔰𝔭(1|2)` -/

open OddMath.SKM

/-- The super Kac–Moody datum of `𝔬𝔰𝔭(1|2)`: weights `ℤ`, simple root `2`, `⟨h, μ⟩ = μ`, and
the simple root odd. -/
def osp12 : Datum Unit ℤ where
  cd :=
    { root := fun _ ↦ 2
      coroot := fun _ ↦ LinearMap.id
      coroot_root_self := fun _ ↦ rfl }
  isGCM :=
    { diag := fun _ ↦ rfl
      offDiag_nonpos := fun i j h ↦ absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ ↦ Iff.rfl }
  parity := fun _ ↦ 1
  even_of_odd := fun _ _ _ ↦ even_two

/-- Scalars for `osp12` over `ℂ`: `tᵢⱼ = 1`, `sᵢⱼ^{pq} = 0`. -/
def osp12Sc : Scalars osp12 ℂ where
  t := fun _ _ ↦ 1
  t_self := fun _ ↦ rfl
  t_symm_of_d_eq_zero := fun _ _ _ ↦ rfl
  s := fun _ _ _ _ ↦ 0
  s_symm := fun _ _ _ _ ↦ rfl
  s_eq_zero := fun _ _ _ _ _ ↦ rfl
  two_isUnit := fun _ ↦ two_ne_zero.isUnit

theorem osp12Sc_homogeneous : osp12Sc.Homogeneous :=
  fun _ _ _ _ _ _ _ _ h ↦ absurd rfl h

/-- The symmetrizer `d = 1` of `osp12`. -/
def osp12Sy : Symmetrizer osp12 where
  d := fun _ ↦ 1
  pos := fun _ ↦ one_pos
  symm := fun _ _ ↦ rfl

/-- The units `c_{λ;i} = 1` of (1.17) for `osp12Sc`. -/
def osp12Cs : CScalars osp12Sc where
  c := fun _ _ ↦ 1
  shift := fun _ _ _ ↦ (one_mul 1).symm

/-! ### Brundan–Ellis, Super Kac–Moody 2-categories, Proposition 7.6

The case `i = j = k` with `i` odd, where the corrected sign of the second triple sum matters. -/

example (μ : ℤ) := AltBraid.prop_7_6 osp12Cs () () () μ

/-! ### Brundan–Ellis, Super Kac–Moody 2-categories, Theorem 8.1

Applied to the empty sequences `a = b = ∅`, with the single reduced matching `[]` and no dots. -/

/-- A matching of the empty sequence with itself has the empty pairing. -/
theorem pairing₂_eq_nil {R : List (StringDiagrams.Chord.TMove (Letter Unit))}
    (hR : IsMatching₂ [] [] R) : pairing₂ [] R = [] := by
  have h := letters_tRun (length_dualW ([] : List (Letter Unit))) R (tStart []) []
    (tStart_letters []) hR.1
  rw [hR.2] at h
  simpa [pairing₂, dualW] using h

theorem isMatching₂_nil : IsMatching₂ ([] : List (Letter Unit)) [] [] := ⟨trivial, rfl⟩

theorem leftEnds₂_nil : leftEnds₂ ([] : List (Letter Unit)) [] = [] := by
  simp [leftEnds₂, pairing₂_eq_nil isMatching₂_nil]

example (μ : ℤ) :
    diagBubSpan osp12 osp12Sc osp12Cs μ [] [] (decoratedFamily₂ [] {[]} fun _ _ ↦ []) = ⊤ :=
  theorem_8_1 μ [] [] {[]}
    (fun R hR ↦ by
      rw [Set.mem_singleton_iff.1 hR]
      exact ⟨isMatching₂_nil, ⟨List.nodup_nil, fun _ hz ↦ by cases hz⟩, List.nodup_nil⟩)
    (fun _ hR' _ ↦ ⟨[], rfl, by
      rw [pairing₂_eq_nil isMatching₂_nil, pairing₂_eq_nil hR']
      exact StringDiagrams.Chord.Iso.refl _⟩)
    (fun _ _ ↦ (0, 0))
    (fun R hR j hj ↦ by
      rw [Set.mem_singleton_iff.1 hR, leftEnds₂_nil] at hj
      cases hj)
    (fun _ _ ↦ [])
    (fun R hR _ ↦ by
      rw [Set.mem_singleton_iff.1 hR]
      exact ⟨rfl, by rw [leftEnds₂_nil]; exact List.Perm.refl _⟩)

/-! ### Brundan–Ellis, Super Kac–Moody 2-categories, Proposition 9.3 -/

example := chevalleyQPiTwo_isAdjointBiequivalence (D := osp12) (Sc := osp12Sc) (sy := osp12Sy)
  (hc := osp12Sc_homogeneous)

/-! ### Brundan–Ellis, Super Kac–Moody 2-categories, Lemma 9.1 and Proposition 9.4

`ψ` at `t = √−1`, its extension to the `(Q, Π)`-envelope, and both inverse laws. -/

example := exists_graded_envelopeSOp_extension
  (psiTwo (sy := osp12Sy) (hc := osp12Sc_homogeneous) Complex.I Complex.I_sq osp12Cs)
  (psiTwo_isGraded Complex.I Complex.I_sq osp12Cs)

example := psiExtension_comp_inverse (sy := osp12Sy) (hc := osp12Sc_homogeneous)
  Complex.I Complex.I_sq osp12Cs

example := psiInverse_comp_extension (sy := osp12Sy) (hc := osp12Sc_homogeneous)
  Complex.I Complex.I_sq osp12Cs

/-! ### Positive reduced matchings: the crossing contribution in Theorem 10.3

Two equal odd strands cross once: degree `-2` and parity `1`. -/

open StringDiagrams StringDiagrams.Chord in
example :
    ∃ (L : List (LayerData Unit))
      (hL : SChain [(true, ()), (true, ())] L [(true, ()), (true, ())]),
      L.map ofL = tLay [(true, ()), (true, ())] [.mv (.cross 0)] ∧
      Diagram.degree (gdeg osp12 osp12Sy) (mkD osp12 (0 : ℤ) L hL) = -2 ∧
      xpar osp12 (0 : ℤ) (tLay [(true, ()), (true, ())] [.mv (.cross 0)]) = 1 := by
  let a : Fin 2 → Unit := fun _ => ()
  let R : List (TMove (Letter Unit)) := [.mv (.cross 0)]
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) R := by
    constructor
    · change 3 < 4 ∧ True
      decide
    · rfl
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) R := by
    refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
    intro z hz
    change z ∈ [_] at hz
    obtain rfl := List.mem_singleton.mp hz
    change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
    decide
  have he : ∀ r : Fin 2, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
    intro r
    fin_cases r
    · change 1 ≠ 3 ∧ (some 2 : Option ℕ) ≠ none ∧ (some 2 : Option ℕ) = some 2
      decide
    · change 0 ≠ 2 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 0
      decide
  have h := positive_matching_degree_parity osp12 osp12Sy (0 : ℤ) a a hm hr
    (Equiv.swap 0 1) he
  simp only [Finset.sum_filter, Fin.sum_univ_two] at h
  simpa [a, R, osp12, osp12Sy, Datum.d, Datum.h, Datum.α] using h

/-! ### Positive matching dot decorations -/

open StringDiagrams.Chord in
example : ∃ p : MatchingStrand (List.ofFn fun _ : Fin 2 => (true, ()))
      [.mv (.cross 0)] → Fin 2,
    Function.Bijective p ∧
      ∀ j : MatchingStrand (List.ofFn fun _ : Fin 2 => (true, ())) [.mv (.cross 0)],
      OnStrand₂ (List.ofFn fun _ : Fin 2 => (true, ())) [.mv (.cross 0)] j (1, (p j).val) := by
  apply positive_top_points (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ())
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

example := topDotMoves_degree osp12 osp12Sy 0 (fun _ : Fin 1 => ())
  (a := List.ofFn fun _ : Fin 1 => (true, ())) (R := [])
  (show IsMatching₂ (List.ofFn fun _ : Fin 1 => (true, ()))
    (List.ofFn fun _ : Fin 1 => (true, ())) [] from ⟨trivial, rfl⟩)
  (fun _ => (0 : Fin 1)) (fun _ => 3) [] rfl

example := topDotMoves_parity osp12 0 (fun _ : Fin 1 => ())
  (a := List.ofFn fun _ : Fin 1 => (true, ())) (R := [])
  (show IsMatching₂ (List.ofFn fun _ : Fin 1 => (true, ()))
    (List.ofFn fun _ : Fin 1 => (true, ())) [] from ⟨trivial, rfl⟩)
  (fun _ => (0 : Fin 1)) (fun _ => 3)

/-! ### Formal dot factors for two odd strands -/

section
open scoped BigOperators

example : oddSl2.dotSeries (-1 : ℤ) (fun _ : Fin 2 ↦ ()) =
    ∏ _r : Fin 2, Ring.inverse
      (1 - PowerSeries.C (oddSl2.pii (-1 : ℤ) ()) *
        PowerSeries.X ^ (2 * oddSl2.d ())) := by
  exact oddSl2.dotSeries_eq_prod_inverse (-1 : ℤ) (fun _ : Fin 2 ↦ ())

example : PowerSeries.coeff 2 (oddSl2.dotSeries (-1 : ℤ) (fun _ : Fin 2 ↦ ())) =
    ∑ l ∈ Finset.finsuppAntidiag Finset.univ 2,
      ∏ r : Fin 2, if 2 * oddSl2.d () ∣ l r then
        oddSl2.pii (-1 : ℤ) () ^ (l r / (2 * oddSl2.d ())) else 0 :=
  oddSl2.coeff_dotSeries (-1) _ 2

example : PowerSeries.coeff 2 (oddSl2.dotSeries (-1 : ℤ) (fun _ : Fin 2 ↦ ())) = -2 := by
  change PowerSeries.coeff 2
    (PreF.DotSeries.strands (fun _ : Fin 2 ↦ (-1 : ℤ)) (fun _ ↦ 2)
      (fun _ ↦ by decide)) = -2
  simp only [PreF.DotSeries.strands, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_two, PowerSeries.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, PreF.DotSeries.coeff_factor]

example := oddSl2.dotCount_monomial (-1 : ℤ)
  (fun _ : Fin 2 ↦ ()) (fun _ ↦ 1)

example : oddSl2.norm (1 : ℤˣ) (-1 : ℤ) () =
    Ring.inverse ((oddSl2.dotDenominator (-1 : ℤ) ()).eval (1 : ℤ)) :=
  oddSl2.norm_eq_inverse_eval_dotDenominator (-1) 1 ()

end

/-! ### Undecorated boundary bending -/

example : ∃ E :
    {R : List (StringDiagrams.Chord.TMove (OddMath.SKM.Letter Unit)) //
      R ∈ ({[]} : Set _)} ≃
    {S : List (StringDiagrams.Chord.TMove (OddMath.SKM.Letter Unit)) //
      S ∈ ({[.mv (.cup 0 (false, ()))]} : Set _)},
    ∀ R, StringDiagrams.Chord.Iso (OddMath.SKM.pairing₂ [] (E R).val)
      (OddMath.SKM.pairing₂ [(true, ())] R.val) :=
  OddMath.SKM.MatchingBendingExamples.identity_cup_equiv (true, ())

/-! ### Ellis–Qi, The differential graded odd nilHecke algebra, Theorems 3.18 and 4.17 -/

attribute [local instance] DG.HasDerivedCategory.small DG.CatModule.HasDerivedCategory.small

example := OddMath.Frontier.EQK0.thm_3_18_equiv_one ℚ

example (n : ℕ) := OddMath.Frontier.EQK0.thm_4_17_equiv_E ℚ n

end NonVacuity

namespace NonVacuity

/-! ### Positive top-decorated matchings in Theorem 10.3

Two equal odd strands cross once, with top dot counts `![1, 2]`:
degree `4` and parity `0`, on the same ordinary diagram. -/

open OddMath.SKM StringDiagrams StringDiagrams.Chord in
-- One odd crossing and three odd dots have even total parity.
example :
    ∃ p : MatchingStrand [(true, ()), (true, ())] [.mv (.cross 0)] ≃ Fin 2,
      (∀ j : MatchingStrand [(true, ()), (true, ())] [.mv (.cross 0)],
        OnStrand₂ [(true, ()), (true, ())] [.mv (.cross 0)] j.val (1, (p j).val)) ∧
      ∃ (L : List (LayerData Unit))
        (hL : SChain [(true, ()), (true, ())] L [(true, ()), (true, ())]),
        L.map ofL = dLay [(true, ()), (true, ())]
          (topDotMoves [(true, ()), (true, ())] [.mv (.cross 0)]
            (fun j => (p j).val) (fun j => ![1, 2] (p j))) ∧
        Diagram.degree (gdeg osp12 osp12Sy) (mkD osp12 (0 : ℤ) L hL) =
          4 ∧
        xpar osp12 (0 : ℤ) (L.map ofL) = 0 := by
  let a : Fin 2 → Unit := fun _ => ()
  let R : List (TMove (Letter Unit)) := [.mv (.cross 0)]
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) R := by
    constructor
    · change 3 < 4 ∧ True
      decide
    · rfl
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) R := by
    refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
    intro z hz
    change z ∈ [_] at hz
    obtain rfl := List.mem_singleton.mp hz
    change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
    decide
  have he : ∀ r : Fin 2, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
    intro r
    fin_cases r
    · change 1 ≠ 3 ∧ (some 2 : Option ℕ) ≠ none ∧ (some 2 : Option ℕ) = some 2
      decide
    · change 0 ≠ 2 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 0
      decide
  obtain ⟨p, hpoints, h⟩ := positive_decorated_degree_parity osp12 osp12Sy (0 : ℤ) a a hm hr
    (Equiv.swap 0 1) he
  obtain ⟨L, hL, hm, hd, hp⟩ := h ![1, 2]
  refine ⟨p, hpoints, L, hL, hm, ?_, ?_⟩
  · simp only [Finset.sum_filter, Fin.sum_univ_two] at hd
    simpa [a, osp12, osp12Sy, Datum.d, Datum.h, Datum.α] using hd
  · rw [hm]
    simp only [Finset.sum_filter, Fin.sum_univ_two] at hp
    have hz : (1 + (1 + 2) : ZMod 2) = 0 := by decide
    simpa [a, osp12, hz] using hp

end NonVacuity

namespace NonVacuity
open OddMath.SKM OddMath.CoveringQuantum
private abbrev Q := oddSl2.rootDatumOf oddSl2Root

-- The existing osp(1|2) datum is recovered on its own weight lattice, without a transport.
def osp12Covering : RootDatum Unit ℤ where
  toSuperCartanDatum := oddSl2
  cd := osp12.cd
  coroot_root _ _ := rfl
example : osp12Covering.toSKM = osp12 := rfl
example : osp12Covering.skmSymmetrizer = osp12Sy := rfl
example : Q.toSKM.α () (1 : ℤ) = osp12.α () := rfl
example (μ : ℤ →+ ℤ) : Q.toSKM.h () μ = osp12.h () (μ 1) := rfl
example : gdeg Q.toSKM Q.skmSymmetrizer (.dot (), 0) = 2 := rfl
example : Shape.parity Q.toSKM (.dot ()) = 1 := rfl

open StringDiagrams StringDiagrams.Chord in
example :
    ∃ (L : List (LayerData Unit))
      (hL : SChain [(true, ()), (true, ())] L [(true, ()), (true, ())]),
      L.map ofL = tLay [(true, ()), (true, ())] [.mv (.cross 0)] ∧
      Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer) (mkD Q.toSKM (0 : ℤ →+ ℤ) L hL) = -2 ∧
      xpar Q.toSKM (0 : ℤ →+ ℤ) (tLay [(true, ()), (true, ())] [.mv (.cross 0)]) = 1 := by
  let a : Fin 2 → Unit := fun _ => ()
  let R : List (TMove (Letter Unit)) := [.mv (.cross 0)]
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) R := by
    constructor
    · change 3 < 4 ∧ True
      decide
    · rfl
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) R := by
    refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
    intro z hz
    change z ∈ [_] at hz
    obtain rfl := List.mem_singleton.mp hz
    change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
    decide
  have he : ∀ r : Fin 2, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
    intro r
    fin_cases r
    · change 1 ≠ 3 ∧ (some 2 : Option ℕ) ≠ none ∧ (some 2 : Option ℕ) = some 2
      decide
    · change 0 ≠ 2 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 0
      decide
  have h := positive_matching_covering_degree_parity Q (0 : ℤ →+ ℤ) a a hm hr
    (Equiv.swap 0 1) he
  simp only [Finset.sum_filter, Fin.sum_univ_two] at h
  simpa [a, R, Q, oddSl2, SuperCartanDatum.dot] using h


end NonVacuity

namespace NonVacuity.DecoratedEnumeration

open OddMath.SKM StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedEnumerationExamples

-- Concrete representative families, with all coverage and uniqueness hypotheses proved.
example :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      Nonempty (({w : Equiv.Perm (Fin 2) // ∀ r, (fun _ => ()) r = (fun _ => ()) (w r)} ×
        (Fin 2 → ℕ)) ≃ {L // L ∈ decoratedFamily₂ repeatedWord repeatedFamily
          (fun R c => topDotMoves repeatedWord R (topPositionExtension repeatedFamily p R)
            (fun j => c j))}) := repeated_enumeration

example :
    ∃ p : ∀ R : {R : List (TMove (Letter Empty)) // R ∈ ({[]} : Set _)},
        MatchingStrand [] R.val ≃ Fin 0,
      Nonempty (({w : Equiv.Perm (Fin 0) // ∀ r, (Fin.elim0 r : Empty) = Fin.elim0 (w r)} ×
        (Fin 0 → ℕ)) ≃ {L // L ∈ decoratedFamily₂ [] ({[]} : Set _)
          (fun R c => topDotMoves [] R (topPositionExtension {[]} p R) (fun j => c j))}) :=
  empty_enumeration

example :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      let f := fun z : {R // R ∈ repeatedFamily} × (Fin 2 → ℕ) =>
        dLay repeatedWord (topDotMoves repeatedWord z.1.val
          (fun j => (p z.1 j).val) (fun j => z.2 (p z.1 j)))
      let R : {R // R ∈ repeatedFamily} := ⟨[], by simp [repeatedFamily]⟩
      let S : {R // R ∈ repeatedFamily} := ⟨[.mv (.cross 0)], by simp [repeatedFamily]⟩
      f (R, ![1, 2]) ≠ f (S, ![1, 2]) ∧ f (S, ![1, 2]) ≠ f (S, ![2, 1]) :=
  repeated_decorations_distinct

end NonVacuity.DecoratedEnumeration

noncomputable section
namespace NonVacuity.DecoratedCoefficients
open OddMath.SKM OddMath.CoveringQuantum StringDiagrams StringDiagrams.Chord
open scoped BigOperators

private abbrev oddDatum := NonVacuity.osp12Covering

private abbrev word : Fin 2 → Unit := fun _ => ()
private abbrev crossing : List (TMove (Letter Unit)) := [.mv (.cross 0)]

private theorem crossing_matching :
    IsMatching₂ (List.ofFn fun r => (true, word r))
      (List.ofFn fun r => (true, word r)) crossing := by
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

private theorem crossing_reduced :
    StrictReduced₂ (List.ofFn fun r => (true, word r)) crossing := by
  refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
  intro z hz
  change z ∈ [_] at hz
  obtain rfl := List.mem_singleton.mp hz
  change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
  decide

private theorem crossing_endpoints : ∀ r : Fin 2,
    Same (pairing₂ (List.ofFn fun r => (true, word r)) crossing)
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
  intro r
  fin_cases r
  · change 1 ≠ 3 ∧ (some 2 : Option ℕ) ≠ none ∧ (some 2 : Option ℕ) = some 2
    decide
  · change 0 ≠ 2 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 0
    decide

-- The crossing shift is -2, not a natural degree. Every hypothesis is proved.
private theorem crossing_coeff :
    ∃ p : MatchingStrand [(true, ()), (true, ())] crossing ≃ Fin 2,
      (∀ j, OnStrand₂ [(true, ()), (true, ())] crossing j.val (1, (p j).val)) ∧
      ∃ (L : (Fin 2 → ℕ) → List (LayerData Unit))
        (hL : ∀ c, SChain [(true, ()), (true, ())] (L c) [(true, ()), (true, ())]),
        (∀ c, (L c).map ofL = dLay [(true, ()), (true, ())]
          (topDotMoves [(true, ()), (true, ())] crossing
            (fun j => (p j).val) (fun j => c (p j)))) ∧
        ∀ z : ℤ,
          ∃ hf : Set.Finite {c : Fin 2 → ℕ |
            Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
              (mkD oddDatum.toSKM 0 (L c) (hL c)) = z},
            (∑ c ∈ hf.toFinset, (-1 : ℤ) ^ (xpar oddDatum.toSKM 0 ((L c).map ofL)).val) =
              if -2 ≤ z then -PowerSeries.coeff (z + 2).toNat
                (oddDatum.toSuperCartanDatum.dotSeries (-1 : ℤ) word) else 0 := by
  obtain ⟨p, hp, L, hL, hm, h⟩ := positive_decorated_coeff oddDatum 0 (-1 : ℤ)
    (by norm_num) word word crossing_matching crossing_reduced (Equiv.swap 0 1) crossing_endpoints
  refine ⟨p, hp, L, hL, hm, ?_⟩
  intro z
  obtain ⟨hf, hc⟩ := h z
  refine ⟨hf, ?_⟩
  simp only [Finset.sum_filter, Fin.sum_univ_two] at hc
  norm_num [word, oddDatum, osp12Covering, oddSl2, SuperCartanDatum.dot] at hc ⊢
  have hv : (1 : ZMod 2).val = 1 := rfl
  simpa only [hv, pow_one, neg_one_mul] using hc

-- The degree -3 fiber vanishes; degree -2 has the odd crossing contribution.
-- At degree 4 all four allocations, including ![1, 2] and ![2, 1], contribute.
example : ∃ (L : (Fin 2 → ℕ) → List (LayerData Unit))
    (hL : ∀ c, SChain [(true, ()), (true, ())] (L c) [(true, ()), (true, ())]),
    ∀ t : Fin 4, ∃ hf : Set.Finite {c : Fin 2 → ℕ |
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 (L c) (hL c)) = (![-3, -2, 0, 4] : Fin 4 → ℤ) t},
      (∑ c ∈ hf.toFinset, (-1 : ℤ) ^ (xpar oddDatum.toSKM 0 ((L c).map ofL)).val) =
        (![0, -1, 2, 4] : Fin 4 → ℤ) t := by
  obtain ⟨_, _, L, hL, _, h⟩ := crossing_coeff
  refine ⟨L, hL, ?_⟩
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
  refine ⟨hf, ?_⟩
  fin_cases t <;>
    norm_num [hcoeff, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
      PreF.DotSeries.coeff_factor] at hc ⊢ <;> exact hc

-- Nonuniform counts on repeated odd colours: one crossing and three dots.
example :
    ∃ p : MatchingStrand [(true, ()), (true, ())] crossing ≃ Fin 2,
      (∀ j, OnStrand₂ [(true, ()), (true, ())] crossing j.val (1, (p j).val)) ∧
      ∃ (L : List (LayerData Unit))
        (hL : SChain [(true, ()), (true, ())] L [(true, ()), (true, ())]),
        L.map ofL = dLay [(true, ()), (true, ())]
          (topDotMoves [(true, ()), (true, ())] crossing
            (fun j => (p j).val) (fun j => ![1, 2] (p j))) ∧
        Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
          (mkD oddDatum.toSKM 0 L hL) = 4 ∧ xpar oddDatum.toSKM 0 (L.map ofL) = 0 := by
  obtain ⟨p, hp, hg⟩ := positive_decorated_degree_parity oddDatum.toSKM
    oddDatum.skmSymmetrizer 0 word word crossing_matching crossing_reduced
    (Equiv.swap 0 1) crossing_endpoints
  obtain ⟨L, hL, hm, hd, hpar⟩ := hg ![1, 2]
  refine ⟨p, hp, L, hL, hm, ?_, ?_⟩
  · simp only [Finset.sum_filter, Fin.sum_univ_two] at hd
    simpa [word, oddDatum, osp12Covering, oddSl2, OddMath.CoveringQuantum.RootDatum.toSKM_d] using hd
  · rw [hm]
    simp only [Finset.sum_filter, Fin.sum_univ_two] at hpar
    have hz : (1 + (1 + 2) : ZMod 2) = 0 := by decide
    simpa [word, oddDatum, osp12Covering, oddSl2, hz] using hpar

-- Empty words and a coefficient ring with zero divisors.
example :
    ∃ p : MatchingStrand ([] : List (Letter Unit)) [] ≃ Fin 0,
      (∀ j, OnStrand₂ ([] : List (Letter Unit)) [] j.val (0, (p j).val)) ∧
      ∃ (L : (Fin 0 → ℕ) → List (LayerData Unit)) (hL : ∀ c, SChain [] (L c) []),
        (∀ c, (L c).map ofL = dLay []
          (topDotMoves [] [] (fun j => (p j).val) (fun j => c (p j)))) ∧
        ∀ z : ℤ, ∃ hf : Set.Finite {c : Fin 0 → ℕ |
          Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
            (mkD oddDatum.toSKM 0 (L c) (hL c)) = z},
          (∑ c ∈ hf.toFinset, (-1 : ZMod 4) ^ (xpar oddDatum.toSKM 0 ((L c).map ofL)).val) =
            if z = 0 then 1 else 0 := by
  let a : Fin 0 → Unit := Fin.elim0
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  obtain ⟨p, hp, L, hL, hmap, h⟩ := positive_decorated_coeff oddDatum 0 (-1 : ZMod 4)
    (by decide) a a hm hr (Equiv.refl _) (fun r => Fin.elim0 r)
  refine ⟨p, hp, L, hL, hmap, ?_⟩
  intro z
  obtain ⟨hf, hc⟩ := h z
  refine ⟨hf, ?_⟩
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
    SuperCartanDatum.dotSeries_empty, PowerSeries.coeff_one] at hc
  by_cases hz : z = 0
  · subst z
    simpa using hc
  · by_cases hn : 0 ≤ z
    · have hp : ¬z ≤ 0 := by omega
      simpa [hz, hn, hp] using hc
    · simpa [hz, hn] using hc

end NonVacuity.DecoratedCoefficients


namespace NonVacuity.PositivePointGrading

open OddMath.SKM StringDiagrams StringDiagrams.Chord DTMove
open OddMath.SKM.PositivePointGradingExamples

-- Both distinct-colour point placements, with every hypothesis proved.
example :
    ∀ ds ∈ [[.dt 0, .tm (.mv (.cross 0))], [.tm (.mv (.cross 0)), .dt 1]],
    ∃ (L : List (LayerData Bool))
      (hL : SChain [(true, false), (true, true)] L [(true, true), (true, false)]),
      L.map ofL = dLay [(true, false), (true, true)] ds ∧
      Diagram.degree (gdeg twoColourDatum twoColourSymmetrizer)
        (mkD twoColourDatum 0 L hL) = 2 ∧
      xpar twoColourDatum 0 (dLay [(true, false), (true, true)] ds) = 1 :=
  two_colour_point_invariance

end NonVacuity.PositivePointGrading
