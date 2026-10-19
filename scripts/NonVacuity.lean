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


noncomputable section
namespace PositiveDecoratedFamilyCoeffNonVacuity
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open scoped BigOperators
attribute [local instance] Classical.propDecidable
private abbrev Q := oddDatum
private abbrev μ : ℤ := 0
private abbrev π : ℤ := -1
private abbrev n : ℕ := 2
private abbrev I := Unit
private abbrev a : Fin n → I := fun _ => ()
private abbrev b : Fin n → I := fun _ => ()
private abbrev M := repeatedFamily
local notation "A" => (List.ofFn fun r => (true, a r))
local notation "B" => (List.ofFn fun r => (true, b r))

example : let C := Q.toSuperCartanDatum
  let κ : Equiv.Perm (Fin n) → ℤ := fun w =>
    ∑ r, ∑ s with r < s ∧ w s < w r, -C.dot (a r) (a s)
  let ε : Equiv.Perm (Fin n) → ZMod 2 := fun w =>
    ∑ r, ∑ s with r < s ∧ w s < w r, Q.parity (a r) * Q.parity (a s)
  ∃ p : ∀ R : {R // R ∈ M}, MatchingStrand A R.val ≃ Fin n,
    (∀ R (j : MatchingStrand A R.val),
      OnStrand₂ A R.val j.val (R.val.length, (p R j).val)) ∧
    (let family := decoratedFamily₂ A M
       (fun R c => topDotMoves A R (topPositionExtension M p R) (fun j => c j))
     let G := {D // D ∈ family}
     ∃ (L : G → List (LayerData I)) (hL : ∀ D, SChain A (L D) B),
       (∀ D, (L D).map ofL = D.val) ∧
       ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
         Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
           (mkD Q.toSKM μ (L D) (hL D)) = z},
         (∑ D ∈ hf.toFinset, π ^ (xpar Q.toSKM μ D.val).val) =
           ∑ w : Equiv.Perm (Fin n), if ∀ r, a r = b (w r) then
             if κ w ≤ z then π ^ (ε w).val *
               PowerSeries.coeff (z - κ w).toNat (C.dotSeries π b)
             else 0
           else 0) := by
  obtain ⟨p, hp, L, hL, hm, h⟩ :=
    positive_decorated_family_coeff Q μ π (by norm_num [π]) a b M
      family_matching family_coverage family_unique
  refine ⟨p, hp, L, hL, hm, ?_⟩
  intro z
  obtain ⟨hf, hc⟩ := h z
  refine ⟨hf, hc.trans ?_⟩
  apply Finset.sum_congr rfl
  intro w _
  have hcol : ∀ r, a r = b (w r) := fun _ => rfl
  rw [ite_eq_left hcol, ite_eq_left hcol]

end PositiveDecoratedFamilyCoeffNonVacuity


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


noncomputable section
namespace OddMath.SKM.PositiveFormCoefficientsNonVacuity
open CoveringQuantum StringDiagrams StringDiagrams.Chord
open PositiveDecoratedFamilyCoefficientsExamples PositiveFormCoefficientsExamples
open scoped BigOperators

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

example (z : ℤ) : (repeatedForm 1 (by norm_num) 0).coeff z = if z = 0 then 1 else 0 :=
  PositiveFormCoefficientsExamples.empty_coeff 1 (by norm_num) z
example (z : ℤ) : (repeatedForm (-1) (by norm_num) 0).coeff z = if z = 0 then 1 else 0 :=
  PositiveFormCoefficientsExamples.empty_coeff (-1) (by norm_num) z
example : (repeatedForm 1 (by norm_num) 2).coeff (-2) = 1 ∧
    (repeatedForm 1 (by norm_num) 2).coeff (-3) = 0 := repeated_negative_coeff 1 (by norm_num)
example : (repeatedForm (-1) (by norm_num) 2).coeff (-2) = -1 ∧
    (repeatedForm (-1) (by norm_num) 2).coeff (-3) = 0 := repeated_negative_coeff (-1) (by norm_num)

end OddMath.SKM.PositiveFormCoefficientsNonVacuity

noncomputable section
namespace NonVacuity.UnequalPositive
open OddMath.SKM.PositiveFormCoefficientsExamples
example (z : ℤ) :
    (twoWordForm 1 (by norm_num) 0 1).coeff z = 0 :=
  unequal_coeff 1 (by norm_num) (by decide : 0 ≠ 1) z

example : EmptyFamilyComparison 1 (by norm_num) 0 1 :=
  unequal_family 1 (by norm_num) (by decide : 0 ≠ 1)

example (z : ℤ) :
    (twoWordForm (-1) (by norm_num) 0 1).coeff z = 0 :=
  unequal_coeff (-1) (by norm_num) (by decide : 0 ≠ 1) z

example : EmptyFamilyComparison (-1) (by norm_num) 0 1 :=
  unequal_family (-1) (by norm_num) (by decide : 0 ≠ 1)

example (z : ℤ) :
    (twoWordForm 1 (by norm_num) 1 2).coeff z = 0 :=
  unequal_coeff 1 (by norm_num) (by decide : 1 ≠ 2) z

example : EmptyFamilyComparison 1 (by norm_num) 1 2 :=
  unequal_family 1 (by norm_num) (by decide : 1 ≠ 2)

example (z : ℤ) :
    (twoWordForm (-1) (by norm_num) 1 2).coeff z = 0 :=
  unequal_coeff (-1) (by norm_num) (by decide : 1 ≠ 2) z

example : EmptyFamilyComparison (-1) (by norm_num) 1 2 :=
  unequal_family (-1) (by norm_num) (by decide : 1 ≠ 2)

example (z : ℤ) :
    (twoWordForm 1 (by norm_num) 1 0).coeff z = 0 :=
  unequal_coeff 1 (by norm_num) (by decide : 1 ≠ 0) z

example : EmptyFamilyComparison 1 (by norm_num) 1 0 :=
  unequal_family 1 (by norm_num) (by decide : 1 ≠ 0)

example (z : ℤ) :
    (twoWordForm (-1) (by norm_num) 1 0).coeff z = 0 :=
  unequal_coeff (-1) (by norm_num) (by decide : 1 ≠ 0) z

example : EmptyFamilyComparison (-1) (by norm_num) 1 0 :=
  unequal_family (-1) (by norm_num) (by decide : 1 ≠ 0)

example (z : ℤ) :
    (twoWordForm 1 (by norm_num) 2 1).coeff z = 0 :=
  unequal_coeff 1 (by norm_num) (by decide : 2 ≠ 1) z

example : EmptyFamilyComparison 1 (by norm_num) 2 1 :=
  unequal_family 1 (by norm_num) (by decide : 2 ≠ 1)

example (z : ℤ) :
    (twoWordForm (-1) (by norm_num) 2 1).coeff z = 0 :=
  unequal_coeff (-1) (by norm_num) (by decide : 2 ≠ 1) z

example : EmptyFamilyComparison (-1) (by norm_num) 2 1 :=
  unequal_family (-1) (by norm_num) (by decide : 2 ≠ 1)

end NonVacuity.UnequalPositive

namespace NonVacuity.LabelledPositive
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveLabelledCoefficientsExamples
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open scoped BigOperators

example :
    ∃ (L : Index → List (LayerData Unit)) (hL : ∀ t, SChain repeatedWord (L t) repeatedWord),
      (∀ t, (L t).map ofL = dLay repeatedWord (serializer t.1 t.2)) ∧
      ∃ hf : Set.Finite {t : Index |
        Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
          (mkD oddDatum.toSKM 0 (L t) (hL t)) = -2},
        (∑ t ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (serializer t.1 t.2))).val) = 1 ∧
        (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (serializer t.1 t.2))).val) = -1 := repeated_signs

example :
    let R : {R // R ∈ repeatedFamily} := ⟨[], by simp⟩
    serializer R (fun _ => 1) = [.dt 0, .dt 1] ∧
      topDotMoves repeatedWord R.val (fun j => position R.val j.val) (fun _ => 1) =
        [.dt 1, .dt 0] := noncanonical_order

end NonVacuity.LabelledPositive

noncomputable section
namespace BoundedIntegrationNonVacuity
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveLabelledCoefficientsExamples
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open OddMath.SKM.DTMove
open scoped BigOperators
attribute [local instance] Classical.propDecidable

example :
    ∃ (τ : ∀ R : {R // R ∈ repeatedFamily},
        (MatchingStrand repeatedWord R.val → ℕ) → List (DTMove Unit)),
      (∀ R c, Decorates₂ repeatedWord R.val (points R) (strandCounts c) (τ R c)) ∧
    ∃ (L : Index → List (LayerData Unit)) (hL : ∀ t, SChain repeatedWord (L t) repeatedWord),
      (∀ t, (L t).map ofL = dLay repeatedWord (τ t.1 t.2)) ∧
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
        ∃ hf : Set.Finite {t : Index |
          Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
            (mkD oddDatum.toSKM 0 (L t) (hL t)) = z},
          (∑ t ∈ hf.toFinset, σ ^ (xpar oddDatum.toSKM 0
            (dLay repeatedWord (τ t.1 t.2))).val) = (repeatedForm σ hσ 2).coeff z :=
  positive_bounded_points_family_form_coeff oddDatum odd_barConsistent 0
    (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) repeatedFamily
    family_matching family_coverage family_unique points points_valid points_bounded

example :
    ∃ (τ : ∀ R : {R // R ∈ repeatedFamily},
        (MatchingStrand repeatedWord R.val → ℕ) → List (DTMove Unit)),
      (∀ R c, Decorates₂ repeatedWord R.val (points R) (strandCounts c) (τ R c)) ∧
    ∃ (L : Index → List (LayerData Unit)) (hL : ∀ t, SChain repeatedWord (L t) repeatedWord),
      (∀ t, (L t).map ofL = dLay repeatedWord (τ t.1 t.2)) ∧
      ∃ hf : Set.Finite {t : Index |
        Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
          (mkD oddDatum.toSKM 0 (L t) (hL t)) = -2},
        (∑ t ∈ hf.toFinset, (1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (τ t.1 t.2))).val) = 1 ∧
        (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (xpar oddDatum.toSKM 0
          (dLay repeatedWord (τ t.1 t.2))).val) = -1 := by
  obtain ⟨τ, hτ, L, hL, hm, hc⟩ := bounded_repeated_family
  obtain ⟨hf, hplus⟩ := hc 1 (by norm_num) (-2)
  obtain ⟨hf', hminus⟩ := hc (-1) (by norm_num) (-2)
  exact ⟨τ, hτ, L, hL, hm, hf, hplus.trans (repeated_negative_coeff 1 (by norm_num)).1,
    hminus.trans (repeated_negative_coeff (-1) (by norm_num)).1⟩

example : ∃ ds : List (DTMove Unit),
    Decorates₂ [(true, ())] [] (fun _ => (0, 0))
      (strandCounts fun _ : MatchingStrand [(true, ())] [] => 3) ds ∧
    DOk₂ [(true, ())] ds :=
  BoundedPointSerializationExamples.identity_boundary

example : ∃ ds : List (DTMove Unit),
    tmoves ds = [.mv (.cross 0), .mv (.cross 1)] ∧
    (dotPts ds).Perm [(2, 1), (0, 2), (1, 0), (0, 1), (2, 1)] :=
  BoundedPointSerializationExamples.unsorted_boundaries

example : ∃ ds : List (DTMove Unit),
    Decorates₂ (List.ofFn fun _ : Fin 3 => (true, ()))
      [.mv (.cross 0), .mv (.cross 1)]
      (fun j => (1, if j = 0 then 2 else if j = 1 then 0 else 1))
      (strandCounts fun j : MatchingStrand (List.ofFn fun _ : Fin 3 => (true, ()))
        [.mv (.cross 0), .mv (.cross 1)] => j.val + 1) ds ∧
    DOk₂ (List.ofFn fun _ : Fin 3 => (true, ())) ds :=
  BoundedPointSerializationExamples.interior_counts

end BoundedIntegrationNonVacuity

namespace NonVacuity.CupAttachment
open OddMath.SKM StringDiagrams StringDiagrams.Chord DTMove
open OddMath.SKM.PositiveFormCoefficientsExamples
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples

private def R : List (TMove (Letter Unit)) := [.mv (.cross 0)]
private def A : List (Letter Unit) := [(true, ()), (true, ())]
private def a : List (Letter Unit) := [(true, ())]
private def ds : List (DTMove Unit) := [.dt 0, .tm (.mv (.cross 0))]
private def q (j : ℕ) : ℕ × ℕ := (0, 1 - j)
private def c (j : MatchingStrand A R) : ℕ := if j.val = 1 then 1 else 0

example :
    IsMatching₂ a ((false, ()) :: A) (cupAttachMatching () R) ∧
    ∃ e : MatchingStrand A R ≃ MatchingStrand a (cupAttachMatching () R),
      (∀ j, (e j).val = j.val) ∧
      Decorates₂ a (cupAttachMatching () R) (cupAttachPoint ∘ q)
        (strandCounts (c ∘ e.symm)) (cupAttachMoves () ds) ∧
      (∀ j ∈ leftEnds₂ a (cupAttachMatching () R),
        (cupAttachPoint (q j)).1 ≤ (cupAttachMatching () R).length ∧
        OnStrand₂ a (cupAttachMatching () R) j (cupAttachPoint (q j))) ∧
      ∃ (L : List (LayerData Unit))
        (hLB : SChain a (cupAttachLayers () a L) ((false, ()) :: A)),
        (cupAttachLayers () a L).map ofL = dLay a (cupAttachMoves () ds) ∧
        Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer) (mkD oddDatum.toSKM 0 (cupAttachLayers () a L) hLB) =
          oddDatum.skmSymmetrizer.d () * oddDatum.toSKM.d () () + 2 * oddDatum.skmSymmetrizer.d () + oddDatum.skmSymmetrizer.d () * (1 + oddDatum.toSKM.h () (wt oddDatum.toSKM 0 a)) ∧
        xpar oddDatum.toSKM 0 (dLay a (cupAttachMoves () ds)) =
          oddDatum.toSKM.parity () * oddDatum.toSKM.parity () + oddDatum.toSKM.parity () :=
  CupTransportExamples.crossing_dot_cup oddDatum.toSKM oddDatum.skmSymmetrizer 0

example :
    let S : List (TMove (Letter Unit)) := [.mv (.cup 1 (false, ())), .cap 0]
    IsMatching₂ [] [(false, ()), (true, ())] (cupAttachMatching () S) ∧
    OnStrand₂ [] (cupAttachMatching () S) 0 (2, 3) := CupTransportExamples.cup_cap_point

example :
    ∀ ds ∈ [[.dt 0, .tm (.mv (.cross 0))], [.tm (.mv (.cross 0)), .dt 1]],
    ∃ (L : List (LayerData Unit))
      (hL : SChain [(true, ()), (true, ())] L [(true, ()), (true, ())])
      (hB : SChain [(true, ())] (cupAttachLayers () [(true, ())] L)
        [(false, ()), (true, ()), (true, ())]),
      L.map ofL = dLay [(true, ()), (true, ())] ds ∧
      (cupAttachLayers () [(true, ())] L).map ofL = dLay [(true, ())] (cupAttachMoves () ds) ∧
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer) (mkD oddDatum.toSKM 0 L hL) = oddDatum.skmSymmetrizer.d () * oddDatum.toSKM.d () () + 2 * oddDatum.skmSymmetrizer.d () ∧
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer) (mkD oddDatum.toSKM 0 (cupAttachLayers () [(true, ())] L) hB) =
        oddDatum.skmSymmetrizer.d () * oddDatum.toSKM.d () () + 2 * oddDatum.skmSymmetrizer.d () + oddDatum.skmSymmetrizer.d () * (1 + oddDatum.toSKM.h () (wt oddDatum.toSKM 0 [(true, ())])) ∧
      xpar oddDatum.toSKM 0 (dLay [(true, ())] (cupAttachMoves () ds)) =
        oddDatum.toSKM.parity () * oddDatum.toSKM.parity () + oddDatum.toSKM.parity () := cup_attached_crossing_dot_points oddDatum.toSKM oddDatum.skmSymmetrizer 0 () ()

end NonVacuity.CupAttachment

namespace NonVacuity.MinimalRewrite
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples

example :
    let R : List (TMove (Letter Unit)) := [.mv (.cross 0)]
    let a : List (Letter Unit) := [(true, ())]
    IsMatching₂ a [(false, ()), (true, ()), (true, ())] (cupAttachMatching () R) ∧
      Reduced₂ a (cupAttachMatching () R) ∧ ncr₂ (cupAttachMatching () R) = 1 :=
  CupReducedExamples.crossing_cup

example :
    cupAttachMatching () ([.cap 0] : List (TMove (Letter Unit))) =
      [.mv (.cup 0 (false, ())), .cap 1] ∧
    IsMatching₂ [(false, ())] [(false, ())]
      [.mv (.cup 0 (false, ())), .cap 1] ∧
    Reduced₂ [(false, ())] [.mv (.cup 0 (false, ())), .cap 1] :=
  CupReducedExamples.cap_attached_zigzag

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (chordLay [(false, ())] [.cup 0 (true, ()), .cross 1]) =
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (chordLay [(false, ())] [.cup 1 (true, ()), .cross 0]) ∧
    xpar oddDatum.toSKM 0 (chordLay [(false, ())] [.cup 0 (true, ()), .cross 1]) =
      xpar oddDatum.toSKM 0 (chordLay [(false, ())] [.cup 1 (true, ()), .cross 0]) :=
  TableIsotopyExamples.pitchfork oddDatum.toSKM oddDatum.skmSymmetrizer 0 (true, ()) (false, ())

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (chordLay [] [.cup 0 (false, ()), .cup 0 (true, ()), .cross 1]) =
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (chordLay [] [.cup 0 (false, ()), .cup 1 (true, ()), .cross 0]) ∧
    xpar oddDatum.toSKM 0 (chordLay [] [.cup 0 (false, ()), .cup 0 (true, ()), .cross 1]) =
      xpar oddDatum.toSKM 0 (chordLay [] [.cup 0 (false, ()), .cup 1 (true, ()), .cross 0]) :=
  TableIsotopyExamples.contextual_pitchfork oddDatum.toSKM oddDatum.skmSymmetrizer 0 () ()

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0 ((crossL [] () () []).map ofL) =
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 (crossL [] () () [])
          (show SChain [up (), up ()] (crossL [] () () []) [up (), up ()] from ⟨rfl, rfl⟩)) ∧
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0 ((crossL [] () () []).map ofL) =
      oddDatum.skmSymmetrizer.d () * oddDatum.toSKM.d () () :=
  TableIsotopyExamples.ordinary_crossing oddDatum.toSKM oddDatum.skmSymmetrizer 0 () ()

example (μ : ℤ) :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer μ [([], .lcup (), [])] =
      if 0 < oddDatum.toSKM.h () μ then
        gsum oddDatum.toSKM oddDatum.skmSymmetrizer μ (dcupL () (oddDatum.toSKM.h () μ - 1).toNat)
      else gsum oddDatum.toSKM oddDatum.skmSymmetrizer μ
        (etaL () (-oddDatum.toSKM.h () μ).toNat ++ lcrossL () ()) :=
  tableDegree_etaP_source oddDatum.toSKM oddDatum.skmSymmetrizer μ ()

example (μ : ℤ) :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer μ [([], .lcap (), [])] =
      if oddDatum.toSKM.h () μ < 0 then
        gsum oddDatum.toSKM oddDatum.skmSymmetrizer μ (dcapL () (-oddDatum.toSKM.h () μ - 1).toNat)
      else gsum oddDatum.toSKM oddDatum.skmSymmetrizer μ
        (lcrossL () () ++ epsL () (oddDatum.toSKM.h () μ).toNat) :=
  tableDegree_epsP_source oddDatum.toSKM oddDatum.skmSymmetrizer μ ()

end NonVacuity.MinimalRewrite

namespace NonVacuity.AdjointCoefficients
open OddMath.CoveringQuantum UDot UDot.GenericTensor Coefficients PreF
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples

example :
    (signLaurent 1 (by norm_num) (sesquilinearForm oddDatum odd_barConsistent
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()]))))).coeff 1 = 1 ∧
    (signLaurent (-1) (by norm_num) (sesquilinearForm oddDatum odd_barConsistent
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()]))))).coeff 1 = -1 :=
  OddMath.CoveringQuantum.UDot.AdjointCoefficientsExamples.repeated_odd_physical_both_signs

example (σ : ℚ) (hσ : σ ^ 2 = 1) :
    (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()]))))).coeff 1 = σ :=
  OddMath.CoveringQuantum.UDot.AdjointCoefficientsExamples.repeated_odd_bent_coeff σ hσ

end NonVacuity.AdjointCoefficients

namespace NonVacuity.CapDotGrading
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositivePointGradingExamples
open OddMath.SKM.CapPushGradingExamples

-- The crossing bound is forced to equality, so both numeric conclusions are used.
example : ∃ E' : List (Move (Letter Bool)),
    Fits 0 E' ∧ Iso (run flipL E') zigzagPairing ∧ E' ≠ [] ∧ ncr E' = 1 ∧
      tableDegree twoColourDatum twoColourSymmetrizer 0 zigzagSource =
        tableDegree twoColourDatum twoColourSymmetrizer 0 (chordLay [] E') ∧
      xpar twoColourDatum 0 zigzagSource = xpar twoColourDatum 0 (chordLay [] E') :=
  zigzag_cap_push

-- The downward dot lies on a fresh cup leg, renamed by the following cap.
example : tableDegree twoColourDatum twoColourSymmetrizer 0
    (dLay [(true, false)] [.tm (.mv (.cup 1 (false, false))), .dt 1, .tm (.cap 0)]) = 2 ∧
    xpar twoColourDatum 0
      (dLay [(true, false)] [.tm (.mv (.cup 1 (false, false))), .dt 1, .tm (.cap 0)]) = 1 :=
  MixedDotGradingExamples.internal_cup_cap_dot twoColourDatum twoColourSymmetrizer 0 false

example :
    let A : List (Letter Bool) := [(true, false)]
    let R : List (TMove (Letter Bool)) := [.mv (.cup 1 (false, false)), .cap 0]
    let T := tRun flipL A.length (tStart A) (R.take 1)
    idD T.st (A.length + 1) = 2 ∧ tRen A.length T (R.drop 1) 2 = 0 :=
  MixedDotGradingExamples.internal_cup_cap_renaming false

end NonVacuity.CapDotGrading

namespace NonVacuity.NormalizedDownAdjoint
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositivePointGradingExamples

example : tableDegree twoColourDatum twoColourSymmetrizer 0 (tLay [(false, false)] []) =
    tableDegree twoColourDatum twoColourSymmetrizer 0
      (tLay [(false, false)] [.mv (.cup 0 (false, false)), .cap 1]) ∧
    xpar twoColourDatum 0 (tLay [(false, false)] []) =
      xpar twoColourDatum 0 (tLay [(false, false)] [.mv (.cup 0 (false, false)), .cap 1]) :=
  TwoSidedGradingExamples.odd_cap_zigzag_normalization

open OddMath.CoveringQuantum UDot UDot.GenericTensor
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.CoveringQuantum.UDot.DownAdjointExamples

example : (signLaurent 1 (by norm_num) downPairing).coeff 1 = 1 ∧
    (signLaurent (-1) (by norm_num) downPairing).coeff 1 = 1 :=
  repeated_odd_down_both_signs

example :
    (signLaurent 1 (by norm_num) (sesquilinearForm oddDatum odd_barConsistent
      (GenericVerma.MixedGram.algebraWord oddDatum 0
        [(false, ()), (true, ()), (true, ())])
      (GenericVerma.MixedGram.algebraWord oddDatum 0 [(true, ())]))).coeff 1 = 1 ∧
    (signLaurent (-1) (by norm_num) (sesquilinearForm oddDatum odd_barConsistent
      (GenericVerma.MixedGram.algebraWord oddDatum 0
        [(false, ()), (true, ()), (true, ())])
      (GenericVerma.MixedGram.algebraWord oddDatum 0 [(true, ())]))).coeff 1 = 1 :=
  ⟨repeated_odd_physical_down_coeff 1 (by norm_num),
    repeated_odd_physical_down_coeff (-1) (by norm_num)⟩

end NonVacuity.NormalizedDownAdjoint

namespace NonVacuity.DecoratedNormalization
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositivePointGradingExamples

example : tableDegree twoColourDatum twoColourSymmetrizer 0
    (dLay [(true, false)] [.tm (.mv (.cup 1 (false, false))), .dt 1, .tm (.cap 0)]) = 2 ∧
    xpar twoColourDatum 0
      (dLay [(true, false)] [.tm (.mv (.cup 1 (false, false))), .dt 1, .tm (.cap 0)]) = 1 :=
  DecoratedNormalizationExamples.odd_internal_cup_cap_normalized_dot

example : tableDegree twoColourDatum twoColourSymmetrizer 0
    (dLay [(true, false), (false, false)] [.dt 1, .tm (.cap 0)]) +
      twoColourSymmetrizer.d false *
        (1 + twoColourDatum.h false (wt twoColourDatum 0 [(false, false)])) = 2 ∧
    xpar twoColourDatum 0 (dLay [(true, false), (false, false)] [.dt 1, .tm (.cap 0)]) = 1 :=
  DecoratedNormalizationExamples.odd_right_cup_cap_normalized_dot

example :
    let A : List (Letter Bool) := [(true, false)]
    let R : List (TMove (Letter Bool)) := [.mv (.cup 1 (false, false)), .cap 0]
    let T := tRun flipL A.length (tStart A) (R.take 1)
    idD T.st (A.length + 1) = 2 ∧ tRen A.length T (R.drop 1) 2 = 0 :=
  DecoratedNormalizationExamples.internal_cup_cap_renaming false

end NonVacuity.DecoratedNormalization

namespace NonVacuity.LeftCupNormalization
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples (oddDatum)

private abbrev A : List (Letter Unit) := [(false, ())]
private abbrev R : List (TMove (Letter Unit)) := [.mv (.cup 1 (true, ())), .cap 0]
private abbrev ds : List (DTMove Unit) := [.tm (.mv (.cup 1 (true, ()))), .dt 2, .tm (.cap 0)]
private abbrev es : List (DTMove Unit) := [.tm (.mv (.cup 0 (true, ()))), .dt 0]

example :
    let T := tRun flipL 1 (tStart A) (R.take 1)
    let U := tRun flipL 0 (tStart ([] : List (Letter Unit)))
      ((leftCupAttachMatching () R).take 2)
    T.nxt = 3 ∧ U.nxt = 2 ∧ idD T.st 3 = 2 ∧ idD U.st 3 = 1 ∧
      tRen 1 T (R.drop 1) 2 = 0 ∧
      tRen 0 U ((leftCupAttachMatching () R).drop 2) 1 = 0 :=
  LeftCupAttachmentExamples.internal_cap_fresh_ids

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2
      (dLay [] (leftCupAttachMoves () ds)) =
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay A ds) - 1 ∧
    xpar oddDatum.toSKM 2 (dLay [] (leftCupAttachMoves () ds)) =
      xpar oddDatum.toSKM 2 (dLay A ds) + 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, hd, hp⟩ := LeftCupAttachmentExamples.internal_cap_odd_shift
  exact ⟨hd, hp⟩

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay [] es) =
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay A ds) - 1 ∧
    xpar oddDatum.toSKM 2 (dLay [] es) = xpar oddDatum.toSKM 2 (dLay A ds) + 1 :=
  LeftCupNormalizationExamples.normalized_internal_cap_odd_shift

example : tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay [] es) = 1 ∧
    xpar oddDatum.toSKM 2 (dLay [] es) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, hd, hp⟩ :=
    LeftCupNormalizationExamples.normalized_internal_cap_values
  exact ⟨hd, hp⟩

end NonVacuity.LeftCupNormalization

namespace NonVacuity.MixedFamilyCoefficients
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples (oddDatum)
open OddMath.SKM.PositiveFormCoefficientsExamples (odd_barConsistent)
open OddMath.CoveringQuantum UDot GenericTensor GenericVerma.MixedGram
open scoped BigOperators

example : Set.Finite {t : MixedFibresExamples.Index |
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (dLay [] (MixedFibresExamples.serializer t.1 t.2)) = 3} ∧
    MixedFibresExamples.oneDot ∈ {t : MixedFibresExamples.Index |
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
        (dLay [] (MixedFibresExamples.serializer t.1 t.2)) = 3} :=
  MixedFibresExamples.cup_degree_three

example : ∃ (L : MixedFibresExamples.Index → List (LayerData Unit))
    (hL : ∀ t, SChain [] (L t) MixedFibresExamples.B),
    (∀ t, Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
      (mkD oddDatum.toSKM 0 (L t) (hL t)) =
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
        (dLay [] (MixedFibresExamples.serializer t.1 t.2))) ∧
    ∀ z : ℤ, Set.Finite {t : MixedFibresExamples.Index |
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 (L t) (hL t)) = z} :=
  MixedFibresExamples.cup_ordinary_fibres

example : ∃ (U : Type) (d : U → ℤ) (p : U → ZMod 2)
    (h : Set.Finite {u | d u = 2}),
    (∑ u ∈ h.toFinset, (1 : ℚ) ^ (p u).val) = 1 ∧
    (∑ u ∈ h.toFinset, (-1 : ℚ) ^ (p u).val) = -1 := by
  classical
  obtain ⟨⟨hp, hpv⟩, ⟨hn, hnv⟩⟩ := CupFamilyCoefficientsExamples.odd_one_dot_signs
  exact ⟨_, _, _, hp, hpv, hnv⟩

example : ∃ (U : Type) (d : U → ℤ) (p : U → ZMod 2)
    (h : Set.Finite {u | d u = 4}),
    (∑ u ∈ h.toFinset, (1 : ℚ) ^ (p u).val) = 1 ∧
    (∑ u ∈ h.toFinset, (-1 : ℚ) ^ (p u).val) = 1 := by
  classical
  obtain ⟨⟨hp, hpv⟩, ⟨hn, hnv⟩⟩ := CupFamilyCoefficientsExamples.odd_two_dot_signs
  exact ⟨_, _, _, hp, hpv, hnv⟩

example :
    (signLaurent 1 (by norm_num) MixedUpAdjointExamples.mixedCupPairing).coeff 2 = 1 ∧
    (signLaurent (-1) (by norm_num) MixedUpAdjointExamples.mixedCupPairing).coeff 2 = -1 ∧
    (signLaurent 1 (by norm_num) MixedUpAdjointExamples.mixedCupPairing).coeff 2 ≠ 0 ∧
    (signLaurent (-1) (by norm_num) MixedUpAdjointExamples.mixedCupPairing).coeff 2 ≠ 0 :=
  MixedUpAdjointExamples.odd_mixed_up_both_signs

example : sesquilinearForm oddDatum odd_barConsistent
    (algebraWord oddDatum 0 [(true, ()), (false, ())])
    (algebraWord oddDatum 0 [(true, ()), (true, ()), (false, ())]) = 0 :=
  MatchingEndpointSupportExamples.form_zero

example (R : List (TMove (Letter Unit))) :
    ¬ IsMatching₂ [(true, ()), (false, ())] [(true, ()), (true, ()), (false, ())] R :=
  MatchingEndpointSupportExamples.no_matching R

example : wt oddDatum.toSKM 7 [] = wt oddDatum.toSKM 7 [(true, ()), (false, ())] :=
  MatchingEndpointSupportExamples.cup_conservation

end NonVacuity.MixedFamilyCoefficients

namespace NonVacuity.LeftCupFamilyCoefficients
open OddMath.SKM
open scoped BigOperators

example : ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ)
    (p : T → ZMod 2) (q : U → ZMod 2)
    (hf : Set.Finite {x | d x = 1}) (hg : Set.Finite {u | e u = 0}),
    (∃ x, d x = 1) ∧ (∃ u, e u = 0) ∧
    (∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val) = -1 ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (q u).val) = 1 ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (q u).val) ≠
      ∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val := by
  classical
  obtain ⟨hf, hg, hx, hu, hs, ht, hne⟩ :=
    LeftCupFamilyCoefficientsExamples.left_cup_negative_sign_distinction
  exact ⟨_, _, _, _, _, _, hf, hg, hx, hu, hs, ht, hne⟩

end NonVacuity.LeftCupFamilyCoefficients

namespace NonVacuity.Claim2Coefficients
open OddMath.SKM OddMath.CoveringQuantum UDot GenericTensor GenericVerma.MixedGram
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples (oddDatum)
open OddMath.SKM.PositiveFormCoefficientsExamples (odd_barConsistent)
open scoped BigOperators

example : ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ)
    (p : T → ZMod 2) (q : U → ZMod 2)
    (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
    (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
    (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
      ((∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 [(true, ()), (false, ())])
        (algebraWord oddDatum 0 []))).coeff z =
          ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
       (∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 [(false, ())])
        (algebraWord oddDatum 0 [(false, ())]))).coeff z =
          ∑ u ∈ (hg z).toFinset, σ ^ (q u).val))) ∧
    (∃ t, d t = 3) ∧ (∃ u, e u = 2) := by
  classical
  obtain ⟨hf, hg, hiff, hcounts⟩ := Claim2CoefficientsExamples.cap_form_coeff_iff
  refine ⟨_, _, _, _, _, _, hf, hg, hiff, ?_, ?_⟩
  · simpa using (hcounts 1 1).1
  · simpa using (hcounts 1 1).2.1

example (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 0 [(true, ()), (true, ()), (false, ())])
      (algebraWord oddDatum 0 [(true, ()), (false, ())]))).coeff z = 0 ∧
    (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 0 [(true, ()), (false, ())])
      (algebraWord oddDatum 0 [(false, ()), (true, ()), (false, ())]))).coeff z = 0 := by
  obtain ⟨_, _, _, hzero⟩ := Claim2MismatchExamples.mismatch_form_coeff_iff
  exact ⟨(hzero σ hσ z).1, (hzero σ hσ z).2.1⟩

end NonVacuity.Claim2Coefficients

namespace NonVacuity.Claim3Coefficients
open OddMath.SKM OddMath.CoveringQuantum UDot GenericTensor GenericVerma.MixedGram
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples (oddDatum)
open OddMath.SKM.PositiveFormCoefficientsExamples (odd_barConsistent)
open scoped BigOperators

example : ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ)
    (p : T → ZMod 2) (q : U → ZMod 2)
    (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
    (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
    (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
      ((∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 [(false, ()), (true, ())])
        (algebraWord oddDatum 0 []))).coeff z =
          ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
       (∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 [(true, ())])
        (algebraWord oddDatum 0 [(true, ())]))).coeff z =
          ∑ u ∈ (hg z).toFinset, σ ^ (q u).val))) ∧
    (∃ t, d t = 1) ∧ (∃ u, e u = 0) ∧
    (∑ t ∈ (hf 1).toFinset, (-1 : ℚ) ^ (p t).val) = -1 ∧
    (∑ u ∈ (hg 0).toFinset, (-1 : ℚ) ^ (q u).val) = 1 := by
  classical
  obtain ⟨hf, hg, hiff, hcounts⟩ := Claim3CoefficientsExamples.cap_form_coeff_iff
  obtain ⟨hx, hu, hs, ht⟩ := hcounts 0 (-1) (by norm_num)
  refine ⟨_, _, _, _, _, _, hf, hg, hiff, ?_, ?_, ?_, ?_⟩
  · simpa using hx
  · simpa using hu
  · simpa [show (1 : ZMod 2).val = 1 from rfl] using hs
  · rw [hs] at ht
    simpa [show (1 : ZMod 2).val = 1 from rfl] using ht

example : ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ)
    (p : T → ZMod 2) (q : U → ZMod 2)
    (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
    (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
    (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
      ((∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 [(false, ())]) (algebraWord oddDatum 0 []))).coeff z =
          ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
       (∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 []) (algebraWord oddDatum 0 [(true, ())]))).coeff z =
          ∑ u ∈ (hg z).toFinset, σ ^ (q u).val))) ∧
    (∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 [(false, ())]) (algebraWord oddDatum 0 []))).coeff z = 0 ∧
      (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 []) (algebraWord oddDatum 0 [(true, ())]))).coeff z = 0 ∧
      (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) = 0 ∧
      (∑ u ∈ (hg z).toFinset, σ ^ (q u).val) = 0) := by
  classical
  obtain ⟨hf, hg, hiff⟩ := Claim3CoefficientsExamples.Mismatch.empty_form_coeff_iff
  exact ⟨_, _, _, _, _, _, hf, hg, hiff, fun σ hσ z =>
    Claim3CoefficientsExamples.Mismatch.empty_coefficients_zero σ hσ z (hf z) (hg z)⟩

end NonVacuity.Claim3Coefficients

namespace NonVacuity.BoundaryCrossing
open StringDiagrams StringDiagrams.Chord OddMath.SKM MixedCrossingLocalExamples

example : tableDegree oddDatum oddSymmetrizer 0 (tLay B S) =
    tableDegree oddDatum oddSymmetrizer 0 (tLay A R) ∧
    xpar oddDatum 0 (tLay B S) = xpar oddDatum 0 (tLay A R) + 1 :=
  BoundaryNormalizationExamples.existing_intersection_normalized

example : ∃ (A B : List (Letter Bool)) (R S : List (StringDiagrams.Chord.TMove (Letter Bool))),
    tableDegree oddDatum oddSymmetrizer 0 (tLay B S) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay A R) ∧
    xpar oddDatum 0 (tLay B S) = xpar oddDatum 0 (tLay A R) + 1 :=
  ⟨_, _, _, _, BoundaryNormalizationExamples.no_intersection_normalized⟩

example : ∃ (qR qS : ℕ → ℕ × ℕ)
    (cR : MatchingStrand A R → ℕ) (cS : MatchingStrand B S → ℕ),
    (∀ j ∈ leftEnds₂ A R, (qR j).1 ≤ R.length ∧ OnStrand₂ A R j (qR j)) ∧
    (∀ j ∈ leftEnds₂ B S, (qS j).1 ≤ S.length ∧ OnStrand₂ B S j (qS j)) ∧
    Decorates₂ A R qR (strandCounts cR) sourceDots ∧
    Decorates₂ B S qS (strandCounts cS) targetDots ∧
    tableDegree oddDatum oddSymmetrizer 0 (dLay B targetDots) = 5 ∧
    tableDegree oddDatum oddSymmetrizer 0 (dLay A sourceDots) = 5 ∧
    xpar oddDatum 0 (dLay B targetDots) = 0 ∧
    xpar oddDatum 0 (dLay A sourceDots) = 1 :=
  ⟨_, _, _, _, BoundaryNormalizationExamples.finite_dotted_normalization⟩

example : (1 : ℚ) ^ (xpar oddDatum 0 (dLay A sourceDots)).val = 1 ∧
    (-1 : ℚ) ^ (xpar oddDatum 0 (dLay A sourceDots)).val = -1 ∧
    (-1 : ℚ) ^ (xpar oddDatum 0 (dLay B targetDots)).val = 1 :=
  signs_detect_factor

end NonVacuity.BoundaryCrossing

namespace NonVacuity.Claim4Coefficients
open OddMath.SKM OddMath.CoveringQuantum UDot GenericTensor GenericVerma.MixedGram
open UDot.ContextualExchangeExamples
open scoped BigOperators

example (k : Bool) :
    let a := (true, false) :: (false, true) ::
      (if k then [(false, false), (true, true)] else [(true, true), (false, false)])
    let b := (false, true) :: (true, false) ::
      (if k then [(false, false), (true, true)] else [(true, true), (false, false)])
    ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ) (p : T → ZMod 2) (q : U → ZMod 2)
      (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
      (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
      (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
        ((∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
          (algebraWord twoOddDatum 0 a) (algebraWord twoOddDatum 0 []))).coeff z =
            ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
         (∀ z : ℤ, (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
          (algebraWord twoOddDatum 0 b) (algebraWord twoOddDatum 0 []))).coeff z =
            ∑ u ∈ (hg z).toFinset, σ ^ (q u).val))) ∧
      (∃ t, d t = 4) ∧ (∃ t, d t = 2) ∧ (∃ u, e u = 2) ∧
      (∀ (σ : ℚ), σ ^ 2 = 1 →
        (∑ t ∈ (hf 2).toFinset, σ ^ (p t).val) = σ ^ (if k then 0 else 1) ∧
        (∑ u ∈ (hg 2).toFinset, σ ^ (q u).val) = σ * σ ^ (if k then 0 else 1)) ∧
      (∑ t ∈ (hf 2).toFinset, (-1 : ℚ) ^ (p t).val) ≠
        ∑ u ∈ (hg 2).toFinset, (-1 : ℚ) ^ (q u).val := by
  classical
  obtain ⟨hf, hg, hiff, hdot, htwo, htwo', hvalues, hne⟩ :=
    Claim4CoefficientsExamples.populated_iff k
  exact ⟨_, _, _, _, _, _, hf, hg, hiff,
    ⟨hdot.choose, hdot.choose_spec.1⟩, htwo, htwo', hvalues, hne⟩

example (k : Bool) : ∃ (T U : Type) (d : T → ℤ) (e : U → ℤ)
    (p : T → ZMod 2) (q : U → ZMod 2)
    (hf : Set.Finite {t | d t = 5}) (hg : Set.Finite {u | e u = 5}),
    (∃ t, d t = 5) ∧ (∃ u, e u = 5) ∧
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p t).val) = (-1 : ℚ) ^ (if k then 1 else 0) ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (q u).val) = -1 * (-1 : ℚ) ^ (if k then 1 else 0) := by
  classical
  obtain ⟨hf, hg, hdot, hu, hs, ht⟩ :=
    BoundaryFamilyExamples.populated_coefficient k (-1) (by norm_num)
  exact ⟨_, _, _, _, _, _, hf, hg, ⟨hdot.choose, hdot.choose_spec.1⟩, hu, hs, ht⟩

example (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
      (algebraWord twoOddDatum 0 [(false, false), (true, false), (false, true), (true, true)])
      (algebraWord twoOddDatum 0 []))).coeff z =
    σ * (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
      (algebraWord twoOddDatum 0 [(false, false), (false, true), (true, false), (true, true)])
      (algebraWord twoOddDatum 0 []))).coeff z :=
  twoOdd_context_coeff σ hσ z

end NonVacuity.Claim4Coefficients

namespace NonVacuity.Claim5Algebra
open OddMath.CoveringQuantum UDot Coefficients GenericTensor GenericVerma.MixedGram
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open UDot.ContextualCommutatorExamples

example :
    sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 0 [(false, ()), (true, ()), (false, ()), (true, ())])
      (algebraWord oddDatum 0 []) -
    Coefficients.pi * sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 0 [(false, ()), (false, ()), (true, ()), (true, ())])
      (algebraWord oddDatum 0 []) =
    (((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) +
      Coefficients.pi * (Coefficients.q : Coefficients.Ring)) *
      sesquilinearForm oddDatum odd_barConsistent
        (algebraWord oddDatum 0 [(false, ()), (true, ())]) (algebraWord oddDatum 0 []) :=
  odd_context_commutator

example :
    sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 2 [(true, ()), (false, ())]) (algebraWord oddDatum 2 []) -
    Coefficients.pi * sesquilinearForm oddDatum odd_barConsistent
      (algebraWord oddDatum 2 [(false, ()), (true, ())]) (algebraWord oddDatum 2 []) ≠
    qpInt Coefficients.q Coefficients.pi 2 := odd_unbarred_commutator_false

example : bar (qpInt Coefficients.q Coefficients.pi 2) ≠ qpInt Coefficients.q Coefficients.pi 2 := odd_two_bar_ne

end NonVacuity.Claim5Algebra

namespace NonVacuity.Claim5MatchingClasses
open StringDiagrams StringDiagrams.Chord OddMath.SKM
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)
open BoundaryExchangeExamples

example :
    tableDegree oddDatum oddSymmetrizer 0 (tLay B S) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay A R) ∧
    xpar oddDatum 0 (tLay B S) = xpar oddDatum 0 (tLay A R) + 1 :=
  existing_intersection_normalized

example :
    tableDegree oddDatum oddSymmetrizer 0 (tLay B₀ S₀) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay A₀ R₀) ∧
    xpar oddDatum 0 (tLay B₀ S₀) = xpar oddDatum 0 (tLay A₀ R₀) + 1 :=
  no_intersection_normalized

example : Ilv (pairing₂ A R) 2 ∧ ¬ Ilv (pairing₂ A₀ R₀) 2 :=
  ⟨existing_intersection, no_existing_intersection⟩

example (ε k : Bool) :
    let a : List (Letter Bool) := if k then [(true, true)] else []
    let b : List (Letter Bool) := if k then [(false, true)] else []
    let C := a ++ (ε, false) :: (!ε, false) :: b
    ∃ (M N : Set (List (TMove (Letter Bool))))
      (E : {V // V ∈ M ∧ Same (pairing₂ C V) b.length (b.length + 1)} ≃ {W // W ∈ N})
      (r : {V // V ∈ M ∧ Same (pairing₂ C V) b.length (b.length + 1)})
      (s : {W // W ∈ N}),
      E.symm (E r) = r ∧ E (E.symm s) = s ∧
      (∀ V, Iso (pairing₂ (a ++ b) (E V).val) (rmAt (pairing₂ C V.val) b.length)) ∧
      (∀ W, Iso (pairing₂ C (E.symm W).val) (capInsertedPairing a b ε false W.val)) := by
  exact ⟨_, _, _, _, _, (CapFamilyExamples.odd_cap_roundtrips ε k).2.1,
    (CapFamilyExamples.odd_cap_roundtrips ε k).2.2, CapFamilyExamples.odd_cap_pairings ε k⟩

end NonVacuity.Claim5MatchingClasses

namespace NonVacuity.Claim5CapAndNoncap
open OddMath.SKM
open OddMath.SKM.NoncapFamilyCoefficientsExamples
open scoped BigOperators

-- A populated coefficient cancellation, with unequal signed coefficients.
example : ∃ (hf : Set.Finite {t : T false | d false t = 2})
    (hg : Set.Finite {u : U false | e false u = 2}),
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p false t).val) = 2 ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' false u).val) = -2 ∧
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p false t).val) +
      (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' false u).val) = 0 ∧
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p false t).val) ≠
      (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' false u).val) := by
  obtain ⟨hf, hg, h1, h2⟩ := (both_signs false).2
  refine ⟨hf, hg, h1, h2, ?_, ?_⟩ <;> rw [h1, h2] <;> norm_num

-- The other intersection branch reverses both signs.
example : ∃ (hf : Set.Finite {t : T true | d true t = 2})
    (hg : Set.Finite {u : U true | e true u = 2}),
    (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p true t).val) = -2 ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' true u).val) = 2 :=
  (both_signs true).2

open StringDiagrams StringDiagrams.Chord
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)

example (ε : Bool) :
    let A : List (Letter Bool) := [(true, true), (ε, false), (!ε, false), (false, true)]
    let R : List (TMove (Letter Bool)) := [.cap 1, .cap 0]
    ∃ (c : MatchingStrand A R → ℕ) (j k : MatchingStrand A R),
      matchingStrandColour A R j = false ∧ matchingStrandColour A R k = true ∧
      c j = 3 ∧ c k = 2 := by
  obtain ⟨j, hj, hc, hcap⟩ := CapStrandsExamples.nonempty_labels ε 3 2
  exact ⟨_, _, _, (CapStrandsExamples.strand_colours ε true).1,
    ((CapStrandsExamples.strand_colours ε true).2 j).trans hj, hcap, hc⟩

example :
    let A : Bool → List (Letter Bool) := fun ε =>
      [(true, false), (ε, false), (!ε, false), (false, false)]
    let B : List (Letter Bool) := [(true, false), (false, false)]
    let R : List (TMove (Letter Bool)) := [.cap 1, .cap 0]
    let S : List (TMove (Letter Bool)) := [.cap 0]
    tableDegree oddDatum oddSymmetrizer 0 (tLay (A true) R) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay B S) + 3 ∧
    xpar oddDatum 0 (tLay (A true) R) = xpar oddDatum 0 (tLay B S) ∧
    tableDegree oddDatum oddSymmetrizer 0 (tLay (A false) R) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay B S) - 1 ∧
    xpar oddDatum 0 (tLay (A false) R) = xpar oddDatum 0 (tLay B S) + 1 :=
  CapNormalizationExamples.odd_nonempty_cap_values

end NonVacuity.Claim5CapAndNoncap

namespace NonVacuity.Claim5DecoratedCap
open StringDiagrams StringDiagrams.Chord OddMath.SKM
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)

-- The closed family consumer supplies both finite fibres and the actual restricted map.
example (ε k : Bool) := CapDecoratedNormalizationExamples.family_fibres ε k

-- Two cap dots and three surviving odd dots at the shifted physical suffix weight.
example : ∃ ds es : List (DTMove Bool),
    tableDegree oddDatum oddSymmetrizer 0
      (dLay [(true, false), (true, false), (false, false), (false, false)] ds) = 14 ∧
    xpar oddDatum 0
      (dLay [(true, false), (true, false), (false, false), (false, false)] ds) = 1 ∧
    tableDegree oddDatum oddSymmetrizer 0
      (dLay [(true, false), (false, false), (true, false), (false, false)] es) = 10 ∧
    xpar oddDatum 0
      (dLay [(true, false), (false, false), (true, false), (false, false)] es) = 0 :=
  ⟨_, _, CapDecoratedNormalizationExamples.nonempty_values⟩

example (ε : Bool) := CapDecoratedNormalizationExamples.nonzero_label_values ε

end NonVacuity.Claim5DecoratedCap

namespace NonVacuity.Claim5CapCoefficients

-- Complete families, independent serializers, and a populated degree-19 fibre.
example (ε : Bool) := OddMath.SKM.CapFamilyCoefficientsExamples.family_coefficients ε

-- Odd weight two distinguishes the corrected scalar from the printed expression.
example := OddMath.CoveringQuantum.CapScalarExamples.odd_two_ne_unbarred
example := OddMath.CoveringQuantum.CapScalarExamples.odd_two_minus_coeff
example := OddMath.CoveringQuantum.CapScalarExamples.odd_two_shifted_coeff

end NonVacuity.Claim5CapCoefficients
