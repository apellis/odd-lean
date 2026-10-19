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
  exact List.map_eq_nil_iff.1 (by simpa [dualW] using h)

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

/-! ### Ellis–Qi, The differential graded odd nilHecke algebra, Theorems 3.18 and 4.17 -/

attribute [local instance] DG.HasDerivedCategory.small DG.CatModule.HasDerivedCategory.small

example := OddMath.Frontier.EQK0.thm_3_18_equiv_one ℚ

example (n : ℕ) := OddMath.Frontier.EQK0.thm_4_17_equiv_E ℚ n

end NonVacuity
