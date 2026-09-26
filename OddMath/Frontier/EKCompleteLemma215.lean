import OddMath.Frontier.EKFinalClosure
import OddMath.Frontier.EKNondegeneracyAudit

/-!
# [EK] Lemma 2.15 for every λ, and the characterisation of `s_λ` on pp. 28–29

Source: Ellis–Khovanov, arXiv:1107.5610v2.
* Lemma 2.15 (p. 18): for every `λ ⊢ n` the form is nondegenerate on `H_{≥λ}` and on `E_{>λᵀ}`.
  The printed proof shows that the restricted Gram determinants are `±1`.
* p. 28, before (3.12), and p. 29: the Schur functions are uniquely determined by
  (1) `(s_λ, h_μ) = 0` for `μ > λ` (lexicographic order), and
  (2) `s_λ = h_λ + Σ_{μ>λ} a_μ h_μ` for certain integers `a_μ`.

The printed proof of Lemma 2.15 uses `(H_{≥λ})^⊥ = E_{>λᵀ}`, which is false
(`EKRestrictedPairing.complement_equality_false`). Here the lemma is derived from Cor 3.9
(`EKClosureComposition.corollary_3_9`) instead. For any lex-upward-closed set `P` of partitions
of `d`:
* `span{h_μ : μ ∈ P} = span{s_μ : μ ∈ P}` (`hSpan_eq_sSpan`): `s_μ − h_μ` is a combination of
  `h_ν` with `ν` strictly dominating `μ` (`EKProp310.schur_sub_mem_upS`), and conversely
  `K_{κμ} ≠ 0` forces `κ ⊵ μ`;
* `span{e_μ : μ ∈ P} = span{s_ρ : ρᵀ ∈ P}` (`eSpan_eq_sTSpan`), by `EKProp310.schur_sub_e_mem`
  and Prop 2.14;
* the Schur functions are signed-orthonormal (Cor 3.9), so each Gram matrix `G` satisfies
  `Aᵀ G A = diag(±1)` for an integer matrix `A`, and `det G = ±1`.

Main statements: `lemma_2_15`, `lemma_2_15_det`, `Hge_eq_schur_span`, `Hgt_nondeg`,
`Egt_nondeg`, `Egt_det`, `Ege_det`, `schur_characterisation`, `schur_existsUnique`.

Lexicographic order is `List.Lex (· < ·)` on row lengths, as in `EKTriangular.Hge` and
`EKRestrictedPairing.Egt`; it agrees definitionally with `EKProp310.LexLT`.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKComplete
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKPartitionSpanning (hPartition ePartition)
open EKNondegeneracy (RestrictedNondeg)

local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## Gram determinants of families related to a signed-orthonormal family -/

/-- The Gram matrix of a finite family in `Q`. -/
def gram {ι : Type*} (v : ι → Q) : Matrix ι ι ℤ :=
  Matrix.of fun i j => quotientPairing (v i) (v j)

/-- If `w_i = Σ_j A_{ji} v_j` and `(w_i, w_j) = ε_i δ_{ij}` with every `ε_i` a unit, then the
Gram determinant of `v` is a unit. -/
theorem gram_det_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] (v w : ι → Q)
    (A : Matrix ι ι ℤ) (hw : ∀ i, w i = ∑ j, A j i • v j) (ε : ι → ℤ) (hε : ∀ i, IsUnit (ε i))
    (hG : ∀ i j, quotientPairing (w i) (w j) = if i = j then ε i else 0) :
    IsUnit (gram v).det := by
  have hmat : A.transpose * gram v * A = Matrix.diagonal ε := by
    ext i j
    rw [Matrix.diagonal_apply, ← hG i j, hw i, hw j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, gram, Matrix.of_apply, map_sum,
      map_zsmul, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hd := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hd
  have hu : IsUnit (∏ i, ε i) := IsUnit.prod_univ_iff.mpr hε
  rw [← hd] at hu
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)

theorem int_isUnit_iff (u : ℤ) : IsUnit u ↔ u = 1 ∨ u = -1 := Int.isUnit_iff

theorem neg_one_pow_isUnit (n : ℕ) : IsUnit ((-1 : ℤ) ^ n) :=
  ((int_isUnit_iff _).mpr (Or.inr rfl)).pow n

/-- A span with unit Gram determinant is nondegenerate. -/
theorem nondeg_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → Q)
    (h : IsUnit (gram v).det) : RestrictedNondeg (Submodule.span ℤ (Set.range v)) :=
  EKNondegeneracy.nondeg_of_gram_det v (h.ne_zero)

/-! ## Lex-upward-closed index sets -/

/-- `P` is closed upwards in the lexicographic order on partitions of `d`. -/
def LexUpClosed (d : ℕ) (P : DegreeShape d → Prop) : Prop :=
  ∀ μ ν : DegreeShape d, P μ → EKProp310.LexLT μ.val ν.val → P ν

/-- The partitions of `d` in `P`, as an index type. -/
abbrev Idx (d : ℕ) (P : DegreeShape d → Prop) := {μ : DegreeShape d // P μ}

open Classical in
instance (d : ℕ) (P : DegreeShape d → Prop) : Fintype (Idx d P) := Subtype.fintype _

/-- `h_μ`, `μ ∈ P`. -/
def hFam (d : ℕ) (P : DegreeShape d → Prop) (i : Idx d P) : Q := hPartition i.val.val

/-- `e_μ`, `μ ∈ P`. -/
def eFam (d : ℕ) (P : DegreeShape d → Prop) (i : Idx d P) : Q := ePartition i.val.val

/-- `s_μ`, `μ ∈ P`. -/
def sFam (d : ℕ) (P : DegreeShape d → Prop) (i : Idx d P) : Q :=
  (EKSchurOrthonormal.schur d i.val : Q)

/-- `s_{μᵀ}`, `μ ∈ P`. -/
def sTFam (d : ℕ) (P : DegreeShape d → Prop) (i : Idx d P) : Q :=
  (EKSchurOrthonormal.schur d (transposeShape d i.val) : Q)

/-- The sign `(-1)^{C(λᵀ,2)}` of Cor 3.9. -/
def eps (lam : YoungDiagram) : ℤ := (-1 : ℤ) ^ EKSchurOrthonormalControls.transposeChoose lam

theorem sFam_gram (d : ℕ) (P : DegreeShape d → Prop) (i j : Idx d P) :
    quotientPairing (sFam d P i) (sFam d P j) = if i = j then eps i.val.val else 0 := by
  rw [sFam, sFam, EKClosureComposition.corollary_3_9]
  by_cases h : i = j
  · subst h; simp [eps]
  · have h' : i.val ≠ j.val := fun e => h (Subtype.ext e)
    simp [h, h']

theorem sTFam_gram (d : ℕ) (P : DegreeShape d → Prop) (i j : Idx d P) :
    quotientPairing (sTFam d P i) (sTFam d P j) =
      if i = j then eps (transposeShape d i.val).val else 0 := by
  rw [sTFam, sTFam, EKClosureComposition.corollary_3_9]
  by_cases h : i = j
  · subst h; simp [eps]
  · have h' : transposeShape d i.val ≠ transposeShape d j.val :=
      fun e => h (Subtype.ext ((transposeShape d).injective e))
    simp [h, h']

/-- `s_ν ∈ span{h_μ : μ ∈ P}` for `ν ∈ P`. -/
theorem schur_mem_hSpan {d : ℕ} {P : DegreeShape d → Prop} (hP : LexUpClosed d P)
    (ν : Idx d P) : sFam d P ν ∈ Submodule.span ℤ (Set.range (hFam d P)) := by
  set T := Submodule.span ℤ (Set.range (hFam d P))
  have hle : EKProp310.UpS d ν.val ≤ T.comap (degreePiece d).subtype := by
    rw [EKProp310.UpS, Submodule.span_le]
    rintro _ ⟨ρ, ⟨hdom, hne⟩, rfl⟩
    rcases EKProp310.lex_le_of_dom hdom with he | hl
    · exact absurd (Subtype.ext he).symm hne
    · exact Submodule.subset_span ⟨⟨ρ, hP _ _ ν.property hl⟩, by
        simp [hFam, degreeHBasis_apply]⟩
  have h1 := hle (EKProp310.schur_sub_mem_upS d ν.val)
  have h2 : hFam d P ν ∈ T := Submodule.subset_span ⟨ν, rfl⟩
  have h3 := T.add_mem h1 h2
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
    degreeHBasis_apply] at h3
  rw [hFam, sub_add_cancel] at h3
  exact h3

/-- `s_{νᵀ} ∈ span{e_μ : μ ∈ P}` for `ν ∈ P`. -/
theorem schurT_mem_eSpan {d : ℕ} {P : DegreeShape d → Prop} (hP : LexUpClosed d P)
    (ν : Idx d P) : sTFam d P ν ∈ Submodule.span ℤ (Set.range (eFam d P)) := by
  set T := Submodule.span ℤ (Set.range (eFam d P))
  set ρ := transposeShape d ν.val with hρ
  have hρT : transposeShape d ρ = ν.val := by
    apply Subtype.ext
    simp [hρ, EKProp310.transposeShape_val, YoungDiagram.transpose_transpose]
  have hle : EKProp310.EAbove d ρ.val.transpose ≤ T.comap (degreePiece d).subtype := by
    rw [EKProp310.EAbove, Submodule.span_le]
    rintro _ ⟨μ, hμ, rfl⟩
    have hν : ρ.val.transpose = ν.val.val := by rw [← EKProp310.transposeShape_val, hρT]
    rw [Set.mem_setOf_eq, hν] at hμ
    exact Submodule.subset_span ⟨⟨μ, hP _ _ ν.property hμ⟩, by
      simp [eFam, degreeEBasis_apply]⟩
  have h1 := hle (EKProp310.schur_sub_e_mem d (EKClosureComposition.identity311 d) ρ)
  have h2 : eFam d P ν ∈ T := Submodule.subset_span ⟨ν, rfl⟩
  have h3 := T.add_mem h1 (T.smul_mem (EKProp310.sgn ρ.val) h2)
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
    Submodule.coe_smul, degreeEBasis_apply, hρT] at h3
  rw [eFam, sub_add_cancel] at h3
  exact h3

theorem coeffs_of_mem {ι : Type*} [Fintype ι] (v w : ι → Q)
    (h : ∀ i, w i ∈ Submodule.span ℤ (Set.range v)) :
    ∃ A : Matrix ι ι ℤ, ∀ i, w i = ∑ j, A j i • v j := by
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (h i)
  exact ⟨fun j i => c i j, fun i => (hc i).symm⟩

/-- **Gram determinant on `span{h_μ : μ ∈ P}`** is `±1` for every lex-upward-closed `P`. -/
theorem hGram_det {d : ℕ} {P : DegreeShape d → Prop} (hP : LexUpClosed d P) :
    (gram (hFam d P)).det = 1 ∨ (gram (hFam d P)).det = -1 := by
  obtain ⟨A, hA⟩ := coeffs_of_mem (hFam d P) (sFam d P) (schur_mem_hSpan hP)
  exact (int_isUnit_iff _).mp (gram_det_isUnit _ _ A hA _
    (fun i => neg_one_pow_isUnit _) (sFam_gram d P))

/-- **Gram determinant on `span{e_μ : μ ∈ P}`** is `±1` for every lex-upward-closed `P`. -/
theorem eGram_det {d : ℕ} {P : DegreeShape d → Prop} (hP : LexUpClosed d P) :
    (gram (eFam d P)).det = 1 ∨ (gram (eFam d P)).det = -1 := by
  obtain ⟨A, hA⟩ := coeffs_of_mem (eFam d P) (sTFam d P) (schurT_mem_eSpan hP)
  exact (int_isUnit_iff _).mp (gram_det_isUnit _ _ A hA _
    (fun i => neg_one_pow_isUnit _) (sTFam_gram d P))

theorem hSpan_nondeg {d : ℕ} {P : DegreeShape d → Prop} (hP : LexUpClosed d P) :
    RestrictedNondeg (Submodule.span ℤ (Set.range (hFam d P))) :=
  nondeg_of_isUnit _ ((int_isUnit_iff _).mpr (hGram_det hP))

theorem eSpan_nondeg {d : ℕ} {P : DegreeShape d → Prop} (hP : LexUpClosed d P) :
    RestrictedNondeg (Submodule.span ℤ (Set.range (eFam d P))) :=
  nondeg_of_isUnit _ ((int_isUnit_iff _).mpr (eGram_det hP))

/-- `span{h_μ : μ ∈ P} = span{s_μ : μ ∈ P}` (Kostka unitriangularity, (3.6)). -/
theorem hSpan_eq_sSpan {d : ℕ} {P : DegreeShape d → Prop} (hP : LexUpClosed d P) :
    Submodule.span ℤ (Set.range (hFam d P)) = Submodule.span ℤ (Set.range (sFam d P)) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr (Set.range_subset_iff.mpr (schur_mem_hSpan hP)))
  rw [Submodule.span_le]
  rintro _ ⟨μ, rfl⟩
  rw [SetLike.mem_coe, hFam, ← degreeHBasis_apply, EKSchurOrthonormal.schur_defining,
    Submodule.coe_sum]
  refine Submodule.sum_mem _ fun κ _ => ?_
  by_cases hK : signedKostka κ.val μ.val.val = 0
  · rw [hK, zero_smul]; exact Submodule.zero_mem _
  rw [Submodule.coe_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨κ, ?_⟩, rfl⟩)
  rcases EKProp310.lex_le_of_dom (EKProp310.dom_of_kostka_ne_zero hK) with he | hl
  · rw [show κ = μ.val from (Subtype.ext he).symm]; exact μ.property
  · exact hP _ _ μ.property hl

/-- `span{e_μ : μ ∈ P} = span{s_ρ : ρᵀ ∈ P}` ((3.11) and Prop 2.14). -/
theorem eSpan_eq_sTSpan {d : ℕ} {P : DegreeShape d → Prop} (hP : LexUpClosed d P) :
    Submodule.span ℤ (Set.range (eFam d P)) = Submodule.span ℤ (Set.range (sTFam d P)) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr (Set.range_subset_iff.mpr (schurT_mem_eSpan hP)))
  rw [Submodule.span_le]
  rintro _ ⟨μ, rfl⟩
  have hx := congrArg Subtype.val (EKProp310.expansion d (EKClosureComposition.identity311 d)
    (degreeEBasis d μ.val))
  rw [SetLike.mem_coe, eFam, ← degreeEBasis_apply, hx, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun κ _ => ?_
  rw [Submodule.coe_smul]
  by_cases hk : EKProp310.LexLT κ.val.transpose μ.val.val
  · rw [degreeEBasis_apply, EKProp310.pair_schur_e_vanish d κ μ.val hk, mul_zero, zero_smul]
    exact Submodule.zero_mem _
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨transposeShape d κ, ?_⟩, ?_⟩)
  · rcases EKProp310.lexLT_trichotomy μ.val.val κ.val.transpose with hl | he | hl
    · exact hP _ _ μ.property hl
    · rw [show transposeShape d κ = μ.val from Subtype.ext he.symm]; exact μ.property
    · exact absurd hl hk
  · simp only [sTFam]
    congr 2
    apply Subtype.ext
    simp [YoungDiagram.transpose_transpose]

/-! ## The four source subspaces -/

/-- Index predicate of `H_{≥λ}` (lexicographic, `|μ| = |λ|`). -/
def PGe (lam : YoungDiagram) (μ : DegreeShape lam.card) : Prop :=
  μ.val = lam ∨ List.Lex (· < ·) lam.rowLens μ.val.rowLens

/-- Index predicate of strict lexicographic order above a fixed diagram `κ`. -/
def PGt (d : ℕ) (κ : YoungDiagram) (μ : DegreeShape d) : Prop :=
  List.Lex (· < ·) κ.rowLens μ.val.rowLens

/-- Index predicate of lexicographic order at or above a fixed diagram `κ`. -/
def PGe' (d : ℕ) (κ : YoungDiagram) (μ : DegreeShape d) : Prop :=
  μ.val = κ ∨ List.Lex (· < ·) κ.rowLens μ.val.rowLens

theorem PGe_closed (lam : YoungDiagram) : LexUpClosed lam.card (PGe lam) := by
  rintro μ ν (h | h) hl
  · right
    have hl' : List.Lex (· < ·) μ.val.rowLens ν.val.rowLens := hl
    rwa [h] at hl'
  · right; exact lt_trans (α := List ℕ) h hl

theorem PGt_closed (d : ℕ) (κ : YoungDiagram) : LexUpClosed d (PGt d κ) :=
  fun _ _ h hl => lt_trans (α := List ℕ) h hl

theorem PGe'_closed (d : ℕ) (κ : YoungDiagram) : LexUpClosed d (PGe' d κ) := by
  rintro μ ν (h | h) hl
  · right
    have hl' : List.Lex (· < ·) μ.val.rowLens ν.val.rowLens := hl
    rwa [h] at hl'
  · right; exact lt_trans (α := List ℕ) h hl

/-- Source `H_{>λ}` (lexicographic), in the notation of p. 18. -/
def Hgt (lam : YoungDiagram) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ ν : YoungDiagram, ν.card = lam.card ∧
    List.Lex (· < ·) lam.rowLens ν.rowLens ∧ hPartition ν = x}

/-- Source `E_{≥κ}` in degree `d` (lexicographic), in the notation of p. 18. -/
def Ege (d : ℕ) (κ : YoungDiagram) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ ν : YoungDiagram, ν.card = d ∧
    (ν = κ ∨ List.Lex (· < ·) κ.rowLens ν.rowLens) ∧ ePartition ν = x}

theorem Hge_eq (lam : YoungDiagram) :
    EKTriangular.Hge lam = Submodule.span ℤ (Set.range (hFam lam.card (PGe lam))) := by
  unfold EKTriangular.Hge
  congr 1
  ext x
  constructor
  · rintro ⟨ν, hd, hl, rfl⟩
    exact ⟨⟨⟨ν, hd⟩, hl⟩, rfl⟩
  · rintro ⟨⟨ν, hl⟩, rfl⟩
    exact ⟨ν.val, ν.property, hl, rfl⟩

theorem Hgt_eq (lam : YoungDiagram) :
    Hgt lam = Submodule.span ℤ (Set.range (hFam lam.card (PGt lam.card lam))) := by
  unfold Hgt
  congr 1
  ext x
  constructor
  · rintro ⟨ν, hd, hl, rfl⟩
    exact ⟨⟨⟨ν, hd⟩, hl⟩, rfl⟩
  · rintro ⟨⟨ν, hl⟩, rfl⟩
    exact ⟨ν.val, ν.property, hl, rfl⟩

theorem Egt_eq (d : ℕ) (lam : YoungDiagram) :
    EKRestrictedPairing.Egt d lam =
      Submodule.span ℤ (Set.range (eFam d (PGt d lam.transpose))) := by
  unfold EKRestrictedPairing.Egt
  congr 1
  ext x
  constructor
  · rintro ⟨ν, hd, hl, rfl⟩
    exact ⟨⟨⟨ν, hd⟩, hl⟩, rfl⟩
  · rintro ⟨⟨ν, hl⟩, rfl⟩
    exact ⟨ν.val, ν.property, hl, rfl⟩

theorem Ege_eq (d : ℕ) (κ : YoungDiagram) :
    Ege d κ = Submodule.span ℤ (Set.range (eFam d (PGe' d κ))) := by
  unfold Ege
  congr 1
  ext x
  constructor
  · rintro ⟨ν, hd, hl, rfl⟩
    exact ⟨⟨⟨ν, hd⟩, hl⟩, rfl⟩
  · rintro ⟨⟨ν, hl⟩, rfl⟩
    exact ⟨ν.val, ν.property, hl, rfl⟩

/-- **EK Lemma 2.15** (p. 18), every `λ`: the form is nondegenerate on `H_{≥λ}` and on
`E_{>λᵀ}` (in degree `|λ|`). -/
theorem lemma_2_15 (lam : YoungDiagram) :
    RestrictedNondeg (EKTriangular.Hge lam) ∧
      RestrictedNondeg (EKRestrictedPairing.Egt lam.card lam) := by
  rw [Hge_eq, Egt_eq]
  exact ⟨hSpan_nondeg (PGe_closed lam), eSpan_nondeg (PGt_closed _ _)⟩

/-- **EK Lemma 2.15, determinant form** (the conclusion of the printed proof, p. 18): the Gram
matrices of `{h_μ : μ ≥ λ}` and `{e_μ : μ > λᵀ}` have determinant `±1`. -/
theorem lemma_2_15_det (lam : YoungDiagram) :
    ((gram (hFam lam.card (PGe lam))).det = 1 ∨ (gram (hFam lam.card (PGe lam))).det = -1) ∧
    ((gram (eFam lam.card (PGt lam.card lam.transpose))).det = 1 ∨
      (gram (eFam lam.card (PGt lam.card lam.transpose))).det = -1) :=
  ⟨hGram_det (PGe_closed lam), eGram_det (PGt_closed _ _)⟩

/-- `H_{≥λ} = span{s_μ : μ ≥ λ}` (lexicographic). -/
theorem Hge_eq_schur_span (lam : YoungDiagram) :
    EKTriangular.Hge lam = Submodule.span ℤ (Set.range (sFam lam.card (PGe lam))) := by
  rw [Hge_eq]; exact hSpan_eq_sSpan (PGe_closed lam)

/-- `E_{>λᵀ} = span{s_ρ : ρᵀ > λᵀ}` (lexicographic), in degree `|λ|`. -/
theorem Egt_eq_schur_span (lam : YoungDiagram) :
    EKRestrictedPairing.Egt lam.card lam =
      Submodule.span ℤ (Set.range (sTFam lam.card (PGt lam.card lam.transpose))) := by
  rw [Egt_eq]; exact eSpan_eq_sTSpan (PGt_closed _ _)

/-- `H_{>λ}`: Gram determinant `±1`. -/
theorem Hgt_det (lam : YoungDiagram) :
    (gram (hFam lam.card (PGt lam.card lam))).det = 1 ∨
      (gram (hFam lam.card (PGt lam.card lam))).det = -1 :=
  hGram_det (PGt_closed _ _)

theorem Hgt_nondeg (lam : YoungDiagram) : RestrictedNondeg (Hgt lam) := by
  rw [Hgt_eq]; exact hSpan_nondeg (PGt_closed _ _)

/-- `E_{>κ}` in any degree `d`, any `κ`: Gram determinant `±1`. -/
theorem Egt_det (d : ℕ) (κ : YoungDiagram) :
    (gram (eFam d (PGt d κ))).det = 1 ∨ (gram (eFam d (PGt d κ))).det = -1 :=
  eGram_det (PGt_closed _ _)

/-- `E_{≥κ}` in any degree `d`, any `κ`: Gram determinant `±1`. -/
theorem Ege_det (d : ℕ) (κ : YoungDiagram) :
    (gram (eFam d (PGe' d κ))).det = 1 ∨ (gram (eFam d (PGe' d κ))).det = -1 :=
  eGram_det (PGe'_closed _ _)

theorem Ege_nondeg (d : ℕ) (κ : YoungDiagram) : RestrictedNondeg (Ege d κ) := by
  rw [Ege_eq]; exact eSpan_nondeg (PGe'_closed _ _)

/-- `E_{>κ}` is nondegenerate in every degree, for every `κ` (not only `κ = λᵀ`, `|λ| = d`). -/
theorem Egt_nondeg (d : ℕ) (lam : YoungDiagram) :
    RestrictedNondeg (EKRestrictedPairing.Egt d lam) := by
  rw [Egt_eq]; exact eSpan_nondeg (PGt_closed _ _)

/-! ## The characterisation of `s_λ` (p. 28, properties (1)–(2); p. 29) -/

open Classical in
/-- Properties (1) and (2) preceding (3.12), for an arbitrary `x ∈ Λ`. -/
def IsSchurChar (d : ℕ) (lam : DegreeShape d) (x : Q) : Prop :=
  (∀ μ : DegreeShape d, List.Lex (· < ·) lam.val.rowLens μ.val.rowLens →
      quotientPairing x (hPartition μ.val) = 0) ∧
  ∃ a : DegreeShape d → ℤ, x = hPartition lam.val +
    ∑ μ ∈ Finset.univ.filter (fun μ : DegreeShape d =>
      List.Lex (· < ·) lam.val.rowLens μ.val.rowLens), a μ • hPartition μ.val

/-- Property (1) for `s_λ`: `(s_λ, h_μ) = 0` for `μ > λ`. -/
theorem schur_pair_h_gt (d : ℕ) (lam μ : DegreeShape d)
    (h : List.Lex (· < ·) lam.val.rowLens μ.val.rowLens) :
    quotientPairing (EKSchurOrthonormal.schur d lam : Q) (hPartition μ.val) = 0 := by
  rw [← degreeHBasis_apply, EKSchurOrthonormal.schur_defining, Submodule.coe_sum, map_sum]
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [Submodule.coe_smul, map_zsmul, EKClosureComposition.corollary_3_9, smul_eq_mul]
  by_cases hk : lam = κ
  · subst hk
    have hK : signedKostka lam.val μ.val = 0 := by
      by_contra hK
      rcases EKProp310.lex_le_of_dom (EKProp310.dom_of_kostka_ne_zero hK) with he | hl
      · rw [he] at h; exact lt_irrefl (α := List ℕ) _ h
      · exact lt_asymm (α := List ℕ) h hl
    rw [hK, zero_mul]
  · rw [if_neg hk, mul_zero]

/-- `s_λ − h_λ ∈ H_{>λ}`. -/
theorem schur_sub_mem_Hgt (d : ℕ) (lam : DegreeShape d) :
    (EKSchurOrthonormal.schur d lam : Q) - hPartition lam.val ∈
      Submodule.span ℤ (Set.range (hFam d (PGt d lam.val))) := by
  set T := Submodule.span ℤ (Set.range (hFam d (PGt d lam.val)))
  have hle : EKProp310.UpS d lam ≤ T.comap (degreePiece d).subtype := by
    rw [EKProp310.UpS, Submodule.span_le]
    rintro _ ⟨ρ, ⟨hdom, hne⟩, rfl⟩
    rcases EKProp310.lex_le_of_dom hdom with he | hl
    · exact absurd (Subtype.ext he).symm hne
    · exact Submodule.subset_span ⟨⟨ρ, hl⟩, by simp [hFam, degreeHBasis_apply]⟩
  have h1 := hle (EKProp310.schur_sub_mem_upS d lam)
  simpa only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
    degreeHBasis_apply] using h1

theorem schur_isSchurChar (d : ℕ) (lam : DegreeShape d) :
    IsSchurChar d lam (EKSchurOrthonormal.schur d lam : Q) := by
  refine ⟨fun μ hμ => schur_pair_h_gt d lam μ hμ, ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (schur_sub_mem_Hgt d lam)
  classical
  refine ⟨fun μ => if h : List.Lex (· < ·) lam.val.rowLens μ.val.rowLens then c ⟨μ, h⟩ else 0, ?_⟩
  rw [eq_add_of_sub_eq' hc.symm]
  congr 1
  rw [Finset.sum_subtype _ (p := PGt d lam.val) (fun μ => by simp [PGt])]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : List.Lex (· < ·) lam.val.rowLens i.val.val.rowLens := i.property
  simp only [hi, dif_pos, hFam]

/-- **p. 28–29: properties (1)–(2) characterise `s_λ`.** An element `x ∈ Λ` satisfies
`(x, h_μ) = 0` for all `μ > λ` and `x ∈ h_λ + Σ_{μ>λ} ℤ h_μ` if and only if `x = s_λ`. -/
theorem schur_characterisation (d : ℕ) (lam : DegreeShape d) (x : Q) :
    IsSchurChar d lam x ↔ x = (EKSchurOrthonormal.schur d lam : Q) := by
  refine ⟨fun hx => ?_, fun hx => hx ▸ schur_isSchurChar d lam⟩
  set T := Submodule.span ℤ (Set.range (hFam d (PGt d lam.val)))
  have hs := schur_isSchurChar d lam
  have hxT : x - hPartition lam.val ∈ T := by
    obtain ⟨a, ha⟩ := hx.2
    rw [ha, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun μ hμ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨⟨μ, (Finset.mem_filter.mp hμ).2⟩, rfl⟩
  have hy : x - (EKSchurOrthonormal.schur d lam : Q) ∈ T := by
    have := T.sub_mem hxT (schur_sub_mem_Hgt d lam)
    rwa [sub_sub_sub_cancel_right] at this
  have hperp : ∀ z ∈ T, quotientPairing (x - (EKSchurOrthonormal.schur d lam : Q)) z = 0 := by
    intro z hz
    have hle : T ≤ LinearMap.ker (quotientPairing (x - (EKSchurOrthonormal.schur d lam : Q))) := by
      rw [Submodule.span_le]
      rintro _ ⟨μ, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, hFam, map_sub, LinearMap.sub_apply,
        hx.1 μ.val μ.property, hs.1 μ.val μ.property, sub_zero]
    exact hle hz
  exact sub_eq_zero.mp (hSpan_nondeg (PGt_closed d lam.val) _ hy hperp)

/-- The characterisation as unique existence. -/
theorem schur_existsUnique (d : ℕ) (lam : DegreeShape d) : ∃! x : Q, IsSchurChar d lam x :=
  ⟨_, schur_isSchurChar d lam, fun x hx => (schur_characterisation d lam x).mp hx⟩

end OddMath.Frontier.EKComplete
