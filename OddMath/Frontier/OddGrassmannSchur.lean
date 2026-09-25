import OddMath.Frontier.OddSymmetricLimit
import OddMath.Frontier.EKFinalClosure
import OddMath.Frontier.Cyclotomic
import OddMath.Frontier.BoxPartitionCount

/-!
# Odd Schur functions and the odd Grassmannian ring

EKL arXiv:1111.1320v1, §5, pp. 44–46.

Carriers: `Q = EKRadicalQuotient.Q` is OΛ; `piN N` is OΛ → OΛ_N; `sK λ` is `s^H_λ` ((5.10));
`Cyclotomic.OH n N` is `OH_{a,N} = OΛ_a/⟨h_m : m > N − a⟩` (p. 44), `a = n+2`.

* Conjecture 5.3 (p. 46) is a theorem for every `a ≥ 2` (`conjecture_5_3`); in each degree the
  odd Schur polynomials with at most `a` rows form a ℤ-basis of OΛ_a (`oddSchurPolynomialBasis`).
* `sBasis`: the `s^H_λ` form a ℤ-basis of OΛ (p. 46).
* `mem_hIdeal_iff_mem_wideSchurSpan`: `⟨h_m : m > b⟩ ⊂ OΛ` is the ℤ-span of the `s^H_λ` with more
  than `b` columns (via EK's `ψ₁ψ₂`, EK Lemma 3.11).
* Proposition 5.4 (p. 46): `proposition_5_4` is a ℤ-basis of `OH_{a,N}` indexed by the partitions
  in the `a × (N − a)` box, with basis vectors the images of the `s^H_λ` (equivalently of the odd
  Schur polynomials `s_λ`), and `toOHQ_sK_eq_zero` gives the vanishing of the other `s^H_λ`.
  The printed proof invokes freeness of `OH_{a,N}` without proof; here the kernel of
  OΛ → OH_{a,N} is identified with the ℤ-span of the `s^H_λ`, `λ ⊄ a × (N − a)`
  (`toOHQ_eq_zero_iff`, `mem_boxIdeal_iff`), from which freeness follows.
  `finrank_OH`: the rank is `C(N, a)`.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace OddMath.Frontier.OddGrassmannSchur

open OddMath.SkewPolynomial
open EKRadicalQuotient (Q)
open OddLREKIdentification (piN sK schurK)
open DegreeShapes (DegreeShape)
open EKPartitionSpanning (ePartition hPartition)
open OddSymmetricLimit

attribute [local instance] DegreeShapes.degreeFintype

/-! ## Conjecture 5.3 -/

/-- **EKL Conjecture 5.3** (p. 46), a theorem for every `a = n+2 ≥ 2`: the image of `s^H_λ` under
OΛ → OΛ_a is the odd Schur polynomial `s_λ` (EKL (2.69)) when `λ` has at most `a` rows, and `0`
otherwise. -/
theorem conjecture_5_3 (n : ℕ) (lam : YoungDiagram) :
    piN (n+2) (sK lam) =
      if lam.colLen 0 ≤ n + 2 then
        OddSymmetrizer.schur n (OddLREKIdentification.toExponent n lam)
      else 0 := by
  split_ifs with h
  · exact OddLRThm38.sK_eq_schur n lam h
  · exact (OddLRThm38.thm38_tall (n+2) lam (Nat.lt_of_not_le h)).1

/-- In each degree `d`, the odd Schur polynomials `s_λ = π_a(s^H_λ)` with at most `a` rows form a
ℤ-basis of the degree-`d` piece of OΛ_a (`a = n+2`). -/
def oddSchurPolynomialBasis (n d : ℕ) :
    Basis {lam : DegreeShape d // lam.val.colLen 0 ≤ n+2} ℤ (ElementaryBasis.degreePiece n d) :=
  Basis.mk (v := fun lam => degreeMap n d (schurK d lam.1))
    (LinearIndependent.of_comp (ElementaryBasis.degreePiece n d).subtype
      (piN_schurK_degree_linearIndependent (n+2) d))
    (by
      rintro y -
      obtain ⟨x, rfl⟩ := degreeMap_surjective n d y
      rw [← (schurBasis d).sum_repr x, map_sum]
      apply Submodule.sum_mem
      intro lam _
      rw [map_zsmul, schurBasis_apply]
      apply Submodule.smul_mem
      by_cases hl : lam.val.colLen 0 ≤ n+2
      · exact Submodule.subset_span ⟨⟨lam, hl⟩, rfl⟩
      · have : degreeMap n d (schurK d lam) = 0 :=
          Subtype.ext (piN_schurK_tall (N := n+2) (by omega))
        rw [this]
        exact zero_mem _)

theorem oddSchurPolynomialBasis_apply (n d : ℕ)
    (lam : {lam : DegreeShape d // lam.val.colLen 0 ≤ n+2}) :
    (oddSchurPolynomialBasis n d lam : SkewPolynomial (n+2)) =
      OddSymmetrizer.schur n (OddLREKIdentification.toExponent n lam.1.val) := by
  rw [oddSchurPolynomialBasis, Basis.mk_apply, degreeMap_coe, ← sK_eq]
  exact OddLRThm38.sK_eq_schur n lam.1.val lam.2

/-! ## The odd Schur basis of OΛ -/

theorem linearIndependent_graded {M ι : Type*} [AddCommGroup M] (w : ι → M) (deg : ι → ℕ)
    (p : ℕ → M →+ M) (hp : ∀ d i, p d (w i) = if deg i = d then w i else 0)
    (hd : ∀ d, LinearIndependent ℤ (fun i : {i // deg i = d} => w i)) :
    LinearIndependent ℤ w := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hg i hi
  have h1 := congrArg (p (deg i)) hg
  rw [map_sum, map_zero] at h1
  simp only [map_zsmul, hp] at h1
  have h2 : ∑ j ∈ s.subtype (fun j => deg j = deg i), g j.1 • w j.1 = 0 := by
    rw [Finset.sum_subtype_eq_sum_filter (f := fun j => g j • w j), Finset.sum_filter]
    refine Eq.trans ?_ h1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  exact linearIndependent_iff'.mp (hd (deg i)) _ (fun j => g j.1) h2 ⟨i, rfl⟩
    (Finset.mem_subtype.mpr hi)

theorem sK_linearIndependent : LinearIndependent ℤ sK := by
  apply linearIndependent_graded sK YoungDiagram.card
    (fun d => (Finsupp.applyAddHom d).comp EKIntegralBases.decompose.toAddMonoidHom)
  · intro d lam
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      Finsupp.applyAddHom_apply, EKIntegralBases.decompose_piece (sK_mem lam),
      Finsupp.single_apply]
  · intro d
    have h := (schurK_linearIndependent d).map' (EKIntegralBases.degreePiece d).subtype
      (Submodule.ker_subtype _)
    have e : (fun i : {i : YoungDiagram // i.card = d} => sK i.1) =
        (EKIntegralBases.degreePiece d).subtype ∘ schurK d := funext fun i => sK_eq d i
    rw [e]
    exact h

theorem sK_span : ⊤ ≤ Submodule.span ℤ (Set.range sK) := by
  rw [← EKIntegralBases.hBasis.span_eq, Submodule.span_le]
  rintro _ ⟨μ, rfl⟩
  let A := (Submodule.span ℤ (Set.range sK)).comap (EKIntegralBases.degreePiece μ.card).subtype
  have hA : ∀ i, schurK μ.card i ∈ A := fun i => by
    rw [Submodule.mem_comap, Submodule.subtype_apply, ← sK_eq]
    exact Submodule.subset_span ⟨_, rfl⟩
  have h := (KostkaModuleInversion.submoduleTarget μ.card A (schurK μ.card)).mpr hA ⟨μ, rfl⟩
  rw [OddLREKIdentification.schurK_defining, Submodule.mem_comap, Submodule.subtype_apply,
    EKIntegralBases.degreeHBasis_apply] at h
  rw [SetLike.mem_coe, EKIntegralBases.hBasis_apply]
  exact h

/-- The odd Schur functions `s^H_λ` form a ℤ-basis of OΛ (EKL p. 46). -/
def sBasis : Basis YoungDiagram ℤ Q := Basis.mk sK_linearIndependent sK_span

@[simp] theorem sBasis_apply (lam : YoungDiagram) : sBasis lam = sK lam := Basis.mk_apply _ _ _

/-- The ℤ-span of the `s^H_λ` with `λ` in a set `S` is detected by `s^H`-coordinates. -/
theorem mem_span_sK_iff (P : YoungDiagram → Prop) (x : Q) :
    x ∈ Submodule.span ℤ {y | ∃ lam, P lam ∧ y = sK lam} ↔
      ∀ lam, ¬ P lam → sBasis.repr x lam = 0 := by
  have e : {y | ∃ lam, P lam ∧ y = sK lam} = sBasis '' {lam | P lam} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image, sBasis_apply]
    exact ⟨fun ⟨l, h, e⟩ => ⟨l, h, e.symm⟩, fun ⟨l, h, e⟩ => ⟨l, h, e.symm⟩⟩
  rw [e, Basis.mem_span_image]
  constructor
  · intro h lam hl
    by_contra hne
    exact hl (h (Finsupp.mem_support_iff.mpr hne))
  · intro h lam hl
    by_contra hne
    exact Finsupp.mem_support_iff.mp hl (h lam hne)

/-! ## Transposition: complete-side ideals -/

open EKAutomorphisms (psi12)

theorem psi12_sK (lam : YoungDiagram) :
    psi12 (sK lam) =
      ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam + lam.card)) • sK lam.transpose := by
  have h := EKFinalClosure.lemma_3_11 lam.card ⟨lam, rfl⟩
  have e := sK_eq lam.card (EKDualBases.transposeShape lam.card ⟨lam, rfl⟩)
  rw [show sK lam.transpose = _ from e]
  exact h

/-- ℤ-span of the `s^H_λ` with more than `b` columns. -/
def wideSchurSpan (b : ℕ) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ lam : YoungDiagram, b < lam.rowLen 0 ∧ x = sK lam}

/-- The two-sided ideal `⟨h_m : m > b⟩` of OΛ. -/
def hIdeal (b : ℕ) : TwoSidedIdeal Q :=
  TwoSidedIdeal.span {x | ∃ m, b < m ∧ x = EKElementaryQuotient.h m}

theorem psi12_mem_wideSchurSpan {b : ℕ} {x : Q} (hx : x ∈ tallSpan b) :
    psi12 x ∈ wideSchurSpan b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨lam, hl, rfl⟩ := hx
    rw [psi12_sK]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨lam.transpose, by rwa [YoungDiagram.rowLen_transpose], rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul z x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ z hx

theorem psi12_mem_tallSpan {b : ℕ} {x : Q} (hx : x ∈ wideSchurSpan b) :
    psi12 x ∈ tallSpan b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨lam, hl, rfl⟩ := hx
    rw [psi12_sK]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨lam.transpose, by rwa [YoungDiagram.colLen_transpose], rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul z x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ z hx

theorem psi12_mem_hIdeal {b : ℕ} {x : Q} (hx : x ∈ elemIdeal b) : psi12 x ∈ hIdeal b := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [EKAutomorphisms.psi12_e]
    exact (hIdeal b).zsmul_mem _ (TwoSidedIdeal.subset_span ⟨m, hm, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | left_absorb a x _ hx => rw [map_mul]; exact (hIdeal b).mul_mem_left _ _ hx
  | right_absorb a x _ hx => rw [map_mul]; exact (hIdeal b).mul_mem_right _ _ hx

theorem psi12_mem_elemIdeal {b : ℕ} {x : Q} (hx : x ∈ hIdeal b) : psi12 x ∈ elemIdeal b := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [EKAutomorphisms.psi12_h]
    exact (elemIdeal b).zsmul_mem _ (TwoSidedIdeal.subset_span ⟨m, hm, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | left_absorb a x _ hx => rw [map_mul]; exact (elemIdeal b).mul_mem_left _ _ hx
  | right_absorb a x _ hx => rw [map_mul]; exact (elemIdeal b).mul_mem_right _ _ hx

/-- `⟨h_m : m > b⟩` is the ℤ-span of the `s^H_λ` with more than `b` columns (EKL p. 46, proof
of Prop 5.4, via `ψ₁ψ₂`). -/
theorem mem_hIdeal_iff_mem_wideSchurSpan (b : ℕ) (x : Q) :
    x ∈ hIdeal b ↔ x ∈ wideSchurSpan b := by
  constructor
  · intro hx
    have h1 := (mem_elemIdeal_iff_mem_tallSpan b _).mp (psi12_mem_elemIdeal hx)
    have h2 := psi12_mem_wideSchurSpan h1
    rwa [EKAutomorphisms.psi12_involutive] at h2
  · intro hx
    have h1 := (mem_elemIdeal_iff_mem_tallSpan b _).mpr (psi12_mem_tallSpan hx)
    have h2 := psi12_mem_hIdeal h1
    rwa [EKAutomorphisms.psi12_involutive] at h2

/-! ## Proposition 5.4 -/

/-- `λ` does not fit in the `a × b` box. -/
def Outside (a b : ℕ) (lam : YoungDiagram) : Prop := a < lam.colLen 0 ∨ b < lam.rowLen 0

/-- The kernel of OΛ → OH_{a,a+b}: `⟨ε_m : m > a⟩ + ⟨h_m : m > b⟩`. -/
def boxIdeal (a b : ℕ) : TwoSidedIdeal Q := elemIdeal a ⊔ hIdeal b

/-- `⟨ε_m : m > a⟩ + ⟨h_m : m > b⟩` is the ℤ-span of the `s^H_λ` with `λ ⊄ a × b`. -/
theorem mem_boxIdeal_iff (a b : ℕ) (x : Q) :
    x ∈ boxIdeal a b ↔ x ∈ Submodule.span ℤ {y | ∃ lam, Outside a b lam ∧ y = sK lam} := by
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := TwoSidedIdeal.mem_sup.mp hx
    rw [mem_elemIdeal_iff_mem_tallSpan] at hy
    rw [mem_hIdeal_iff_mem_wideSchurSpan] at hz
    apply add_mem
    · exact Submodule.span_mono (by rintro w ⟨lam, hl, e⟩; exact ⟨lam, Or.inl hl, e⟩) hy
    · exact Submodule.span_mono (by rintro w ⟨lam, hl, e⟩; exact ⟨lam, Or.inr hl, e⟩) hz
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨lam, hl | hl, rfl⟩ := hx
      · apply TwoSidedIdeal.mem_sup_left
        rw [mem_elemIdeal_iff_mem_tallSpan]
        exact Submodule.subset_span ⟨lam, hl, rfl⟩
      · apply TwoSidedIdeal.mem_sup_right
        rw [mem_hIdeal_iff_mem_wideSchurSpan]
        exact Submodule.subset_span ⟨lam, hl, rfl⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul z x _ hx => exact (boxIdeal a b).zsmul_mem z hx

theorem mem_boxIdeal_iff_repr (a b : ℕ) (x : Q) :
    x ∈ boxIdeal a b ↔ ∀ lam, ¬ Outside a b lam → sBasis.repr x lam = 0 :=
  (mem_boxIdeal_iff a b x).trans (mem_span_sK_iff _ x)

open Cyclotomic in
/-- OΛ → OΛ_a → OH_{a,N}, `a = n+2`, `N = a+b`. -/
def toOHQ (n b : ℕ) : Q →+* OH n (n+2+b) := (toOH n (n+2+b)).comp (piA n)

theorem toOHQ_surjective (n b : ℕ) : Function.Surjective (toOHQ n b) :=
  (Cyclotomic.toOH_surjective n _).comp (piA_surjective n)

theorem piA_h (n m : ℕ) : piA n (EKElementaryQuotient.h m) = Cyclotomic.hK n m :=
  Subtype.ext (OddLREKIdentification.piN_h _ _)

/-- The image of `⟨h_m : m > b⟩` under `π_a` is an ideal of OΛ_a. -/
def imageIdeal (n b : ℕ) : TwoSidedIdeal (OddSymmetricKernel.kernelSubring n) :=
  TwoSidedIdeal.mk' {y | ∃ x ∈ hIdeal b, piA n x = y}
    ⟨0, zero_mem _, map_zero _⟩
    (by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, add_mem hx hy, map_add _ _ _⟩)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨-x, neg_mem hx, map_neg _ _⟩)
    (by
      rintro q _ ⟨x, hx, rfl⟩
      obtain ⟨q', rfl⟩ := piA_surjective n q
      exact ⟨q' * x, (hIdeal b).mul_mem_left _ _ hx, map_mul _ _ _⟩)
    (by
      rintro _ q ⟨x, hx, rfl⟩
      obtain ⟨q', rfl⟩ := piA_surjective n q
      exact ⟨x * q', (hIdeal b).mul_mem_right _ _ hx, map_mul _ _ _⟩)

/-- `ker(OΛ → OH_{a,a+b}) = ⟨ε_m : m > a⟩ + ⟨h_m : m > b⟩`. -/
theorem toOHQ_eq_zero_iff (n b : ℕ) (x : Q) : toOHQ n b x = 0 ↔ x ∈ boxIdeal (n+2) b := by
  constructor
  · intro hx
    have h1 : piA n x ∈ Cyclotomic.grassmannianIdeal n (n+2+b) :=
      (Cyclotomic.toOH_eq_zero_iff n _ _).mp hx
    have hle : Cyclotomic.grassmannianIdeal n (n+2+b) ≤ imageIdeal n b := by
      apply TwoSidedIdeal.span_le.mpr
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, imageIdeal, TwoSidedIdeal.mem_mk']
      exact ⟨EKElementaryQuotient.h m, TwoSidedIdeal.subset_span ⟨m, by omega, rfl⟩, piA_h n m⟩
    have h2 := hle h1
    rw [imageIdeal, TwoSidedIdeal.mem_mk'] at h2
    obtain ⟨x', hx', he⟩ := h2
    have h3 : x - x' ∈ elemIdeal (n+2) := by
      rw [← piA_eq_zero_iff, map_sub, he, sub_self]
    apply TwoSidedIdeal.mem_sup.mpr
    exact ⟨x - x', h3, x', hx', sub_add_cancel x x'⟩
  · intro hx
    have hle : boxIdeal (n+2) b ≤ TwoSidedIdeal.ker (toOHQ n b) := by
      apply sup_le
      · intro y hy
        rw [TwoSidedIdeal.mem_ker, toOHQ, RingHom.comp_apply, (piA_eq_zero_iff n y).mpr hy,
          map_zero]
      · apply TwoSidedIdeal.span_le.mpr
        rintro _ ⟨m, hm, rfl⟩
        rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker, toOHQ, RingHom.comp_apply, piA_h]
        exact Cyclotomic.toOH_hK n _ m (by omega)
    exact (TwoSidedIdeal.mem_ker _).mp (hle hx)

/-- Partitions in the `a × b` box. -/
abbrev BoxShape (a b : ℕ) := {lam : YoungDiagram // lam.colLen 0 ≤ a ∧ lam.rowLen 0 ≤ b}

/-- EKL Prop 5.4, vanishing part: `s^H_λ ↦ 0` in OH_{a,N} unless `λ ⊆ a × (N − a)`. -/
theorem toOHQ_sK_eq_zero (n b : ℕ) (lam : YoungDiagram) (h : Outside (n+2) b lam) :
    toOHQ n b (sK lam) = 0 :=
  (toOHQ_eq_zero_iff n b _).mpr ((mem_boxIdeal_iff _ _ _).mpr (Submodule.subset_span ⟨lam, h, rfl⟩))

theorem not_outside (a b : ℕ) (lam : BoxShape a b) : ¬ Outside a b lam.1 := by
  rintro (h | h) <;> [exact absurd lam.2.1 (by omega); exact absurd lam.2.2 (by omega)]

theorem oddSchur_linearIndependent (n b : ℕ) :
    LinearIndependent ℤ (fun lam : BoxShape (n+2) b => toOHQ n b (sK lam.1)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hg i hi
  have h1 : toOHQ n b (∑ j ∈ s, g j • sK j.1) = 0 := by
    rw [map_sum]
    simpa only [map_zsmul] using hg
  have h2 := (mem_boxIdeal_iff_repr _ _ _).mp ((toOHQ_eq_zero_iff n b _).mp h1) i.1
    (not_outside _ _ i)
  rw [map_sum] at h2
  simp only [map_zsmul, ← sBasis_apply, Basis.repr_self, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul,
    mul_ite, _root_.mul_one, MulZeroClass.mul_zero] at h2
  rw [Finset.sum_eq_single i] at h2
  · simpa using h2
  · intro j _ hji
    rw [if_neg (fun h => hji (Subtype.ext h))]
  · intro h; exact absurd hi h

theorem oddSchur_span (n b : ℕ) :
    ⊤ ≤ Submodule.span ℤ (Set.range (fun lam : BoxShape (n+2) b => toOHQ n b (sK lam.1))) := by
  rintro y -
  obtain ⟨x, rfl⟩ := toOHQ_surjective n b y
  have hx : x ∈ Submodule.span ℤ (Set.range sK) := sK_span Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨lam, rfl⟩ := hx
    by_cases hl : Outside (n+2) b lam
    · rw [toOHQ_sK_eq_zero n b lam hl]
      exact zero_mem _
    · simp only [Outside, not_or, not_lt] at hl
      exact Submodule.subset_span ⟨⟨lam, hl⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul z x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ z hx

/-- **EKL Proposition 5.4** (p. 46), for `a = n+2 ≥ 2` and `N = a+b ≥ a`: over ℤ, the images
of the odd Schur functions `s^H_λ` with `λ ⊆ a × (N − a)` form a ℤ-basis of `OH_{a,N}`.
No freeness of `OH_{a,N}` is assumed: the kernel of OΛ → OH_{a,N} is computed as the ℤ-span of
the remaining `s^H_λ` (`mem_boxIdeal_iff`). -/
def proposition_5_4 (n b : ℕ) : Basis (BoxShape (n+2) b) ℤ (Cyclotomic.OH n (n+2+b)) :=
  Basis.mk (oddSchur_linearIndependent n b) (oddSchur_span n b)

theorem proposition_5_4_apply (n b : ℕ) (lam : BoxShape (n+2) b) :
    proposition_5_4 n b lam = Cyclotomic.toOH n (n+2+b) (piA n (sK lam.1)) :=
  Basis.mk_apply _ _ _

/-- The basis vectors are the images of the odd Schur polynomials `s_λ ∈ OΛ_a` (EKL (2.69)),
which are homogeneous of degree `|λ|`. -/
theorem proposition_5_4_schur (n b : ℕ) (lam : BoxShape (n+2) b) :
    ∃ h : OddSymmetrizer.schur n (OddLREKIdentification.toExponent n lam.1) ∈
        OddSymmetricKernel.kernelSubring n,
      proposition_5_4 n b lam = Cyclotomic.toOH n (n+2+b) ⟨_, h⟩ ∧
      ElementaryBasis.Homogeneous lam.1.card
        (OddSymmetrizer.schur n (OddLREKIdentification.toExponent n lam.1)) := by
  have e := OddLRThm38.sK_eq_schur n lam.1 lam.2.1
  refine ⟨e ▸ (piA n (sK lam.1)).2, ?_, ?_⟩
  · rw [proposition_5_4_apply]
    congr 1
    exact Subtype.ext e
  · rw [← e]
    exact piN_homogeneous (n+2) lam.1.card ⟨_, sK_mem lam.1⟩

/-- `OH_{a,a+b} ≅ OΛ/(⟨ε_m : m > a⟩ + ⟨h_m : m > b⟩)`, `a = n+2`. -/
def oh_equiv_quotient (n b : ℕ) :
    Q ⧸ (boxIdeal (n+2) b).asIdeal ≃+* Cyclotomic.OH n (n+2+b) :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift _ (toOHQ n b) (fun x hx =>
      (toOHQ_eq_zero_iff n b x).mpr (TwoSidedIdeal.mem_asIdeal.mp hx)))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.Quotient.lift_mk] at hy
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (TwoSidedIdeal.mem_asIdeal.mpr ((toOHQ_eq_zero_iff n b x).mp hy)),
     by
      intro y
      obtain ⟨x, rfl⟩ := toOHQ_surjective n b y
      exact ⟨Ideal.Quotient.mk _ x, Ideal.Quotient.lift_mk _ _ _⟩⟩

/-! ## Rank of `OH_{a,N}` -/

/-- The Young diagram with row lengths `α₀ ≥ α₁ ≥ ⋯ ≥ α_{a-1}`. -/
def ofRows {a : ℕ} (α : Fin a → ℕ) (hα : Antitone α) : YoungDiagram where
  cells := by
    classical
    exact (Finset.range a ×ˢ Finset.range (∑ i, α i + 1)).filter
      (fun p => ∃ h : p.1 < a, p.2 < α ⟨p.1, h⟩)
  isLowerSet := by
    classical
    rintro ⟨i, j⟩ ⟨i', j'⟩ hle hmem
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq] at hmem ⊢
    obtain ⟨⟨_, _⟩, h, hj⟩ := hmem
    obtain ⟨hi', hj'⟩ := hle
    simp only at hi' hj'
    have hα' : α ⟨i, h⟩ ≤ α ⟨i', by omega⟩ := hα (Fin.mk_le_mk.mpr hi')
    have hs : α ⟨i', by omega⟩ ≤ ∑ k, α k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

theorem mem_ofRows {a : ℕ} (α : Fin a → ℕ) (hα : Antitone α) (i j : ℕ) :
    (i, j) ∈ ofRows α hα ↔ ∃ h : i < a, j < α ⟨i, h⟩ := by
  classical
  change (i, j) ∈ (ofRows α hα).cells ↔ _
  simp only [ofRows, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h, hj⟩
    have hs : α ⟨i, h⟩ ≤ ∑ k, α k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    exact ⟨⟨h, by omega⟩, h, hj⟩

theorem rowLen_ofRows {a : ℕ} (α : Fin a → ℕ) (hα : Antitone α) (i : Fin a) :
    (ofRows α hα).rowLen i = α i := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_ofRows]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.2, h⟩⟩

/-- `λ ⊆ a × b` ↔ antitone `a`-tuples with entries `≤ b` (`BoxPartitionCount.box`). -/
def boxEquiv (a b : ℕ) : BoxShape a b ≃ BoxPartitionCount.box a b where
  toFun lam := ⟨fun i => lam.1.rowLen i, BoxPartitionCount.mem_box.mpr
    ⟨fun i j hij => lam.1.rowLen_anti _ _ hij,
     fun i => (lam.1.rowLen_anti 0 i (Nat.zero_le _)).trans lam.2.2⟩⟩
  invFun α := ⟨ofRows α.1 (BoxPartitionCount.mem_box.mp α.2).1, by
    constructor
    · by_contra h
      push_neg at h
      have := (mem_ofRows _ _ a 0).mp (YoungDiagram.mem_iff_lt_colLen.mpr h)
      obtain ⟨h1, _⟩ := this
      omega
    · by_contra h
      push_neg at h
      obtain ⟨h1, h2⟩ := (mem_ofRows _ _ 0 b).mp (YoungDiagram.mem_iff_lt_rowLen.mpr h)
      have := (BoxPartitionCount.mem_box.mp α.2).2 ⟨0, h1⟩
      omega⟩
  left_inv lam := by
    apply Subtype.ext
    apply YoungDiagram.ext
    ext ⟨i, j⟩
    dsimp only
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, mem_ofRows]
    constructor
    · rintro ⟨_, h⟩; exact YoungDiagram.mem_iff_lt_rowLen.mpr h
    · intro h
      have hi : i < lam.1.colLen 0 :=
        YoungDiagram.mem_iff_lt_colLen.mp (lam.1.up_left_mem le_rfl (Nat.zero_le _) h)
      exact ⟨by have := lam.2.1; omega, YoungDiagram.mem_iff_lt_rowLen.mp h⟩
  right_inv α := by
    apply Subtype.ext
    funext i
    dsimp only
    exact rowLen_ofRows _ _ i

noncomputable instance (a b : ℕ) : Fintype (BoxShape a b) :=
  Fintype.ofEquiv _ (boxEquiv a b).symm

theorem card_boxShape (a b : ℕ) : Fintype.card (BoxShape a b) = (a + b).choose a := by
  rw [Fintype.card_congr (boxEquiv a b), Fintype.card_coe, BoxPartitionCount.card_box]

/-- `OH_{a,N}` is a free ℤ-module of rank `C(N, a)` (`a = n+2 ≤ N`). -/
theorem finrank_OH (n b : ℕ) :
    Module.finrank ℤ (Cyclotomic.OH n (n+2+b)) = (n+2+b).choose (n+2) := by
  rw [Module.finrank_eq_card_basis (proposition_5_4 n b), card_boxShape]

instance (n b : ℕ) : Module.Free ℤ (Cyclotomic.OH n (n+2+b)) :=
  Module.Free.of_basis (proposition_5_4 n b)

end OddMath.Frontier.OddGrassmannSchur
