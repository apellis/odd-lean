import OddMath.SKM.RouquierMateSectors

/-!
# The coupled raising functor of two separated sectors

Ports the coproduct assembly of `Categorification/TwoRep/RouqCoproduct.lean`
(`objEF`, `objFE`, `sigD`, the summed crossing `δ` and `rouqSig_eq`) to the
super setting, for the two-sector case used by separated fusion: a reservoir
sector with nilpotent dots and a probe sector with invertible dots.

The coupled 1-morphisms are given with finite sector decompositions
(`SectorDecomp`): even inclusions and projections with the biproduct
identities. For the content-shifted Hom family the two summands of the coupled
raising functor are to be the postcomposition and precomposition sectors; that
decomposition is an input here, not constructed.

* `SectorDecomp.comp`: the four-summand decomposition of `E₁ ≫ E₂`.
* `coupledAdjunction`: the diagonal adjunction built from the sector
  adjunctions, with both triangle identities. Its counit restricts and its unit
  projects to the sector counit and unit (`inc_coupledCounit`,
  `coupledUnit_proj`).
* `coupledRationalLeft`, `coupledRationalRight`: the position-preserving
  cross-sector crossing entries. They are the quotient of the original-datum
  crossing by the product-datum one on separated sectors: the finite series
  inverting `y - q x` when one dot is nilpotent and the other invertible. Their
  slide identities are `coupledRationalLeft_spec` and `coupledRationalRight_spec`;
  odd dots and `q = -1` are allowed, and no dot is assumed central.
* `CoupledFactors.cross`: the coupled crossing, a block matrix whose diagonal
  sector blocks are the factor crossings, whose position-preserving
  cross-sector blocks are the rational entries, and whose sector-swapping blocks
  are given entries intertwining the dots.
* `CoupledFactors.slide`: the upward slide of the coupled crossing.
* `CoupledFactors.mateProjectionFormula`: F's `MateProjectionFormula.of_sectors`
  for the actual coupled data; the probe inverses and reservoir nilpotence are
  those of the concrete sectors.

The quadratic, braid and Rouquier-inversion relations of the coupled crossing
are not proved here, and the sector-swapping blocks are not computed: the
projection formula does not involve them.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-! ## Rational cross-sector entries in an associative ring -/

section Ring
variable {R : Type*} [Ring R]

/-- The cross-sector entry inverting `Y - q X` on the left when `X` is nilpotent
and `Y` has right inverse `Z`: `Σ_{r<N} q^r Z^{r+1} X^r`. -/
def coupledRationalLeft (q : ℤ) (X Z : R) (N : ℕ) : R :=
  ∑ r ∈ Finset.range N, (q ^ r) • (Z ^ (r + 1) * X ^ r)

/-- The left rational entry solves the separated slide `Y d - q d X = 1`. Neither
centrality of `X`, `Y` nor `q² = 1` is used. -/
theorem coupledRationalLeft_spec (q : ℤ) {X Y Z : R} (N : ℕ) (hYZ : Y * Z = 1)
    (hX : X ^ N = 0) :
    Y * coupledRationalLeft q X Z N - q • (coupledRationalLeft q X Z N * X) = 1 := by
  unfold coupledRationalLeft
  rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib]
  have h : ∀ r ∈ Finset.range N,
      Y * (q ^ r • (Z ^ (r + 1) * X ^ r)) - q • (q ^ r • (Z ^ (r + 1) * X ^ r) * X) =
        q ^ r • (Z ^ r * X ^ r) - q ^ (r + 1) • (Z ^ (r + 1) * X ^ (r + 1)) := by
    intro r _
    congr 1
    · rw [mul_smul_comm, pow_succ' Z r, ← mul_assoc, ← mul_assoc, hYZ, one_mul]
    · rw [smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ, ← pow_succ']
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub' (fun r => q ^ r • (Z ^ r * X ^ r)) N]
  simp [hX]

/-- The cross-sector entry inverting on the right when `X` is nilpotent and `Y`
has left inverse `Z`: `-Σ_{r<N} q^(r+1) X^r Z^(r+1)`. -/
def coupledRationalRight (q : ℤ) (X Z : R) (N : ℕ) : R :=
  ∑ r ∈ Finset.range N, (-q ^ (r + 1)) • (X ^ r * Z ^ (r + 1))

/-- The right rational entry solves `X d - q d Y = 1`, for a sign `q² = 1`. -/
theorem coupledRationalRight_spec {q : ℤ} (hq : q * q = 1) {X Y Z : R} (N : ℕ)
    (hZY : Z * Y = 1) (hX : X ^ N = 0) :
    X * coupledRationalRight q X Z N - q • (coupledRationalRight q X Z N * Y) = 1 := by
  unfold coupledRationalRight
  rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib]
  have h : ∀ r ∈ Finset.range N,
      X * ((-q ^ (r + 1)) • (X ^ r * Z ^ (r + 1))) -
          q • ((-q ^ (r + 1)) • (X ^ r * Z ^ (r + 1)) * Y) =
        q ^ r • (X ^ r * Z ^ r) - q ^ (r + 1) • (X ^ (r + 1) * Z ^ (r + 1)) := by
    intro r _
    have hZ : Z ^ (r + 1) * Y = Z ^ r := by rw [pow_succ, mul_assoc, hZY, mul_one]
    have hqq : q * -q ^ (r + 1) = -q ^ r := by
      rw [pow_succ', mul_neg, ← mul_assoc, hq, one_mul]
    rw [mul_smul_comm, ← mul_assoc, ← pow_succ', smul_mul_assoc, smul_smul, mul_assoc, hZ, hqq,
      neg_smul, neg_smul, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub' (fun r => q ^ r • (X ^ r * Z ^ r)) N]
  simp [hX]

end Ring

/-! ## Powers and sums of whiskered 2-morphisms -/

section Powers
variable {a b c : B}

omit [∀ a b : B, Preadditive (a ⟶ b)] in
/-- Vertical powers are the powers of the endomorphism monoid. -/
theorem rouquierPower_eq_pow {E : a ⟶ b} (x : E ⟶ E) (n : ℕ) :
    rouquierPower x n = (show End E from x) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rouquierPower_succ, ih, pow_succ']; rfl

include k

theorem sum_whiskerRight {ι : Type*} (s : Finset ι) {E E' : a ⟶ b} (f : ι → (E ⟶ E'))
    (F : b ⟶ c) : (∑ i ∈ s, f i) ▷ F = ∑ i ∈ s, f i ▷ F :=
  map_sum (AddMonoidHom.mk' (fun η : E ⟶ E' => η ▷ F)
    fun η θ => TwoSupercategory.add_whiskerRight (R := k) η θ F) f s

theorem whiskerLeft_sum {ι : Type*} (s : Finset ι) (F : c ⟶ a) {E E' : a ⟶ b}
    (f : ι → (E ⟶ E')) : F ◁ (∑ i ∈ s, f i) = ∑ i ∈ s, F ◁ f i :=
  map_sum (AddMonoidHom.mk' (fun η : E ⟶ E' => F ◁ η)
    fun η θ => TwoSupercategory.whiskerLeft_add (R := k) F η θ) f s

omit [TwoSupercategory k B] in
theorem even_comp_mem {E E' E'' : a ⟶ b} {f : E ⟶ E'} {g : E' ⟶ E''}
    (hf : f ∈ parity (R := k) _ _ 0) (hg : g ∈ parity (R := k) _ _ 0) :
    f ≫ g ∈ parity (R := k) _ _ 0 := by
  simpa using Supercategory.comp_mem hf hg

end Powers

/-! ## Finite sector decompositions of 1-morphisms -/

/-- A finite decomposition of a 1-morphism into sector summands, by even
inclusions and projections satisfying the biproduct identities. -/
structure SectorDecomp {a b : B} (M : a ⟶ b) (ι : Type) [Fintype ι] [DecidableEq ι]
    (O : ι → (a ⟶ b)) where
  inc : ∀ i, O i ⟶ M
  proj : ∀ i, M ⟶ O i
  inc_mem : ∀ i, inc i ∈ parity (R := k) _ _ 0
  proj_mem : ∀ i, proj i ∈ parity (R := k) _ _ 0
  inc_proj : ∀ i, inc i ≫ proj i = 𝟙 (O i)
  inc_proj_ne : ∀ i j, i ≠ j → inc i ≫ proj j = 0
  total : ∑ i, proj i ≫ inc i = 𝟙 M

namespace SectorDecomp
variable {a b c : B} {M : a ⟶ b} {ι : Type} [Fintype ι] [DecidableEq ι] {O : ι → (a ⟶ b)}
  (D : SectorDecomp (k := k) M ι O)

omit [TwoSupercategory k B] in
theorem inc_sum (i : ι) {N : a ⟶ b} (f : ∀ j, O j ⟶ N) :
    D.inc i ≫ ∑ j, D.proj j ≫ f j = f i := by
  rw [Preadditive.comp_sum, Finset.sum_eq_single i]
  · rw [← Category.assoc, D.inc_proj, Category.id_comp]
  · intro j _ hj
    rw [← Category.assoc, D.inc_proj_ne i j (Ne.symm hj), Limits.zero_comp]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [TwoSupercategory k B] in
theorem sum_proj (i : ι) {N : a ⟶ b} (f : ∀ j, N ⟶ O j) :
    (∑ j, f j ≫ D.inc j) ≫ D.proj i = f i := by
  rw [Preadditive.sum_comp, Finset.sum_eq_single i]
  · rw [Category.assoc, D.inc_proj, Category.comp_id]
  · intro j _ hj
    rw [Category.assoc, D.inc_proj_ne j i hj, Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [TwoSupercategory k B] in
theorem ext {N : a ⟶ b} {f g : M ⟶ N} (h : ∀ i, D.inc i ≫ f = D.inc i ≫ g) : f = g := by
  rw [← Category.id_comp f, ← Category.id_comp g, ← D.total, Preadditive.sum_comp,
    Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by rw [Category.assoc, Category.assoc, h i]

/-- A diagonal endomorphism with the given sector blocks. -/
def diag (d : ∀ i, O i ⟶ O i) : M ⟶ M := ∑ i, D.proj i ≫ d i ≫ D.inc i

omit [TwoSupercategory k B] in
theorem inc_diag (d : ∀ i, O i ⟶ O i) (i : ι) : D.inc i ≫ D.diag d = d i ≫ D.inc i :=
  D.inc_sum i fun j => d j ≫ D.inc j

omit [TwoSupercategory k B] in
theorem diag_proj (d : ∀ i, O i ⟶ O i) (i : ι) : D.diag d ≫ D.proj i = D.proj i ≫ d i := by
  have := D.sum_proj i fun j => D.proj j ≫ d j
  unfold diag
  simpa only [Category.assoc] using this

omit [TwoSupercategory k B] in
theorem eq_diag {f : M ⟶ M} (d : ∀ i, O i ⟶ O i) (h : ∀ i, D.inc i ≫ f = d i ≫ D.inc i) :
    f = D.diag d :=
  D.ext fun i => by rw [h, D.inc_diag]

/-- An endomorphism with the given block matrix. -/
def mat (m : ∀ i j, O i ⟶ O j) : M ⟶ M := ∑ i, ∑ j, D.proj i ≫ m i j ≫ D.inc j

omit [TwoSupercategory k B] in
theorem inc_mat (m : ∀ i j, O i ⟶ O j) (i : ι) :
    D.inc i ≫ D.mat m = ∑ j, m i j ≫ D.inc j := by
  unfold mat
  simp_rw [← Preadditive.comp_sum]
  exact D.inc_sum i fun i' => ∑ j, m i' j ≫ D.inc j

omit [TwoSupercategory k B] in
theorem mat_comp_diag (m : ∀ i j, O i ⟶ O j) (d : ∀ i, O i ⟶ O i) :
    D.mat m ≫ D.diag d = D.mat fun i j => m i j ≫ d j :=
  D.ext fun i => by
    rw [← Category.assoc, D.inc_mat, D.inc_mat, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun j _ => by rw [Category.assoc, D.inc_diag, Category.assoc]

omit [TwoSupercategory k B] in
theorem diag_comp_mat (m : ∀ i j, O i ⟶ O j) (d : ∀ i, O i ⟶ O i) :
    D.diag d ≫ D.mat m = D.mat fun i j => d i ≫ m i j :=
  D.ext fun i => by
    rw [← Category.assoc, D.inc_diag, Category.assoc, D.inc_mat, D.inc_mat,
      Preadditive.comp_sum]
    simp only [Category.assoc]

omit [TwoSupercategory k B] in
theorem mat_sub_zsmul (m m' : ∀ i j, O i ⟶ O j) (q : ℤ) :
    D.mat m - q • D.mat m' = D.mat fun i j => m i j - q • m' i j :=
  D.ext fun i => by
    rw [Preadditive.comp_sub, Preadditive.comp_zsmul, D.inc_mat, D.inc_mat, D.inc_mat,
      Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Preadditive.sub_comp, Preadditive.zsmul_comp]

omit [TwoSupercategory k B] in
theorem mat_eq_id (m : ∀ i j, O i ⟶ O j) (h₁ : ∀ i, m i i = 𝟙 (O i))
    (h₂ : ∀ i j, i ≠ j → m i j = 0) : D.mat m = 𝟙 M :=
  D.ext fun i => by
    rw [D.inc_mat, Category.comp_id, Finset.sum_eq_single i]
    · rw [h₁, Category.id_comp]
    · intro j _ hj; rw [h₂ i j (Ne.symm hj), Limits.zero_comp]
    · intro h; exact absurd (Finset.mem_univ i) h

/-- Exchange of an even sector map with a whiskered 2-morphism. -/
@[reassoc]
theorem exch {f g : a ⟶ b} {h i : b ⟶ c} {η : f ⟶ g} (hη : η ∈ parity (R := k) f g 0)
    (θ : h ⟶ i) : f ◁ θ ≫ η ▷ i = η ▷ h ≫ g ◁ θ :=
  (TwoSupercategory.whisker_exchange_of_even_left hη θ).symm

/-- The four-summand decomposition of a composite of decomposed 1-morphisms. -/
def comp {N : b ⟶ c} {κ : Type} [Fintype κ] [DecidableEq κ] {P : κ → (b ⟶ c)}
    (D' : SectorDecomp (k := k) N κ P) :
    SectorDecomp (k := k) (M ≫ N) (ι × κ) (fun x => O x.1 ≫ P x.2) where
  inc x := D.inc x.1 ▷ P x.2 ≫ M ◁ D'.inc x.2
  proj x := D.proj x.1 ▷ N ≫ O x.1 ◁ D'.proj x.2
  inc_mem x := even_comp_mem (TwoSupercategory.whiskerRight_mem _ (D.inc_mem x.1))
    (TwoSupercategory.whiskerLeft_mem _ (D'.inc_mem x.2))
  proj_mem x := even_comp_mem (TwoSupercategory.whiskerRight_mem _ (D.proj_mem x.1))
    (TwoSupercategory.whiskerLeft_mem _ (D'.proj_mem x.2))
  inc_proj x := by
    obtain ⟨i, j⟩ := x
    dsimp only
    rw [Category.assoc, ← Category.assoc (M ◁ D'.inc j), exch (D.proj_mem i), Category.assoc,
      ← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k), D.inc_proj,
      ← TwoSupercategory.whiskerLeft_comp (R := k), D'.inc_proj,
      TwoSupercategory.id_whiskerRight (R := k), TwoSupercategory.whiskerLeft_id (R := k),
      Category.comp_id]
  inc_proj_ne x y hxy := by
    obtain ⟨i, j⟩ := x
    obtain ⟨i', j'⟩ := y
    dsimp only
    rw [Category.assoc, ← Category.assoc (M ◁ D'.inc j), exch (D.proj_mem i'), Category.assoc,
      ← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
      ← TwoSupercategory.whiskerLeft_comp (R := k)]
    by_cases hi : i = i'
    · subst hi
      have hj : j ≠ j' := fun h => hxy (by rw [h])
      rw [D'.inc_proj_ne j j' hj, whiskerLeft_zero' (k := k), Limits.comp_zero]
    · rw [D.inc_proj_ne i i' hi, zero_whiskerRight' (k := k), Limits.zero_comp]
  total := by
    have h : ∀ x : ι × κ, (D.proj x.1 ▷ N ≫ O x.1 ◁ D'.proj x.2) ≫
        (D.inc x.1 ▷ P x.2 ≫ M ◁ D'.inc x.2) =
          (D.proj x.1 ≫ D.inc x.1) ▷ N ≫ M ◁ (D'.proj x.2 ≫ D'.inc x.2) := by
      intro x
      rw [Category.assoc, ← Category.assoc (O x.1 ◁ D'.proj x.2), exch (D.inc_mem x.1),
        TwoSupercategory.comp_whiskerRight (R := k),
        TwoSupercategory.whiskerLeft_comp (R := k)]
      simp only [Category.assoc]
    rw [Finset.sum_congr rfl fun x _ => h x, Fintype.sum_prod_type]
    simp_rw [← Preadditive.comp_sum, ← Preadditive.sum_comp]
    rw [← whiskerLeft_sum (k := k), ← sum_whiskerRight (k := k), D.total, D'.total,
      TwoSupercategory.id_whiskerRight (R := k), TwoSupercategory.whiskerLeft_id (R := k),
      Category.comp_id]

@[simp] theorem comp_inc {N : b ⟶ c} {κ : Type} [Fintype κ] [DecidableEq κ]
    {P : κ → (b ⟶ c)} (D' : SectorDecomp (k := k) N κ P) (x : ι × κ) :
    (D.comp D').inc x = D.inc x.1 ▷ P x.2 ≫ M ◁ D'.inc x.2 := rfl

@[simp] theorem comp_proj {N : b ⟶ c} {κ : Type} [Fintype κ] [DecidableEq κ]
    {P : κ → (b ⟶ c)} (D' : SectorDecomp (k := k) N κ P) (x : ι × κ) :
    (D.comp D').proj x = D.proj x.1 ▷ N ≫ O x.1 ◁ D'.proj x.2 := rfl

/-- A first-strand diagonal 2-morphism is diagonal on the composite. -/
theorem diag_whiskerRight {N : b ⟶ c} {κ : Type} [Fintype κ] [DecidableEq κ]
    {P : κ → (b ⟶ c)} (D' : SectorDecomp (k := k) N κ P) (d : ∀ i, O i ⟶ O i) :
    D.diag d ▷ N = (D.comp D').diag fun x => d x.1 ▷ P x.2 :=
  (D.comp D').eq_diag _ fun x => by
    rw [comp_inc, Category.assoc,
      ← TwoSupercategory.whisker_exchange_of_even_right (D.diag d) (D'.inc_mem x.2),
      ← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k), D.inc_diag,
      TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]

/-- A second-strand diagonal 2-morphism is diagonal on the composite. -/
theorem diag_whiskerLeft {N : b ⟶ c} {κ : Type} [Fintype κ] [DecidableEq κ]
    {P : κ → (b ⟶ c)} (D' : SectorDecomp (k := k) N κ P) (d : ∀ j, P j ⟶ P j) :
    M ◁ D'.diag d = (D.comp D').diag fun x => O x.1 ◁ d x.2 :=
  (D.comp D').eq_diag _ fun x => by
    rw [comp_inc, Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k), D'.inc_diag,
      TwoSupercategory.whiskerLeft_comp (R := k), ← Category.assoc, ← exch (D.inc_mem x.1),
      Category.assoc]

end SectorDecomp

/-! ## The diagonal coupled adjunction -/

section Adjunction
variable {a b : B} {E : a ⟶ b} {F : b ⟶ a} {ι : Type} [Fintype ι] [DecidableEq ι]
  {OE : ι → (a ⟶ b)} {OF : ι → (b ⟶ a)}
  (DE : SectorDecomp (k := k) E ι OE) (DF : SectorDecomp (k := k) F ι OF)
  (A : ∀ i, SuperAdjunction (k := k) (OE i) (OF i))

/-- The diagonal unit: the sum of the sector units. -/
def coupledUnit : 𝟙 a ⟶ E ≫ F := ∑ i, (A i).unit ≫ (DE.comp DF).inc (i, i)

/-- The diagonal counit: the sum of the sector counits. -/
def coupledCounit : F ≫ E ⟶ 𝟙 b := ∑ i, (DF.comp DE).proj (i, i) ≫ (A i).counit

theorem coupledUnit_proj (i : ι) :
    coupledUnit DE DF A ≫ (DE.comp DF).proj (i, i) = (A i).unit := by
  unfold coupledUnit
  rw [Preadditive.sum_comp, Finset.sum_eq_single i]
  · rw [Category.assoc, (DE.comp DF).inc_proj, Category.comp_id]
  · intro j _ hj
    rw [Category.assoc, (DE.comp DF).inc_proj_ne (j, j) (i, i)
      (fun h => hj (congrArg Prod.fst h)), Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem inc_coupledCounit (i : ι) :
    (DF.comp DE).inc (i, i) ≫ coupledCounit DE DF A = (A i).counit := by
  unfold coupledCounit
  rw [Preadditive.comp_sum, Finset.sum_eq_single i]
  · rw [← Category.assoc, (DF.comp DE).inc_proj, Category.id_comp]
  · intro j _ hj
    rw [← Category.assoc, (DF.comp DE).inc_proj_ne (i, i) (j, j)
      (fun h => hj (congrArg Prod.fst h).symm), Limits.zero_comp]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem inc_coupledCounit_ne (x : ι × ι) (hx : x.1 ≠ x.2) :
    (DF.comp DE).inc x ≫ coupledCounit DE DF A = 0 := by
  unfold coupledCounit
  rw [Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Category.assoc, (DF.comp DE).inc_proj_ne x (j, j)
    (fun h => hx (by rw [h])), Limits.zero_comp]

/-- The counit on a whiskered sector inclusion of `E`. -/
theorem whiskerLeft_inc_coupledCounit (i : ι) :
    F ◁ DE.inc i ≫ coupledCounit DE DF A = DF.proj i ▷ OE i ≫ (A i).counit := by
  have hF : F ◁ DE.inc i = ∑ j, DF.proj j ▷ OE i ≫ (DF.comp DE).inc (j, i) := by
    simp only [SectorDecomp.comp_inc]
    simp_rw [← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k)]
    rw [← Preadditive.sum_comp, ← sum_whiskerRight (k := k), DF.total,
      TwoSupercategory.id_whiskerRight (R := k), Category.id_comp]
  rw [hF, Preadditive.sum_comp, Finset.sum_eq_single i]
  · rw [Category.assoc, inc_coupledCounit]
  · intro j _ hj
    rw [Category.assoc, inc_coupledCounit_ne DE DF A (j, i) hj, Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The counit on a whiskered sector inclusion of `F`. -/
theorem inc_whiskerRight_coupledCounit (i : ι) :
    DF.inc i ▷ E ≫ coupledCounit DE DF A = OF i ◁ DE.proj i ≫ (A i).counit := by
  have hF : DF.inc i ▷ E = ∑ j, OF i ◁ DE.proj j ≫ (DF.comp DE).inc (i, j) := by
    simp only [SectorDecomp.comp_inc]
    simp_rw [← Category.assoc, SectorDecomp.exch (DF.inc_mem i), Category.assoc,
      ← TwoSupercategory.whiskerLeft_comp (R := k)]
    rw [← Preadditive.comp_sum, ← whiskerLeft_sum (k := k), DE.total,
      TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]
  rw [hF, Preadditive.sum_comp, Finset.sum_eq_single i]
  · rw [Category.assoc, inc_coupledCounit]
  · intro j _ hj
    rw [Category.assoc, inc_coupledCounit_ne DE DF A (i, j) (Ne.symm hj), Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The unit followed by a whiskered sector projection of `F`. -/
theorem coupledUnit_whiskerLeft_proj (i : ι) :
    coupledUnit DE DF A ≫ E ◁ DF.proj i = (A i).unit ≫ DE.inc i ▷ OF i := by
  unfold coupledUnit
  rw [Preadditive.sum_comp, Finset.sum_eq_single i]
  · rw [SectorDecomp.comp_inc, Category.assoc, Category.assoc,
      ← TwoSupercategory.whiskerLeft_comp (R := k), DF.inc_proj,
      TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]
  · intro j _ hj
    rw [SectorDecomp.comp_inc, Category.assoc, Category.assoc,
      ← TwoSupercategory.whiskerLeft_comp (R := k), DF.inc_proj_ne j i hj,
      whiskerLeft_zero' (k := k), Limits.comp_zero, Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The unit followed by a whiskered sector projection of `E`. -/
theorem coupledUnit_proj_whiskerRight (i : ι) :
    coupledUnit DE DF A ≫ DE.proj i ▷ F = (A i).unit ≫ OE i ◁ DF.inc i := by
  unfold coupledUnit
  rw [Preadditive.sum_comp, Finset.sum_eq_single i]
  · rw [SectorDecomp.comp_inc, Category.assoc, Category.assoc, SectorDecomp.exch (DE.proj_mem i),
      ← Category.assoc (DE.inc i ▷ OF i), ← TwoSupercategory.comp_whiskerRight (R := k),
      DE.inc_proj, TwoSupercategory.id_whiskerRight (R := k), Category.id_comp]
  · intro j _ hj
    rw [SectorDecomp.comp_inc, Category.assoc, Category.assoc, SectorDecomp.exch (DE.proj_mem i),
      ← Category.assoc (DE.inc j ▷ OF j), ← TwoSupercategory.comp_whiskerRight (R := k),
      DE.inc_proj_ne j i hj, zero_whiskerRight' (k := k), Limits.zero_comp, Limits.comp_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The coupled adjunction.** The diagonal sum of the sector adjunctions, with
both triangle identities. -/
def coupledAdjunction : SuperAdjunction (k := k) E F where
  unit := coupledUnit DE DF A
  counit := coupledCounit DE DF A
  unit_mem := Submodule.sum_mem _ fun i _ => even_comp_mem (A i).unit_mem
    ((DE.comp DF).inc_mem (i, i))
  counit_mem := Submodule.sum_mem _ fun i _ => even_comp_mem ((DF.comp DE).proj_mem (i, i))
    (A i).counit_mem
  left_triangle := DE.ext fun i => by
    rw [Category.comp_id,
      TwoSupercategory.leftUnitor_inv_naturality_assoc k,
      ← TwoSupercategory.whisker_exchange_of_even_right_assoc _ (DE.inc_mem i),
      TwoSupercategory.associator_naturality_right_assoc k,
      ← TwoSupercategory.whiskerLeft_comp'_assoc k, whiskerLeft_inc_coupledCounit,
      TwoSupercategory.whiskerLeft_comp'_assoc k,
      ← TwoSupercategory.associator_naturality_middle_assoc k,
      ← TwoSupercategory.comp_whiskerRight'_assoc k, coupledUnit_whiskerLeft_proj,
      TwoSupercategory.comp_whiskerRight'_assoc k,
      TwoSupercategory.associator_naturality_left_assoc k,
      ← SectorDecomp.exch_assoc (DE.inc_mem i),
      TwoSupercategory.rightUnitor_naturality k]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (· ≫ DE.inc i) (A i).left_triangle
  right_triangle := DF.ext fun i => by
    rw [Category.comp_id,
      TwoSupercategory.rightUnitor_inv_naturality_assoc k,
      TwoSupercategory.whisker_exchange_of_even_left_assoc (DF.inc_mem i),
      TwoSupercategory.associator_inv_naturality_left_assoc k,
      ← TwoSupercategory.comp_whiskerRight'_assoc k, inc_whiskerRight_coupledCounit,
      TwoSupercategory.comp_whiskerRight'_assoc k,
      ← TwoSupercategory.associator_inv_naturality_middle_assoc k,
      ← TwoSupercategory.whiskerLeft_comp'_assoc k, coupledUnit_proj_whiskerRight,
      TwoSupercategory.whiskerLeft_comp'_assoc k,
      TwoSupercategory.associator_inv_naturality_right_assoc k,
      ← TwoSupercategory.whisker_exchange_of_even_left_assoc (A i).counit_mem,
      TwoSupercategory.leftUnitor_naturality k]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (· ≫ DF.inc i) (A i).right_triangle

end Adjunction

/-! ## Two separated sectors -/

/-- The two separated sectors of a coupled raising functor: the reservoir, with
nilpotent dots, and the probe, with invertible dots. -/
inductive CoupledSector
  | reservoir
  | probe
  deriving DecidableEq

open CoupledSector

instance : Fintype CoupledSector where
  elems := {reservoir, probe}
  complete x := by cases x <;> simp

/-- Two separated factors at consecutive weights `a → b → c`, with sector
decompositions of the coupled raising and lowering 1-morphisms. The sector
data are the factor adjunctions, dots and diagonal crossings with their upward
slides, the sector-swapping crossing blocks with their dot intertwining,
two-sided inverses of the probe dots and nilpotence of the reservoir dots. The
position-preserving cross-sector blocks are not data: they are the rational
entries `rationalRP`, `rationalPR`. -/
structure CoupledFactors (a b c : B) where
  E₁ : a ⟶ b
  F₁ : b ⟶ a
  E₂ : b ⟶ c
  F₂ : c ⟶ b
  O₁ : CoupledSector → (a ⟶ b)
  P₁ : CoupledSector → (b ⟶ a)
  O₂ : CoupledSector → (b ⟶ c)
  P₂ : CoupledSector → (c ⟶ b)
  DE₁ : SectorDecomp (k := k) E₁ CoupledSector O₁
  DF₁ : SectorDecomp (k := k) F₁ CoupledSector P₁
  DE₂ : SectorDecomp (k := k) E₂ CoupledSector O₂
  DF₂ : SectorDecomp (k := k) F₂ CoupledSector P₂
  adj₁ : ∀ s, SuperAdjunction (k := k) (O₁ s) (P₁ s)
  adj₂ : ∀ s, SuperAdjunction (k := k) (O₂ s) (P₂ s)
  p : ZMod 2
  dot₁ : ∀ s, O₁ s ⟶ O₁ s
  dot₂ : ∀ s, O₂ s ⟶ O₂ s
  dot₁_mem : ∀ s, dot₁ s ∈ parity (R := k) _ _ p
  dot₂_mem : ∀ s, dot₂ s ∈ parity (R := k) _ _ p
  cross : ∀ s, O₁ s ≫ O₂ s ⟶ O₁ s ≫ O₂ s
  cross_slide : ∀ s, cross s ≫ O₁ s ◁ dot₂ s -
    koszulSign p p • (dot₁ s ▷ O₂ s ≫ cross s) = 𝟙 _
  swapRP : O₁ reservoir ≫ O₂ probe ⟶ O₁ probe ≫ O₂ reservoir
  swapRP_slide : swapRP ≫ O₁ probe ◁ dot₂ reservoir =
    koszulSign p p • (dot₁ reservoir ▷ O₂ probe ≫ swapRP)
  swapPR : O₁ probe ≫ O₂ reservoir ⟶ O₁ reservoir ≫ O₂ probe
  swapPR_slide : swapPR ≫ O₁ reservoir ◁ dot₂ probe =
    koszulSign p p • (dot₁ probe ▷ O₂ reservoir ≫ swapPR)
  inv₁ : O₁ probe ⟶ O₁ probe
  dot₁_inv₁ : dot₁ probe ≫ inv₁ = 𝟙 _
  inv₁_dot₁ : inv₁ ≫ dot₁ probe = 𝟙 _
  inv₂ : O₂ probe ⟶ O₂ probe
  dot₂_inv₂ : dot₂ probe ≫ inv₂ = 𝟙 _
  inv₂_dot₂ : inv₂ ≫ dot₂ probe = 𝟙 _
  N : ℕ
  nil₁ : rouquierPower (dot₁ reservoir) N = 0
  nil₂ : rouquierPower (dot₂ reservoir) N = 0

namespace CoupledFactors
variable {a b c : B} (C : CoupledFactors (k := k) a b c)

/-- The coupled source dot: diagonal with the sector dots. -/
def x₁ : C.E₁ ⟶ C.E₁ := C.DE₁.diag C.dot₁

/-- The coupled target dot: diagonal with the sector dots. -/
def x₂ : C.E₂ ⟶ C.E₂ := C.DE₂.diag C.dot₂

/-- The coupled source adjunction. -/
def A₁ : SuperAdjunction (k := k) C.E₁ C.F₁ := coupledAdjunction C.DE₁ C.DF₁ C.adj₁

/-- The coupled target adjunction. -/
def A₂ : SuperAdjunction (k := k) C.E₂ C.F₂ := coupledAdjunction C.DE₂ C.DF₂ C.adj₂

/-- The position-preserving reservoir-then-probe crossing block. -/
def rationalRP : C.O₁ reservoir ≫ C.O₂ probe ⟶ C.O₁ reservoir ≫ C.O₂ probe :=
  coupledRationalLeft (R := End (C.O₁ reservoir ≫ C.O₂ probe)) (koszulSign C.p C.p)
    (C.dot₁ reservoir ▷ C.O₂ probe) (C.O₁ reservoir ◁ C.inv₂) C.N

/-- The position-preserving probe-then-reservoir crossing block. -/
def rationalPR : C.O₁ probe ≫ C.O₂ reservoir ⟶ C.O₁ probe ≫ C.O₂ reservoir :=
  coupledRationalRight (R := End (C.O₁ probe ≫ C.O₂ reservoir)) (koszulSign C.p C.p)
    (C.O₁ probe ◁ C.dot₂ reservoir) (C.inv₁ ▷ C.O₂ reservoir) C.N

theorem rationalRP_slide : C.rationalRP ≫ C.O₁ reservoir ◁ C.dot₂ probe -
    koszulSign C.p C.p • (C.dot₁ reservoir ▷ C.O₂ probe ≫ C.rationalRP) = 𝟙 _ :=
  coupledRationalLeft_spec (R := End (C.O₁ reservoir ≫ C.O₂ probe)) (koszulSign C.p C.p)
    (X := C.dot₁ reservoir ▷ C.O₂ probe) (Y := C.O₁ reservoir ◁ C.dot₂ probe)
    (Z := C.O₁ reservoir ◁ C.inv₂) C.N
    (show C.O₁ reservoir ◁ C.inv₂ ≫ C.O₁ reservoir ◁ C.dot₂ probe = 𝟙 _ by
      rw [← TwoSupercategory.whiskerLeft_comp (R := k), C.inv₂_dot₂,
        TwoSupercategory.whiskerLeft_id (R := k)])
    (by rw [whiskerRight_rouquierPower (k := k), C.nil₁, zero_whiskerRight' (k := k)])

theorem rationalPR_slide : C.rationalPR ≫ C.O₁ probe ◁ C.dot₂ reservoir -
    koszulSign C.p C.p • (C.dot₁ probe ▷ C.O₂ reservoir ≫ C.rationalPR) = 𝟙 _ :=
  coupledRationalRight_spec (R := End (C.O₁ probe ≫ C.O₂ reservoir))
    (koszulSign_mul_self C.p C.p)
    (X := C.O₁ probe ◁ C.dot₂ reservoir) (Y := C.dot₁ probe ▷ C.O₂ reservoir)
    (Z := C.inv₁ ▷ C.O₂ reservoir) C.N
    (show C.dot₁ probe ▷ C.O₂ reservoir ≫ C.inv₁ ▷ C.O₂ reservoir = 𝟙 _ by
      rw [← TwoSupercategory.comp_whiskerRight (R := k), C.dot₁_inv₁,
        TwoSupercategory.id_whiskerRight (R := k)])
    (by rw [whiskerLeft_rouquierPower (k := k), C.nil₂, whiskerLeft_zero' (k := k)])

/-- The blocks of the coupled crossing on the four summands of `E₁ ≫ E₂`. -/
def crossEntry : ∀ x y : CoupledSector × CoupledSector,
    C.O₁ x.1 ≫ C.O₂ x.2 ⟶ C.O₁ y.1 ≫ C.O₂ y.2
  | (reservoir, reservoir), (reservoir, reservoir) => C.cross reservoir
  | (probe, probe), (probe, probe) => C.cross probe
  | (reservoir, probe), (reservoir, probe) => C.rationalRP
  | (probe, reservoir), (probe, reservoir) => C.rationalPR
  | (reservoir, probe), (probe, reservoir) => C.swapRP
  | (probe, reservoir), (reservoir, probe) => C.swapPR
  | _, _ => 0

/-- **The coupled crossing**: the block matrix of `crossEntry`. -/
def coupledCross : C.E₁ ≫ C.E₂ ⟶ C.E₁ ≫ C.E₂ := (C.DE₁.comp C.DE₂).mat C.crossEntry

/-- **The coupled crossing slide.** -/
theorem slide : C.coupledCross ≫ C.E₁ ◁ C.x₂ -
    koszulSign C.p C.p • (C.x₁ ▷ C.E₂ ≫ C.coupledCross) = 𝟙 (C.E₁ ≫ C.E₂) := by
  rw [x₂, x₁, C.DE₁.diag_whiskerLeft C.DE₂, C.DE₁.diag_whiskerRight C.DE₂, coupledCross,
    SectorDecomp.mat_comp_diag, SectorDecomp.diag_comp_mat, SectorDecomp.mat_sub_zsmul]
  apply SectorDecomp.mat_eq_id
  · rintro ⟨_ | _, _ | _⟩
    · exact C.cross_slide reservoir
    · exact C.rationalRP_slide
    · exact C.rationalPR_slide
    · exact C.cross_slide probe
  · rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ h <;>
      first
      | exact absurd rfl h
      | exact sub_eq_zero.mpr C.swapRP_slide
      | exact sub_eq_zero.mpr C.swapPR_slide
      | exact (show (0 : _ ⟶ _) ≫ _ - koszulSign C.p C.p • (_ ≫ (0 : _ ⟶ _)) = 0 by simp)

/-- The source sectors of the coupled adjunction. -/
def sourceSector (s : CoupledSector) : SourceSector C.A₁ C.x₁ where
  E := C.O₁ s
  F := C.P₁ s
  adj := C.adj₁ s
  dot := C.dot₁ s
  dot_mem := ⟨C.p, C.dot₁_mem s⟩
  iE := C.DE₁.inc s
  iF := C.DF₁.inc s
  iF_mem := C.DF₁.inc_mem s
  dot_comm := C.DE₁.inc_diag C.dot₁ s
  counit_comm := inc_coupledCounit C.DE₁ C.DF₁ C.adj₁ s

/-- The target sectors of the coupled adjunction. -/
def targetSector (s : CoupledSector) : TargetSector C.A₂ C.x₂ where
  E := C.O₂ s
  F := C.P₂ s
  adj := C.adj₂ s
  dot := C.dot₂ s
  dot_mem := ⟨C.p, C.dot₂_mem s⟩
  pE := C.DE₂.proj s
  pF := C.DF₂.proj s
  pF_mem := C.DF₂.proj_mem s
  dot_comm := C.DE₂.diag_proj C.dot₂ s
  unit_comm := coupledUnit_proj C.DE₂ C.DF₂ C.adj₂ s

/-- **The mate projection formula of the coupled crossing.** The coordinates are
the actual dotted sector cups and caps, with powers of the probe inverses for
negative indices. -/
theorem mateProjectionFormula :
    SuperRouquierLoc.MateProjectionFormula C.A₁ C.A₂ C.coupledCross C.p
      (sectorIn (C.DE₁.inc reservoir) (C.DF₁.inc reservoir))
      (sectorIn (C.DE₁.inc probe) (C.DF₁.inc probe))
      (sectorOut (C.DE₂.proj reservoir) (C.DF₂.proj reservoir))
      (sectorOut (C.DE₂.proj probe) (C.DF₂.proj probe))
      (C.targetSector reservoir).cup (C.sourceSector reservoir).cap
      (probeCup (C.targetSector probe) C.inv₂) (probeCap (C.sourceSector probe) C.inv₁)
      C.N C.N :=
  SuperRouquierLoc.MateProjectionFormula.of_sectors C.coupledCross C.p C.slide
    (C.sourceSector reservoir) (C.sourceSector probe)
    (C.targetSector reservoir) (C.targetSector probe)
    C.inv₁ C.inv₁_dot₁ C.inv₂ C.dot₂_inv₂ C.N C.N C.nil₂ C.nil₁

end CoupledFactors

end OddMath.SKM
