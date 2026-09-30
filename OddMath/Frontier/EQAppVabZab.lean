import OddMath.Frontier.EQAppVab
import OddMath.Frontier.EQLimaOsym
import OddMath.Frontier.EQZabCell
import OddMath.Frontier.EQZabSchur

/-!
# Ellis–Qi, Appendix A.3: the cohomology of `V_{a,b}`

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.3 and Corollary 4.8 (printed numbering).  `V_{a,b} ⊆ Z_{a,b}` is the `ℤ`-span of
`{s̃_λ(y) z : λ ∈ Par(b,a)}`; by (4.21) (`EQZab.zab_span`, `EQZab.zab_indep`),
`Z_{a,b} ≅ V_{a,b} ⊗ OΛ_{a+b}`, so `V_{a,b}` controls the finite-cell filtration of
`OΛ_a ⊗ OΛ_b` by shifts of the regular dg module over `OΛ_{a+b}`.

Here `V_{a,b}` is the concrete subcomplex of `EQZab`: in the untwisted model (`EQZab.schurSpan`,
differential `EQZab.dZ`, basis `s_λ(y)`) and literally (`EQZab.schurSpanT`, differential
Definition 4.6 `EQZab.dT`, basis `s̃_λ(y) z`).  Partitions are Young diagrams in the `b × a` box,
`s_λ = EQSchur.untwisted b (rowExp b λ)`.

* `vBasis`, `vBasisT`: the Schur functions form a `ℤ`-basis of `V_{a,b}` (independence from
  (4.21)).
* `actsByBoxes_dV`, `actsByBoxes_dVT`: Lemma 4.7 (`EQZab.lemma_4_7_box`,
  `EQZab.lemma_4_7_box_twisted`) is the formula of `EQApp.VFormula`.
* **`a` even** (`homologyV_even`, `homologyVT_even`): `H(V_{a,b})` is a free abelian group with
  basis the classes of the Lima Schur functions `s̃_λ(y) z`, `λ ∈ Par(b,a)` Lima — as printed.
* **`a` odd**: `H(V_{a,b})` is free with basis `s̃_λ(y) z`, `λ ∈ Par(b,a)` with `IsOddLima b λ`
  (`homologyV_odd`, `homologyVT_odd`); it vanishes for `b` odd (`homologyV_odd_odd`,
  `homologyVT_odd_odd`), but **not for `b` even**: the class of `s̃_{(a^b)}(y) z` is nonzero
  (`homologyV_rectangle_ne_zero`, `homologyVT_rectangle_ne_zero`), refuting the printed
  "`H(V_{a,b}) = 0` for `a` odd".
-/

namespace OddMath.Frontier.EQApp

open Finset OddMath.Frontier.EQLima
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open OddMath.Frontier.EQSkewDifferential OddMath.Frontier.EQSchur OddMath.Frontier.EQZab

noncomputable section

local instance (priority := high) eqAppVabNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) eqAppVabNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {a b : ℕ}

/-! ### Partitions in the box and exponent vectors -/

/-- The index set `P(b,a)` of the basis (4.21), as a finite type. -/
abbrev BoxIdx (b a : ℕ) : Type := {e : Fin b → ℕ // e ∈ BoxPartitionCount.box b a}

theorem rowExp_mem_box (μ : {μ : YoungDiagram // InBox b a μ}) :
    rowExp b μ.1 ∈ BoxPartitionCount.box b a :=
  BoxPartitionCount.mem_box.mpr ⟨rowExp_antitone b μ.1, fun i => rowLen_le_of_inBox μ.2 i⟩

/-- The extension by zero of an exponent vector. -/
def extExp (e : Fin b → ℕ) (i : ℕ) : ℕ := if h : i < b then e ⟨i, h⟩ else 0

theorem extExp_antitone {e : Fin b → ℕ} (he : Antitone e) : Antitone (extExp e) := by
  intro i j hij
  unfold extExp
  by_cases hj : j < b
  · simp only [hj, show i < b by omega, ↓reduceDIte]
    exact he (Fin.mk_le_mk.mpr hij)
  · simp only [hj, ↓reduceDIte]; exact Nat.zero_le _

theorem extExp_zero (e : Fin b → ℕ) : ∀ i, b ≤ i → extExp e i = 0 :=
  fun i hi => by unfold extExp; simp only [show ¬ i < b by omega, ↓reduceDIte]

/-- The Young diagram of an element of `P(b,a)`. -/
def ydOfBox (e : BoxIdx b a) : {μ : YoungDiagram // InBox b a μ} :=
  ⟨ydOf (extExp e.1) (extExp_antitone (BoxPartitionCount.mem_box.mp e.2).1) b, fun c hc => by
    rw [mem_ydOf (extExp_zero e.1)] at hc
    unfold extExp at hc
    split_ifs at hc with h
    · exact ⟨h, lt_of_lt_of_le hc ((BoxPartitionCount.mem_box.mp e.2).2 _)⟩
    · omega⟩

theorem mem_ydOfBox (e : BoxIdx b a) {c : ℕ × ℕ} : c ∈ (ydOfBox e).1 ↔ c.2 < extExp e.1 c.1 :=
  mem_ydOf (hr := extExp_antitone (BoxPartitionCount.mem_box.mp e.2).1) (extExp_zero _)

theorem rowLen_ydOfBox (e : BoxIdx b a) (i : ℕ) : (ydOfBox e).1.rowLen i = extExp e.1 i :=
  rowLen_ydOf (hr := extExp_antitone (BoxPartitionCount.mem_box.mp e.2).1) (extExp_zero _) i

/-- `Par(b,a)` (Young diagrams in the `b × a` box) `≃ P(b,a)` (antitone `b`-tuples `≤ a`). -/
def boxEquiv (b a : ℕ) : {μ : YoungDiagram // InBox b a μ} ≃ BoxIdx b a where
  toFun μ := ⟨rowExp b μ.1, rowExp_mem_box μ⟩
  invFun := ydOfBox
  left_inv μ := by
    apply Subtype.ext
    apply YoungDiagram.ext
    ext ⟨i, j⟩
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, mem_ydOfBox,
      YoungDiagram.mem_iff_lt_rowLen]
    unfold extExp
    split_ifs with h
    · rfl
    · rw [rowLen_eq_zero_of_inBox μ.2 (by simp only at h ⊢; omega)]
  right_inv e := by
    apply Subtype.ext
    funext i
    change (ydOfBox e).1.rowLen i.val = e.1 i
    rw [rowLen_ydOfBox, extExp]
    simp only [i.2, ↓reduceDIte]

/-! ### The basis of `V_{a,b}` -/

theorem zsmul_one_eq_zero {N : ℕ} {g : ℤ} (h : g • (1 : SkewPolynomial N) = 0) : g = 0 := by
  have h0 := congrArg (fun f : SkewPolynomial N => f 0) h
  change g * (1 : SkewPolynomial N) 0 = 0 at h0
  have h1 : (1 : SkewPolynomial N) 0 = 1 := by
    change (OddMath.SkewPolynomial.monomial 0 1 : SkewPolynomial N) 0 = 1
    simp [OddMath.SkewPolynomial.monomial]
  rw [h1, mul_one] at h0
  exact h0

/-- Linear independence of `s_λ(y)` (resp. `s̃_λ(y)`), `λ ∈ P(b,a)`, from (4.21). -/
theorem linearIndependent_box (F : (Fin b → ℕ) → SkewPolynomial (a+b))
    (ψ : SkewPolynomial (a+b) →+* SkewPolynomial (a+b))
    (hind : ∀ c : (Fin b → ℕ) → SkewPolynomial (a+b), (∀ μ, c μ ∈ osym (a+b)) →
      ∑ μ ∈ BoxPartitionCount.box b a, F μ * ψ (c μ) = 0 →
        ∀ μ ∈ BoxPartitionCount.box b a, c μ = 0) :
    LinearIndependent ℤ (fun e : BoxIdx b a => F e.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg e
  set c : (Fin b → ℕ) → SkewPolynomial (a+b) := fun x =>
    if h : x ∈ BoxPartitionCount.box b a then g ⟨x, h⟩ • (1 : SkewPolynomial (a+b)) else 0
  have hc : ∀ x, c x ∈ osym (a+b) := fun x => by
    simp only [c]
    split_ifs
    · exact Subring.zsmul_mem _ (Subring.one_mem _) _
    · exact Subring.zero_mem _
  have hsum : ∑ μ ∈ BoxPartitionCount.box b a, F μ * ψ (c μ) = 0 := by
    rw [← Finset.sum_coe_sort, ← hg]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [c, x.2, ↓reduceDIte, map_zsmul, map_one, mul_smul_comm, mul_one]
  have := hind c hc hsum e.1 e.2
  simp only [c, e.2, ↓reduceDIte] at this
  exact zsmul_one_eq_zero this

/-- The Schur functions `s_λ(y)` of `V_{a,b}` (untwisted model), indexed by `Par(b,a)`. -/
def vFam (a b : ℕ) (μ : {μ : YoungDiagram // InBox b a μ}) : SkewPolynomial (a+b) :=
  inclY a b (untwisted b (rowExp b μ.1))

/-- The Schur functions `s̃_λ(y) z` of `V_{a,b}` (literal twisted model). -/
def vFamT (a b : ℕ) (μ : {μ : YoungDiagram // InBox b a μ}) : SkewPolynomial (a+b) :=
  inclY a b (twisted b (rowExp b μ.1))

theorem linearIndependent_vFam : LinearIndependent ℤ (vFam a b) := by
  have := (linearIndependent_box (fun e => inclY a b (untwisted b e)) (phiAB a b)
    (fun c hc h => zab_indep c hc h)).comp (boxEquiv b a) (boxEquiv b a).injective
  exact this

theorem linearIndependent_vFamT : LinearIndependent ℤ (vFamT a b) := by
  have := (linearIndependent_box (fun e => inclY a b (twisted b e)) (twistRev (a+b))
    (fun c hc h => zab_indep_twisted c hc h)).comp (boxEquiv b a) (boxEquiv b a).injective
  exact this

theorem span_range_box (F : (Fin b → ℕ) → SkewPolynomial (a+b)) :
    Submodule.span ℤ (Set.range fun μ : {μ : YoungDiagram // InBox b a μ} => F (rowExp b μ.1)) =
      Submodule.span ℤ (Set.range fun μ : ParBox b a => F μ.val) := by
  congr 1
  ext f
  constructor
  · rintro ⟨μ, rfl⟩
    exact ⟨⟨rowExp b μ.1, BoxPartitionCount.mem_box.mp (rowExp_mem_box μ)⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    refine ⟨(boxEquiv b a).symm ⟨e.1, BoxPartitionCount.mem_box.mpr e.2⟩, ?_⟩
    have := congrArg Subtype.val ((boxEquiv b a).apply_symm_apply ⟨e.1,
      BoxPartitionCount.mem_box.mpr e.2⟩)
    change F (rowExp b _) = F e.1
    rw [show rowExp b ((boxEquiv b a).symm ⟨e.1, BoxPartitionCount.mem_box.mpr e.2⟩).1 = e.1
      from this]

/-- **The basis of `V_{a,b}`** (untwisted model): `{s_λ(y) : λ ∈ Par(b,a)}`. -/
def vBasis (a b : ℕ) : Module.Basis {μ : YoungDiagram // InBox b a μ} ℤ (schurSpan a b) :=
  (Module.Basis.span (linearIndependent_vFam (a := a) (b := b))).map
    (LinearEquiv.ofEq _ _ (span_range_box (a := a) (fun e => inclY a b (untwisted b e))))

theorem vBasis_apply (μ : {μ : YoungDiagram // InBox b a μ}) :
    (vBasis a b μ : SkewPolynomial (a+b)) = vFam a b μ := by
  simp [vBasis, Module.Basis.span_apply]

/-- **The basis of `V_{a,b}`** (literally): `{s̃_λ(y) z : λ ∈ Par(b,a)}`. -/
def vBasisT (a b : ℕ) : Module.Basis {μ : YoungDiagram // InBox b a μ} ℤ (schurSpanT a b) :=
  (Module.Basis.span (linearIndependent_vFamT (a := a) (b := b))).map
    (LinearEquiv.ofEq _ _ (span_range_box (a := a) (fun e => inclY a b (twisted b e))))

theorem vBasisT_apply (μ : {μ : YoungDiagram // InBox b a μ}) :
    (vBasisT a b μ : SkewPolynomial (a+b)) = vFamT a b μ := by
  simp [vBasisT, Module.Basis.span_apply]

/-! ### The differential -/

/-- The differential of `V_{a,b}` (untwisted model). -/
def dV (a b : ℕ) : schurSpan a b →ₗ[ℤ] schurSpan a b where
  toFun x := ⟨dZ a b x, cor_4_8_stable x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_zsmul _ _ _)

/-- The differential of `V_{a,b}` (Definition 4.6). -/
def dVT (a b : ℕ) : schurSpanT a b →ₗ[ℤ] schurSpanT a b where
  toFun x := ⟨dT a b x, cor_4_8_stable_twisted x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_zsmul _ _ _)

theorem vA_eq (μ : {μ : YoungDiagram // InBox b a μ}) :
    (vSystem a b).A μ =
      (univ.filter fun i : Fin b => Addable μ.1 (i.val, μ.1.rowLen i) ∧
        VCol a (i.val, μ.1.rowLen i) ∧ μ.1.rowLen i < a).map
        ⟨fun i : Fin b => (i.val, μ.1.rowLen i), fun _ _ h => Fin.ext (congrArg Prod.fst h)⟩ := by
  ext ⟨x, y⟩
  rw [mem_vSystem_A, Finset.mem_map]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hc, hx, hy, hadd⟩
    have hyx := ((addable_iff_rowLen μ.1 x y).mp hadd).1
    subst hyx
    exact ⟨⟨x, hx⟩, ⟨hadd, hc, hy⟩, rfl, rfl⟩
  · rintro ⟨i, ⟨hadd, hc, hy⟩, rfl, rfl⟩
    exact ⟨hc, i.2, hy, hadd⟩

theorem vCoeff_mod (μ : YoungDiagram) (i : Fin b) :
    ((a : ℤ) + EQSchur.content (rowExp b μ) i) % 2 =
      if VCol a (i.val, μ.rowLen i) then 1 else 0 := by
  rw [EQSchur.content]
  simp only [rowExp, VCol]
  split_ifs with h <;> omega

/-- The box formula of Lemma 4.7 on a family `F` indexed by exponent vectors gives
`EQApp.VFormula` for any basis of a submodule whose members are `F (rowExp b λ)`. -/
theorem actsByBoxes_of_formula {V : Submodule ℤ (SkewPolynomial (a+b))}
    (s : Module.Basis {μ : YoungDiagram // InBox b a μ} ℤ V) (D : V →ₗ[ℤ] V)
    (D' : SkewPolynomial (a+b) →+ SkewPolynomial (a+b)) (F : (Fin b → ℕ) → SkewPolynomial (a+b))
    (hs : ∀ μ, (s μ : SkewPolynomial (a+b)) = F (rowExp b μ.1))
    (hD : ∀ x, (D x : SkewPolynomial (a+b)) = D' x)
    (hF : ∀ l : Fin b → ℕ, Antitone l → (∀ j, l j ≤ a) → D' (F l) =
      ∑ i, if Antitone (l + expSingle i) ∧ l i < a then
        ((-1 : ℤ) ^ (rowsAbove l i + i.val) * (((a : ℤ) + EQSchur.content l i) % 2)) •
          F (l + expSingle i)
      else 0) :
    VFormula s D := by
  classical
  intro μ
  apply Subtype.ext
  rw [hD, hs, hF _ (rowExp_antitone b μ.1) (fun j => rowLen_le_of_inBox μ.2 j), vA_eq,
    AddSubmonoidClass.coe_finsetSum, Finset.sum_map, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk, SetLike.val_smul]
  have hlt : rowExp b μ.1 i < a ↔ μ.1.rowLen i < a := Iff.rfl
  by_cases hA : Addable μ.1 (i.val, μ.1.rowLen i)
  · have hA' := (addable_iff_antitone μ.1 i).mp hA
    rw [vCoeff_mod, rowsAbove_rowExp]
    by_cases hW : VCol a (i.val, μ.1.rowLen i)
    · by_cases ha : μ.1.rowLen i < a
      · have hmem : (i.val, μ.1.rowLen i) ∈ (vSystem a b).A μ :=
          mem_vSystem_A.mpr ⟨hW, i.2, ha, hA⟩
        simp only [hA', hW, hA, ha, hlt, and_self, ↓reduceIte, mul_one]
        rw [hs, vSystem_add_val hmem, rowExp_addCell hA, schurSign]
        push_cast
        rfl
      · simp [hA', hW, hA, ha, hlt]
    · simp [hA', hW, hA, hlt]
  · have hA' : ¬ Antitone (rowExp b μ.1 + expSingle i) := fun h =>
      hA ((addable_iff_antitone μ.1 i).mpr h)
    simp [hA, hA']

/-- **Lemma 4.7 on `V_{a,b}`** (untwisted model). -/
theorem actsByBoxes_dV : VFormula (vBasis a b) (dV a b) :=
  actsByBoxes_of_formula (vBasis a b) (dV a b) (dZ a b) (fun e => inclY a b (untwisted b e))
    vBasis_apply (fun _ => rfl) (fun l hl hla => lemma_4_7_box l hl hla)

/-- **Lemma 4.7 on `V_{a,b}`** (literally, Definition 4.6). -/
theorem actsByBoxes_dVT : VFormula (vBasisT a b) (dVT a b) :=
  actsByBoxes_of_formula (vBasisT a b) (dVT a b) (dT a b) (fun e => inclY a b (twisted b e))
    vBasisT_apply (fun _ => rfl) (fun l hl hla => lemma_4_7_box_twisted l hl hla)

/-! ### Hypercube decomposition -/

/-- **Ellis–Qi, Appendix A.3**: `V_{a,b}` (with the differential of Definition 4.6) is a direct sum
of hypercube complexes, one for each partition `q ∈ Par(b,a)` without removable boxes of colour
`VCol a`; the urns of `q` are its addable boxes of that colour inside the box. -/
theorem vDecomp_dVT (x : schurSpanT a b) :
    ((vBasisT a b).repr.trans (decompEquiv (vSystem a b))) (dVT a b x) =
      DFinsupp.mapRange.linearMap (fun q => hyperDelta (vSystem a b)
        (fun μ c => schurSign μ.1 c) q) (((vBasisT a b).repr.trans (decompEquiv (vSystem a b))) x) :=
  actsByBoxes_decomp actsByBoxes_dVT x

/-! ### The cohomology of `V_{a,b}` -/

/-- **Ellis–Qi, Appendix A.3, `a` even**: `H(V_{a,b})` is a free abelian group with basis the
classes of the Lima Schur functions `s_λ(y)`, `λ ∈ Par(b,a)` a Lima partition. -/
def homologyV_even (ha : Even a) :
    Module.Basis {μ : YoungDiagram // IsLima μ ∧ InBox b a μ} ℤ (Homology (dV a b)) :=
  vHomologyBasisEven actsByBoxes_dV ha

theorem homologyV_even_apply (ha : Even a) (μ : {μ : YoungDiagram // IsLima μ ∧ InBox b a μ}) :
    ((homologyV_even ha μ : Homology (dV a b))) = Submodule.Quotient.mk
      ⟨vBasis a b ⟨μ.1, μ.2.2⟩, LinearMap.mem_ker.mpr (schur_crit_cocycle actsByBoxes_dV
        ((vCrit_iff_even ha ⟨μ.1, μ.2.2⟩).mpr μ.2.1))⟩ :=
  vHomologyBasisEven_apply actsByBoxes_dV ha μ

/-- **Ellis–Qi, Appendix A.3, `a` even**, literally: `H(V_{a,b})` is a free abelian group with basis
the classes of `s̃_λ(y) z`, `λ ∈ Par(b,a)` a Lima partition. -/
def homologyVT_even (ha : Even a) :
    Module.Basis {μ : YoungDiagram // IsLima μ ∧ InBox b a μ} ℤ (Homology (dVT a b)) :=
  vHomologyBasisEven actsByBoxes_dVT ha

theorem homologyVT_even_apply (ha : Even a) (μ : {μ : YoungDiagram // IsLima μ ∧ InBox b a μ}) :
    ((homologyVT_even ha μ : Homology (dVT a b))) = Submodule.Quotient.mk
      ⟨vBasisT a b ⟨μ.1, μ.2.2⟩, LinearMap.mem_ker.mpr (schur_crit_cocycle actsByBoxes_dVT
        ((vCrit_iff_even ha ⟨μ.1, μ.2.2⟩).mpr μ.2.1))⟩ :=
  vHomologyBasisEven_apply actsByBoxes_dVT ha μ

/-- **`a` odd, corrected**: `H(V_{a,b})` is a free abelian group with basis the classes of
`s_λ(y)`, `λ ∈ Par(b,a)` with `IsOddLima b λ`. -/
def homologyV_odd (ha : Odd a) :
    Module.Basis {μ : YoungDiagram // IsOddLima b μ ∧ InBox b a μ} ℤ (Homology (dV a b)) :=
  vHomologyBasisOdd actsByBoxes_dV ha

/-- **`a` odd, corrected**, literally. -/
def homologyVT_odd (ha : Odd a) :
    Module.Basis {μ : YoungDiagram // IsOddLima b μ ∧ InBox b a μ} ℤ (Homology (dVT a b)) :=
  vHomologyBasisOdd actsByBoxes_dVT ha

theorem homologyVT_odd_apply (ha : Odd a)
    (μ : {μ : YoungDiagram // IsOddLima b μ ∧ InBox b a μ}) :
    ((homologyVT_odd ha μ : Homology (dVT a b))) = Submodule.Quotient.mk
      ⟨vBasisT a b ⟨μ.1, μ.2.2⟩, LinearMap.mem_ker.mpr (schur_crit_cocycle actsByBoxes_dVT
        ((vCrit_iff_odd ha ⟨μ.1, μ.2.2⟩).mpr μ.2.1))⟩ :=
  vHomologyBasisOdd_apply actsByBoxes_dVT ha μ

/-- `a`, `b` odd: `H(V_{a,b}) = 0`. -/
theorem homologyV_odd_odd (ha : Odd a) (hb : Odd b) : Subsingleton (Homology (dV a b)) :=
  vHomology_odd_odd actsByBoxes_dV ha hb

theorem homologyVT_odd_odd (ha : Odd a) (hb : Odd b) : Subsingleton (Homology (dVT a b)) :=
  vHomology_odd_odd actsByBoxes_dVT ha hb

/-- **Refutation** of "`H(V_{a,b}) = 0` for `a` odd" (Ellis–Qi, Appendix A.3): for `a` odd and
`b` even the class of `s_{(a^b)}(y)` is nonzero. -/
theorem homologyV_rectangle_ne_zero (ha : Odd a) (hb : Even b) :
    homologyV_odd ha (rectangleIdx ha hb) ≠ 0 :=
  vHomology_rectangle_ne_zero actsByBoxes_dV ha hb

/-- **Refutation**, literally: for `a` odd and `b` even the class of `s̃_{(a^b)}(y) z` in
`H(V_{a,b})` (differential of Definition 4.6) is nonzero. -/
theorem homologyVT_rectangle_ne_zero (ha : Odd a) (hb : Even b) :
    homologyVT_odd ha (rectangleIdx ha hb) ≠ 0 :=
  vHomology_rectangle_ne_zero actsByBoxes_dVT ha hb

theorem homologyVT_odd_even_nontrivial (ha : Odd a) (hb : Even b) :
    Nontrivial (Homology (dVT a b)) :=
  vHomology_odd_even_nontrivial actsByBoxes_dVT ha hb

end

end OddMath.Frontier.EQApp
