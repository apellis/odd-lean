import OddMath.Frontier.EQAppHypercube
import OddMath.Frontier.EQLimaCohomology

/-!
# Ellis–Qi, Appendix A.3: the complex `V_{a,b}` (abstract part)

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.3 (printed numbering).  The complex `V_{a,b}` has basis `{s_λ 1_z : λ ∈ Par(b,a)}`
(partitions with at most `b` rows and at most `a` columns, as in Lemma 4.7: the formula below only
preserves this box) and differential
`d(s_λ 1_z) = Σ_{μ = λ + □_i ∈ Par(b,a)} (-1)^{|λ/i| + i - 1} {a + ct(□_i)} s_μ 1_z`.

Here this is treated abstractly: a module `M` with a basis indexed by the Young diagrams in the
`b × a` box and a differential given by the formula above (`ActsByBoxes (vSystem a b) …`).  Rows
and columns are `0`-based, so `ct(i, j) = j - i` and the sign is `schurSign` (`(-1)^{|λ/i| + i}`).
The coefficient `{a + ct(□)}` is `1` exactly for the boxes of colour `VCol a`:
`a + j - i` odd, i.e. white boxes if `a` is even and black boxes if `a` is odd.

* `vSystem a b`: partitions in the `b × a` box, with the addable/removable boxes of colour
  `VCol a` inside the box, as an `EQLima.BoxSystem`; it is a direct sum of hypercube complexes
  (`EQApp.decompEquiv_delta`).
* **`a` even** (`vCrit_iff_even`, `vHomologyBasisEven`): the critical partitions are exactly the
  Lima partitions in the box, so `H(V_{a,b})` is free with basis the classes of the Lima Schur
  functions `s_λ`, `λ ∈ Par(b,a)` Lima — as printed.
* **`a` odd** (`vCrit_iff_odd`, `vHomologyBasisOdd`): the critical partitions are the partitions
  `λ` with exactly `b` rows, `b` even, all parts odd and `λ_{2k} = λ_{2k+1}` (`IsOddLima b`;
  equivalently `λ = (1^b) + ν` with `ν ∈ Par(b, a-1)` a Lima partition).  Hence:
  - `vHomology_odd_odd`: `H(V_{a,b}) = 0` if `a` and `b` are odd;
  - **the printed claim "`H(V_{a,b}) = 0` for `a` odd" is false when `b` is even**
    (`vHomology_odd_even_nontrivial`, over any nontrivial ring): e.g. the full rectangle `(a^b)`
    (`rectangle_isOddLima`) and `(1^b)` are cocycles which are not coboundaries.  The printed
    reason, "no partition has neither addable nor removable white [black] boxes", holds without
    the box constraint, but in the `b × a` box with `b` even the rectangle `(a^b)` has no addable
    box and its only removable box has content `a - b`, which is odd.  The smallest instance is
    `a = 1`, `b = 2`: `V_{1,2}` has basis `∅, (1), (1,1)`, `d(∅) = ±(1)`, `d((1)) = 0` (the box
    `(1,0)` has content `-1` and `{1 - 1} = 0`) and `d((1,1)) = 0`, so `H(V_{1,2}) ≅ k` spanned by
    `[s_{(1,1)}]`.
-/

namespace OddMath.Frontier.EQApp

open Finset OddMath.Frontier.EQLima

/-! ### Young diagrams from row lengths -/

/-- The Young diagram with row lengths `r` (antitone, zero from row `n` on). -/
def ydOf (r : ℕ → ℕ) (hr : Antitone r) (n : ℕ) : YoungDiagram where
  cells := (range n ×ˢ range (r 0)).filter fun c => c.2 < r c.1
  isLowerSet := by
    intro x y hxy hx
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have := hxy.1
    have := hr hxy.1
    have := hr (Nat.zero_le y.1)
    have := hxy.2
    refine ⟨⟨by omega, by omega⟩, by omega⟩

theorem mem_ydOf {r : ℕ → ℕ} {hr : Antitone r} {n : ℕ} (hn : ∀ i, n ≤ i → r i = 0)
    {c : ℕ × ℕ} : c ∈ ydOf r hr n ↔ c.2 < r c.1 := by
  change c ∈ (range n ×ˢ range (r 0)).filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have := hr (Nat.zero_le c.1)
    refine ⟨⟨?_, by omega⟩, h⟩
    by_contra hc
    have := hn c.1 (by omega)
    omega

theorem rowLen_ydOf {r : ℕ → ℕ} {hr : Antitone r} {n : ℕ} (hn : ∀ i, n ≤ i → r i = 0) (i : ℕ) :
    (ydOf r hr n).rowLen i = r i :=
  rowLen_eq_of fun _ => mem_ydOf hn

/-! ### Colours and the box -/

/-- The boxes counted by `{a + ct(□)}`: `a + j - i` odd (white for `a` even, black for `a` odd). -/
def VCol (a : ℕ) (c : ℕ × ℕ) : Prop := (a + c.1 + c.2) % 2 = 1

instance (a : ℕ) : DecidablePred (VCol a) :=
  fun c => inferInstanceAs (Decidable ((a + c.1 + c.2) % 2 = 1))

theorem checker_vCol (a : ℕ) : Checker (VCol a) := by
  intro i j h; unfold VCol at *; constructor <;> omega

theorem vCol_iff_white {a : ℕ} (ha : Even a) (c : ℕ × ℕ) : VCol a c ↔ IsWhite c := by
  have := Nat.even_iff.mp ha
  unfold VCol IsWhite; omega

theorem vCol_iff_black {a : ℕ} (ha : Odd a) (c : ℕ × ℕ) : VCol a c ↔ IsBlack c := by
  have := Nat.odd_iff.mp ha
  unfold VCol IsBlack; omega

/-- Partitions in the `b × a` box: at most `b` rows and at most `a` columns (`Par(b,a)`). -/
def InBox (b a : ℕ) (μ : YoungDiagram) : Prop := ∀ c ∈ μ, c.1 < b ∧ c.2 < a

/-- The boxes of colour `VCol a` inside the `b × a` box. -/
def VBoxCol (a b : ℕ) (c : ℕ × ℕ) : Prop := VCol a c ∧ c.1 < b ∧ c.2 < a

instance (a b : ℕ) : DecidablePred (VBoxCol a b) := fun c => by unfold VBoxCol; infer_instance

theorem checker_vBoxCol (a b : ℕ) : Checker (VBoxCol a b) :=
  (checker_vCol a).and fun c => c.1 < b ∧ c.2 < a

/-- The box system of `V_{a,b}` (Ellis–Qi, Appendix A.3): partitions in the `b × a` box, boxes of
colour `VCol a` inside the box. -/
def vSystem (a b : ℕ) : BoxSystem {μ : YoungDiagram // InBox b a μ} (ℕ × ℕ) :=
  (ydSystem (VBoxCol a b) (checker_vBoxCol a b)).restrict (InBox b a)
    (by
      intro μ c hμ hc x hx
      obtain ⟨⟨-, hc1, hc2⟩, hac⟩ := mem_addableCells.mp hc
      change x ∈ addCell μ c at hx
      rcases (mem_addCell hac x).mp hx with rfl | h
      · exact ⟨hc1, hc2⟩
      · exact hμ x h)
    (by
      intro μ c hμ hc x hx
      obtain ⟨-, hrc⟩ := mem_removableCells.mp hc
      change x ∈ remCell μ c at hx
      exact hμ x ((mem_remCell hrc x).mp hx).2)

theorem vSystem_add_val {a b : ℕ} {μ : {μ : YoungDiagram // InBox b a μ}} {c : ℕ × ℕ}
    (hc : c ∈ (vSystem a b).A μ) : ((vSystem a b).add μ c).1 = addCell μ.1 c :=
  BoxSystem.restrict_add_val _ _ _ _ hc

theorem mem_vSystem_A {a b : ℕ} {μ : {μ : YoungDiagram // InBox b a μ}} {c : ℕ × ℕ} :
    c ∈ (vSystem a b).A μ ↔ VCol a c ∧ c.1 < b ∧ c.2 < a ∧ Addable μ.1 c := by
  change c ∈ addableCells (VBoxCol a b) μ.1 ↔ _
  rw [mem_addableCells]; unfold VBoxCol; tauto

theorem mem_vSystem_R {a b : ℕ} {μ : {μ : YoungDiagram // InBox b a μ}} {c : ℕ × ℕ} :
    c ∈ (vSystem a b).R μ ↔ VCol a c ∧ Removable μ.1 c := by
  change c ∈ removableCells (VBoxCol a b) μ.1 ↔ _
  rw [mem_removableCells]
  unfold VBoxCol
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, μ.2 c h2.1⟩, h2⟩

/-- The signs `(-1)^{|λ/i| + i - 1}` of Lemma 4.7 make every square anticommute. -/
theorem squareCond_vSystem {k : Type*} [CommRing k] (a b : ℕ) :
    (vSystem a b).SquareCond (k := k) (fun μ c => schurSign μ.1 c) := by
  intro μ c c' hc hc' hne
  have := squareCond_schurSign (k := k) (checker_vBoxCol a b) μ.1 c c' hc hc' hne
  simp only at this ⊢
  rw [vSystem_add_val hc, vSystem_add_val hc']
  exact this

/-! ### Row lengths of partitions in the box -/

section Rows

variable {a b : ℕ} {μ : YoungDiagram}

theorem rowLen_le_of_inBox (h : InBox b a μ) (i : ℕ) : μ.rowLen i ≤ a := by
  by_contra hc
  have := (h (i, a) (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))).2
  omega

theorem rowLen_eq_zero_of_inBox (h : InBox b a μ) {i : ℕ} (hi : b ≤ i) : μ.rowLen i = 0 := by
  by_contra hc
  have := (h (i, 0) (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))).1
  omega

theorem lengthLE_of_inBox (h : InBox b a μ) : LengthLE b μ := fun c hc => (h c hc).1

end Rows

/-! ### Critical partitions -/

theorem vCrit_iff (a b : ℕ) (μ : {μ : YoungDiagram // InBox b a μ}) :
    (vSystem a b).Crit μ ↔
      (∀ c, VCol a c → c.1 < b → c.2 < a → ¬ Addable μ.1 c) ∧
        (∀ c, VCol a c → ¬ Removable μ.1 c) := by
  rw [BoxSystem.crit_iff]
  simp only [Finset.eq_empty_iff_forall_notMem, mem_vSystem_A, mem_vSystem_R, not_and]

/-- **`a` even** (Ellis–Qi, Appendix A.3): the critical partitions of `V_{a,b}` are exactly the
Lima partitions in the `b × a` box. -/
theorem vCrit_iff_even {a b : ℕ} (ha : Even a) (μ : {μ : YoungDiagram // InBox b a μ}) :
    (vSystem a b).Crit μ ↔ IsLima μ.1 := by
  rw [vCrit_iff]
  have ha' := Nat.even_iff.mp ha
  constructor
  · rintro ⟨hA, hR⟩
    refine isLima_of_noWhite (lengthLE_of_inBox μ.2) (fun c hc hcb hadd => ?_)
      (fun c hc => hR c ((vCol_iff_white ha c).mpr hc))
    by_cases hca : c.2 < a
    · exact hA c ((vCol_iff_white ha c).mpr hc) hcb hca hadd
    · obtain ⟨i, j⟩ := c
      obtain ⟨hj, hup⟩ := (addable_iff_rowLen μ.1 i j).mp hadd
      have h1 := rowLen_le_of_inBox μ.2 i
      simp only at hca hc
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · unfold IsWhite at hc; simp only at hc; omega
      · have := hup hi
        have := rowLen_le_of_inBox μ.2 (i - 1)
        omega
  · intro h
    obtain ⟨hA, hR⟩ := noWhite_of_isLima h
    exact ⟨fun c hc _ _ => hA c ((vCol_iff_white ha c).mp hc),
      fun c hc => hR c ((vCol_iff_white ha c).mp hc)⟩

/-- The critical partitions for `a` odd: exactly `b` rows, `b` even, all rows of odd length, and
rows paired, `λ_{2k} = λ_{2k+1}` (`0`-based rows). -/
def IsOddLima (b : ℕ) (μ : YoungDiagram) : Prop :=
  Even b ∧ ∀ k, 2 * k < b → Odd (μ.rowLen (2 * k)) ∧ μ.rowLen (2 * k + 1) = μ.rowLen (2 * k)

/-- **`a` odd**: the critical partitions of `V_{a,b}` are the `IsOddLima b` partitions in the box
(the printed text claims there are none). -/
theorem vCrit_iff_odd {a b : ℕ} (ha : Odd a) (μ : {μ : YoungDiagram // InBox b a μ}) :
    (vSystem a b).Crit μ ↔ IsOddLima b μ.1 := by
  rw [vCrit_iff]
  have ha' := Nat.odd_iff.mp ha
  have hle : ∀ i, μ.1.rowLen i ≤ a := rowLen_le_of_inBox μ.2
  have hzero : ∀ i, b ≤ i → μ.1.rowLen i = 0 := fun i hi => rowLen_eq_zero_of_inBox μ.2 hi
  have hanti : ∀ i j, i ≤ j → μ.1.rowLen j ≤ μ.1.rowLen i := fun i j h => μ.1.rowLen_anti i j h
  constructor
  · rintro ⟨hA, hR⟩
    have key : ∀ k, 2 * k < b →
        Odd (μ.1.rowLen (2 * k)) ∧ μ.1.rowLen (2 * k + 1) = μ.1.rowLen (2 * k) := by
      intro k
      induction k with
      | zero =>
        intro hb
        have hodd : Odd (μ.1.rowLen 0) := by
          rw [Nat.odd_iff]
          by_contra hc
          have hlt : μ.1.rowLen 0 < a := by have := hle 0; omega
          refine hA (0, μ.1.rowLen 0) (by unfold VCol; simp only; omega) hb hlt ?_
          rw [addable_iff_rowLen]
          exact ⟨rfl, fun h => absurd h (lt_irrefl 0)⟩
        refine ⟨hodd, ?_⟩
        have h01 := hanti 0 1 (Nat.zero_le 1)
        by_contra hne
        have := Nat.odd_iff.mp hodd
        refine hR (0, μ.1.rowLen 0 - 1) (by unfold VCol; simp only; omega) ?_
        rw [removable_iff_rowLen]
        simp only [Nat.mul_zero, Nat.zero_add] at hne ⊢
        omega
      | succ k ih =>
        intro hb
        obtain ⟨ihodd, ihpair⟩ := ih (by omega)
        have ihodd' := Nat.odd_iff.mp ihodd
        have e1 : 2 * (k + 1) = 2 * k + 2 := by ring
        rw [e1] at hb ⊢
        have hodd : Odd (μ.1.rowLen (2 * k + 2)) := by
          rw [Nat.odd_iff]
          by_contra hc
          have hlt : μ.1.rowLen (2 * k + 2) < a := by have := hle (2 * k + 2); omega
          have h21 := hanti (2 * k + 1) (2 * k + 2) (by omega)
          refine hA (2 * k + 2, μ.1.rowLen (2 * k + 2)) (by unfold VCol; simp only; omega) hb hlt ?_
          rw [addable_iff_rowLen]
          refine ⟨rfl, fun _ => ?_⟩
          rw [show 2 * k + 2 - 1 = 2 * k + 1 by omega]
          omega
        refine ⟨hodd, ?_⟩
        have h23 := hanti (2 * k + 2) (2 * k + 3) (by omega)
        by_contra hne
        have := Nat.odd_iff.mp hodd
        refine hR (2 * k + 2, μ.1.rowLen (2 * k + 2) - 1) (by unfold VCol; simp only; omega) ?_
        rw [removable_iff_rowLen]
        rw [show 2 * k + 2 + 1 = 2 * k + 3 by ring] at hne ⊢
        omega
    refine ⟨?_, key⟩
    rw [Nat.even_iff]
    by_contra hb
    obtain ⟨hodd, hpair⟩ := key (b / 2) (by omega)
    have := hzero (2 * (b / 2) + 1) (by omega)
    have := Nat.odd_iff.mp hodd
    omega
  · rintro ⟨hb, hpairs⟩
    have hb' := Nat.even_iff.mp hb
    refine ⟨fun ⟨i, j⟩ hc hib hja hadd => ?_, fun ⟨i, j⟩ hc hrem => ?_⟩
    · obtain ⟨rfl, hup⟩ := (addable_iff_rowLen μ.1 i j).mp hadd
      unfold VCol at hc
      simp only at hc hib hja
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
      · subst hk
        have := Nat.odd_iff.mp (hpairs k hib).1
        omega
      · subst hk
        have := (hpairs k (by omega)).2
        have := hup (by omega)
        rw [show 2 * k + 1 - 1 = 2 * k by omega] at this
        omega
    · have hrem' := (removable_iff_rowLen μ.1 i j).mp hrem
      have hib : i < b := (μ.2 _ hrem.1).1
      unfold VCol at hc
      simp only at hc hib
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
      · subst hk
        have := (hpairs k hib).2
        omega
      · subst hk
        have h1 := (hpairs k (by omega)).2
        have h2 := Nat.odd_iff.mp (hpairs k (by omega)).1
        omega

/-- `b` odd: no critical partitions when `a` is odd. -/
theorem vCritSet_eq_empty_of_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    (vSystem a b).critSet = ∅ := by
  ext μ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have := ((vCrit_iff_odd ha μ).mp h).1
  exact (Nat.not_even_iff_odd.mpr hb) this

/-- The full rectangle `(a^b)`. -/
def rectangle (b a : ℕ) : YoungDiagram :=
  ydOf (fun i => if i < b then a else 0)
    (fun i j h => by dsimp only; split_ifs <;> omega) b

theorem rectangle_zero (b a : ℕ) : ∀ i, b ≤ i → (fun i => if i < b then a else 0) i = 0 :=
  fun i hi => by dsimp only; split_ifs <;> omega

theorem rowLen_rectangle (b a i : ℕ) : (rectangle b a).rowLen i = if i < b then a else 0 :=
  rowLen_ydOf (rectangle_zero b a) i

theorem rectangle_inBox (b a : ℕ) : InBox b a (rectangle b a) := by
  intro c hc
  rw [rectangle, mem_ydOf (rectangle_zero b a)] at hc
  split_ifs at hc with h <;> omega

/-- For `a` odd and `b` even, the rectangle `(a^b)` is critical. -/
theorem rectangle_isOddLima {a b : ℕ} (ha : Odd a) (hb : Even b) : IsOddLima b (rectangle b a) := by
  refine ⟨hb, fun k hk => ?_⟩
  have hb' := Nat.even_iff.mp hb
  rw [rowLen_rectangle, rowLen_rectangle]
  simp only [hk, show 2 * k + 1 < b by omega, ↓reduceIte]
  exact ⟨ha, trivial⟩

/-! ### Hypercube decomposition of a complex with a box-type basis -/

/-- If `D` acts on the basis `s` by adding boxes, then `M` is isomorphic, as a complex, to the direct
sum of the hypercube complexes of the initial shapes (`EQApp.decompEquiv_delta`). -/
theorem actsByBoxes_decomp {k : Type*} [CommRing k] {P B : Type*} [DecidableEq B]
    {S : BoxSystem P B} {M : Type*} [AddCommGroup M] [Module k M] {s : Module.Basis P k M}
    {c : P → B → kˣ} {D : M →ₗ[k] M} (hD : ActsByBoxes S s c D) (x : M) :
    (s.repr.trans (decompEquiv S)) (D x) =
      DFinsupp.mapRange.linearMap (fun q => hyperDelta S c q) ((s.repr.trans (decompEquiv S)) x) := by
  have h := actsByBoxes_intertwine hD (s.repr x)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h, LinearEquiv.apply_symm_apply,
    decompEquiv_delta]

/-! ### Cohomology of `V_{a,b}` -/

section Cohomology

variable {k : Type*} [CommRing k] {a b : ℕ} {M : Type*} [AddCommGroup M] [Module k M]
  (s : Module.Basis {μ : YoungDiagram // InBox b a μ} k M) (D : M →ₗ[k] M)

/-- The differential of Ellis–Qi, Appendix A.3 (Lemma 4.7 in `0`-based rows) on a basis indexed by
`Par(b,a)`: `D(s_λ) = Σ_{μ = λ + □ ∈ Par(b,a)} (-1)^{|λ/i| + i} {a + ct(□)} s_μ`. -/
def VFormula : Prop := ActsByBoxes (vSystem a b) s (fun μ c => schurSign μ.1 c) D

variable {s D}

/-- The critical partitions for `a` even are the Lima partitions in the box. -/
def critEquivEven (ha : Even a) :
    (vSystem a b).critSet ≃ {μ : YoungDiagram // IsLima μ ∧ InBox b a μ} where
  toFun p := ⟨p.1.1, (vCrit_iff_even ha p.1).mp p.2, p.1.2⟩
  invFun μ := ⟨⟨μ.1, μ.2.2⟩, (vCrit_iff_even ha ⟨μ.1, μ.2.2⟩).mpr μ.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The critical partitions for `a` odd. -/
def critEquivOdd (ha : Odd a) :
    (vSystem a b).critSet ≃ {μ : YoungDiagram // IsOddLima b μ ∧ InBox b a μ} where
  toFun p := ⟨p.1.1, (vCrit_iff_odd ha p.1).mp p.2, p.1.2⟩
  invFun μ := ⟨⟨μ.1, μ.2.2⟩, (vCrit_iff_odd ha ⟨μ.1, μ.2.2⟩).mpr μ.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Ellis–Qi, Appendix A.3, `a` even**: `H(V_{a,b})` is free with basis the classes of the Lima
Schur functions `s_λ`, `λ ∈ Par(b,a)` a Lima partition. -/
noncomputable def vHomologyBasisEven (hD : VFormula s D) (ha : Even a) :
    Module.Basis {μ : YoungDiagram // IsLima μ ∧ InBox b a μ} k (Homology D) :=
  (schurHomologyBasis hD (squareCond_vSystem a b)).reindex (critEquivEven ha)

theorem vHomologyBasisEven_apply (hD : VFormula s D) (ha : Even a)
    (μ : {μ : YoungDiagram // IsLima μ ∧ InBox b a μ}) :
    vHomologyBasisEven hD ha μ = Submodule.Quotient.mk ⟨s ⟨μ.1, μ.2.2⟩, LinearMap.mem_ker.mpr
      (schur_crit_cocycle hD ((vCrit_iff_even ha ⟨μ.1, μ.2.2⟩).mpr μ.2.1))⟩ := by
  rw [vHomologyBasisEven, Module.Basis.reindex_apply, schurHomologyBasis_apply]
  rfl

/-- **`a` odd (corrected)**: `H(V_{a,b})` is free with basis the classes of `s_λ`, `λ ∈ Par(b,a)`
with `IsOddLima b λ`. -/
noncomputable def vHomologyBasisOdd (hD : VFormula s D) (ha : Odd a) :
    Module.Basis {μ : YoungDiagram // IsOddLima b μ ∧ InBox b a μ} k (Homology D) :=
  (schurHomologyBasis hD (squareCond_vSystem a b)).reindex (critEquivOdd ha)

theorem vHomologyBasisOdd_apply (hD : VFormula s D) (ha : Odd a)
    (μ : {μ : YoungDiagram // IsOddLima b μ ∧ InBox b a μ}) :
    vHomologyBasisOdd hD ha μ = Submodule.Quotient.mk ⟨s ⟨μ.1, μ.2.2⟩, LinearMap.mem_ker.mpr
      (schur_crit_cocycle hD ((vCrit_iff_odd ha ⟨μ.1, μ.2.2⟩).mpr μ.2.1))⟩ := by
  rw [vHomologyBasisOdd, Module.Basis.reindex_apply, schurHomologyBasis_apply]
  rfl

/-- **`a` and `b` odd**: `H(V_{a,b}) = 0` (the printed claim holds in this case). -/
theorem vHomology_odd_odd (hD : VFormula s D) (ha : Odd a) (hb : Odd b) :
    Subsingleton (Homology D) := by
  have : IsEmpty (vSystem a b).critSet := by
    rw [vCritSet_eq_empty_of_odd ha hb]; exact Set.isEmpty_coe_sort.mpr rfl
  exact (schurHomologyBasis hD (squareCond_vSystem a b)).repr.toEquiv.subsingleton

/-- The rectangle `(a^b)` as an index of `vHomologyBasisOdd` (`a` odd, `b` even). -/
def rectangleIdx (ha : Odd a) (hb : Even b) :
    {μ : YoungDiagram // IsOddLima b μ ∧ InBox b a μ} :=
  ⟨rectangle b a, rectangle_isOddLima ha hb, rectangle_inBox b a⟩

/-- **Refutation of the printed claim** "`H(V_{a,b}) = 0` for `a` odd": for `a` odd and `b` even
the class of the rectangle `s_{(a^b)}` is a nonzero element of `H(V_{a,b})`. -/
theorem vHomology_rectangle_ne_zero [Nontrivial k] (hD : VFormula s D) (ha : Odd a)
    (hb : Even b) : vHomologyBasisOdd hD ha (rectangleIdx ha hb) ≠ 0 :=
  (vHomologyBasisOdd hD ha).ne_zero _

theorem vHomology_odd_even_nontrivial [Nontrivial k] (hD : VFormula s D) (ha : Odd a)
    (hb : Even b) : Nontrivial (Homology D) :=
  ⟨⟨_, 0, vHomology_rectangle_ne_zero hD ha hb⟩⟩

end Cohomology

end OddMath.Frontier.EQApp
