import OddMath.Frontier.EKPairingMatrices
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Sort

/-!
# EK platforms and prescribed-margin matrices

Source: EK arXiv:1107.5610v2, pp.5–7, minimal platform diagrams and (2.1).
Rows are top platforms and columns bottom platforms, with the conventions of
`EKPairingMatrices`. Empty platforms are allowed. No quotient descent is claimed.
-/
namespace OddMath.Frontier.EKPlatformBijection
open scoped BigOperators
open EKPairingMatrices

/-- Individual strands, ordered first by top platform, then bottom platform,
then their position within that pair of platforms. -/
abbrev Tokens {r c : ℕ} (M : Raw r c) := Σₗ i : Fin r, Σₗ j : Fin c, Fin (M i j)

/-- Swap the two platform labels, retaining the individual strand. -/
def swapTokens {r c : ℕ} (M : Raw r c) : Tokens M ≃ Tokens (fun j i => M i j) where
  toFun x := ⟨x.2.1, x.1, x.2.2⟩
  invFun x := ⟨x.2.1, x.1, x.2.2⟩
  left_inv := by rintro ⟨i,j,k⟩; rfl
  right_inv := by rintro ⟨i,j,k⟩; rfl

theorem card_tokens {r c : ℕ} (M : Raw r c) :
    Fintype.card (Tokens M) = ∑ i, ∑ j, M i j := by
  simp [Tokens, Fintype.card_sigma]

noncomputable def tokenOrder {n r c : ℕ} (M : Raw r c)
    (h : (∑ i, ∑ j, M i j) = n) : Fin n ≃o Tokens M :=
  Fintype.orderIsoFinOfCardEq _ ((card_tokens M).trans h)

theorem token_fst_monotone {r c : ℕ} (M : Raw r c) :
    Monotone (fun x : Tokens M => x.1) := by
  intro a b h
  rcases (Sigma.Lex.le_def.mp h) with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- Transposing tokens preserves their order whenever they have a common
starting or ending platform: exactly the source no-within condition. -/
theorem swapTokens_lt {r c : ℕ} (M : Raw r c) (a b : Tokens M)
    (h : a < b) (hs : a.1 = b.1 ∨ a.2.1 = b.2.1) :
    swapTokens M a < swapTokens M b := by
  rcases a with ⟨i,j,k⟩
  rcases b with ⟨i',j',k'⟩
  rcases hs with hsame | hsame
  · dsimp at hsame; subst i'
    have h' : (toLex ⟨j,k⟩ : Σₗ j : Fin c, Fin (M i j)) < toLex ⟨j',k'⟩ := by
      simpa only [Sigma.Lex.lt_def, lt_self_iff_false, false_or, exists_const] using h
    rcases Sigma.Lex.lt_def.mp h' with hj | ⟨hj,hk⟩
    · exact Sigma.Lex.left _ _ hj
    · change j = j' at hj; subst j'
      exact Sigma.Lex.right _ _ (Sigma.Lex.right _ _ hk)
  · dsimp at hsame; subst j'
    rcases Sigma.Lex.lt_def.mp h with hi | ⟨hi,hk⟩
    · exact Sigma.Lex.right _ _ (Sigma.Lex.left _ _ hi)
    · dsimp at hi; subst i'
      exact Sigma.Lex.right _ _ (Sigma.Lex.right _ _ (by
        simpa only [Sigma.Lex.lt_def, lt_self_iff_false, false_or, exists_const] using hk))

/-- Read the same strands in bottom order and in top order. -/
noncomputable def canonical {n r c : ℕ} (M : Raw r c)
    (h : (∑ i, ∑ j, M i j) = n) : PlatformDiagram n r c := by
  let t := tokenOrder M h
  let b := tokenOrder (fun j i => M i j) ((Finset.sum_comm).trans h)
  let s := swapTokens (fun j i => M i j)
  let p := b.toEquiv.trans (s.trans t.symm.toEquiv)
  exact {
    topPlatform := fun a => (t a).1
    bottomPlatform := fun a => (b a).1
    top_monotone := (token_fst_monotone M).comp t.monotone
    bottom_monotone := (token_fst_monotone _).comp b.monotone
    perm := p
    noWithin := by
      intro a z haz hs
      apply t.symm.strictMono
      apply swapTokens_lt _ _ _ (b.strictMono haz)
      change (b a).1 = (b z).1 ∨
        (t (t.symm (s (b a)))).1 = (t (t.symm (s (b z)))).1 at hs
      simpa [s, swapTokens] using hs }

theorem canonical_matrix {n r c : ℕ} (M : Raw r c)
    (h : (∑ i, ∑ j, M i j) = n) : (canonical M h).matrix = M := by
  funext i j
  let t := tokenOrder M h
  let b := tokenOrder (fun j i => M i j) ((Finset.sum_comm).trans h)
  change (∑ a, if (t (t.symm (swapTokens (fun j i => M i j) (b a)))).1 = i ∧
    (b a).1 = j then 1 else 0) = M i j
  simp only [OrderIso.apply_symm_apply]
  change (∑ a, if (b a).2.1 = i ∧ (b a).1 = j then 1 else 0) = M i j
  trans ∑ x : Tokens (fun j i => M i j), if x.2.1 = i ∧ x.1 = j then 1 else 0
  · exact b.toEquiv.sum_comp (fun x => if x.2.1 = i ∧ x.1 = j then (1 : ℕ) else 0)
  change (∑ x : (j : Fin c) × (i : Fin r) × Fin (M i j),
    if x.2.1 = i ∧ x.1 = j then 1 else 0) = M i j
  simp only [Fintype.sum_sigma]
  change (∑ j' : Fin c, ∑ i' : Fin r, ∑ _k : Fin (M i' j'),
    if i' = i ∧ j' = j then (1 : ℕ) else 0) = M i j
  simp [Finset.sum_const, mul_ite, ite_and]

/-- The total number of endpoints determined by the row margins. -/
theorem mat_total {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ} (M : Mat β α) :
    (∑ i, ∑ j, M i j) = ∑ i, β i := by
  change (∑ i, rowSum M i) = _
  simp only [M.property.1]

/-- Histogram of a tuple, expressed in the same counting convention as matrices. -/
theorem count_ofFn {A : Type*} [DecidableEq A] {n : ℕ} (f : Fin n → A) (x : A) :
    (List.ofFn f).count x = ∑ a, if f a = x then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp only [beq_iff_eq, eq_comm]
    split_ifs <;> simp_all [Nat.add_comm]

/-- A weakly increasing tuple is determined by its multiplicities. -/
theorem monotone_eq_counts {A : Type*} [LinearOrder A] {n : ℕ} {f g : Fin n → A}
    (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (∑ a, if f a = x then (1 : ℕ) else 0) =
      ∑ a, if g a = x then 1 else 0) : f = g := by
  apply List.ofFn_injective
  apply List.eq_of_perm_of_sorted _ hf.ofFn_sorted hg.ofFn_sorted
  apply List.perm_iff_count.mpr
  intro x
  simpa only [count_ofFn] using h x

/-- Endpoints in inverse order are increasing within each top platform. -/
theorem inverse_within {n r c : ℕ} (D : PlatformDiagram n r c) {a b : Fin n}
    (hab : a < b) (ht : D.topPlatform a = D.topPlatform b) :
    D.perm.symm a < D.perm.symm b := by
  by_contra hn
  have hne : D.perm.symm b ≠ D.perm.symm a := fun h => (ne_of_lt hab)
    (D.perm.symm.injective h).symm
  have hba := lt_of_le_of_ne (le_of_not_gt hn) hne
  have h := D.noWithin _ _ hba (Or.inr (by simpa using ht.symm))
  simp only [Equiv.apply_symm_apply] at h
  exact (not_lt_of_gt hab) h

/-- Bottom endpoints are sorted by bottom platform, then by top platform. -/
theorem bottom_keys_monotone {n r c : ℕ} (D : PlatformDiagram n r c) :
    Monotone (fun a => (toLex (D.bottomPlatform a, D.topPlatform (D.perm a)) :
      Fin c ×ₗ Fin r)) := by
  intro a b hab
  apply Prod.Lex.toLex_le_toLex'.mpr
  refine ⟨D.bottom_monotone hab, ?_⟩
  intro hB
  rcases lt_or_eq_of_le hab with hab | rfl
  · exact D.top_monotone (le_of_lt (D.noWithin a b hab (Or.inl hB)))
  · exact le_rfl

/-- Inverse endpoints are sorted by top platform and by their original position. -/
theorem inverse_keys_monotone {n r c : ℕ} (D : PlatformDiagram n r c) :
    Monotone (fun a => (toLex (D.topPlatform a, D.perm.symm a) : Fin r ×ₗ Fin n)) := by
  intro a b hab
  apply Prod.Lex.toLex_le_toLex'.mpr
  refine ⟨D.top_monotone hab, ?_⟩
  intro hT
  rcases lt_or_eq_of_le hab with hab | rfl
  · exact le_of_lt (inverse_within D hab hT)
  · exact le_rfl

/-- No two source platform diagrams have the same multiplicity matrix. -/
theorem matrix_injective {n r c : ℕ} :
    Function.Injective (@PlatformDiagram.matrix n r c) := by
  intro D E hm
  have hT : D.topPlatform = E.topPlatform := by
    refine monotone_eq_counts (A := Fin r) D.top_monotone E.top_monotone ?_
    intro i
    convert (congrFun D.toMat.property.1 i).symm.trans
      ((congrArg (fun M => rowSum M i) hm).trans (congrFun E.toMat.property.1 i)) using 1 <;>
      apply Finset.sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl
  have hB : D.bottomPlatform = E.bottomPlatform := by
    refine monotone_eq_counts (A := Fin c) D.bottom_monotone E.bottom_monotone ?_
    intro j
    convert (congrFun D.toMat.property.2 j).symm.trans
      ((congrArg (fun M => colSum M j) hm).trans (congrFun E.toMat.property.2 j)) using 1 <;>
      apply Finset.sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl
  have hK : (fun a => (toLex (D.bottomPlatform a, D.topPlatform (D.perm a)) :
      Fin c ×ₗ Fin r)) = (fun a => toLex (E.bottomPlatform a, E.topPlatform (E.perm a))) := by
    refine monotone_eq_counts (A := Fin c ×ₗ Fin r) (bottom_keys_monotone D)
      (bottom_keys_monotone E) ?_
    intro x
    obtain ⟨j,i⟩ := x
    have hm' := congrFun (congrFun hm i) j
    change (∑ a, if D.topPlatform (D.perm a) = i ∧ D.bottomPlatform a = j then 1 else 0) =
      (∑ a, if E.topPlatform (E.perm a) = i ∧ E.bottomPlatform a = j then 1 else 0) at hm'
    have key_eq (b : Fin c) (t : Fin r) :
        (toLex (b,t) : Fin c ×ₗ Fin r) = (j,i) ↔ b = j ∧ t = i := by
      change (b,t) = (j,i) ↔ _
      simp only [Prod.mk.injEq]
    convert hm' using 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;>
      simp only [key_eq, and_comm]
  have hTP : ∀ a, D.topPlatform (D.perm a) = E.topPlatform (E.perm a) := by
    intro a; exact congrArg (fun x : Fin c ×ₗ Fin r => x.2) (congrFun hK a)
  let f := fun a => (toLex (D.topPlatform (D.perm a), a) : Fin r ×ₗ Fin n)
  have hd : Monotone (f ∘ D.perm.symm) := by
    simpa [f, Function.comp_def] using inverse_keys_monotone D
  have he : Monotone (f ∘ E.perm.symm) := by
    simpa only [f, Function.comp_def, hTP, Equiv.apply_symm_apply] using
      inverse_keys_monotone E
  have hu := Tuple.unique_monotone hd he
  have hp : D.perm.symm = E.perm.symm := by
    apply Equiv.ext; intro a
    exact congrArg (fun x : Fin r ×ₗ Fin n => x.2) (congrFun hu a)
  have hP : D.perm = E.perm := by simpa using congrArg Equiv.symm hp
  cases D; cases E; cases hT; cases hB; cases hP; rfl

/-- Prescribed platform sizes, expressed as actual endpoint counts, not as
an assumed matrix reconstruction certificate. -/
def HasMargins {n r c : ℕ} (D : PlatformDiagram n r c)
    (β : Fin r → ℕ) (α : Fin c → ℕ) : Prop :=
  (fun i => ∑ a, if D.topPlatform a = i then (1 : ℕ) else 0) = β ∧
  (fun j => ∑ a, if D.bottomPlatform a = j then (1 : ℕ) else 0) = α

abbrev Diagrams {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :=
  {D : PlatformDiagram (∑ i, β i) r c // HasMargins D β α}

theorem hasMargins_iff {n r c : ℕ} (D : PlatformDiagram n r c)
    (β : Fin r → ℕ) (α : Fin c → ℕ) :
    HasMargins D β α ↔ rowSum D.matrix = β ∧ colSum D.matrix = α := by
  have hr : rowSum D.matrix = (fun i => ∑ a, if D.topPlatform a = i then 1 else 0) :=
    D.toMat.property.1
  have hc : colSum D.matrix = (fun j => ∑ a, if D.bottomPlatform a = j then 1 else 0) :=
    D.toMat.property.2
  simp only [HasMargins, hr, hc]

def diagramMatrix {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ}
    (D : Diagrams β α) : Mat β α :=
  ⟨D.val.matrix, (hasMargins_iff D.val β α).mp D.property⟩

noncomputable def matrixDiagram {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ}
    (M : Mat β α) : Diagrams β α :=
  ⟨canonical M (mat_total M), by
    rw [hasMargins_iff, canonical_matrix]
    exact M.property⟩

/-- Genuine platform-diagram/matrix equivalence; neither inverse is a hypothesis. -/
noncomputable def diagramEquiv {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    Diagrams β α ≃ Mat β α where
  toFun := diagramMatrix
  invFun := matrixDiagram
  left_inv D := by
    apply Subtype.ext; apply matrix_injective
    exact canonical_matrix _ _
  right_inv M := by
    apply Subtype.ext
    exact canonical_matrix _ _

noncomputable instance {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    Fintype (Diagrams β α) := Fintype.ofEquiv (Mat β α) (diagramEquiv β α).symm

/-- Source diagram sum, with the source permutation inversion length. -/
noncomputable def diagramPairing {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) : ℤ :=
  ∑ D : Diagrams β α, (-1 : ℤ) ^ D.val.length

/-- EK (2.1), q=-1: transport from actual source platform diagrams to all
nonnegative matrices of the prescribed margins. -/
theorem diagramPairing_eq_pairing {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    diagramPairing β α = pairing β α := by
  unfold diagramPairing pairing
  apply Fintype.sum_equiv (diagramEquiv β α)
  intro D
  exact congrArg (fun k => (-1 : ℤ)^k) D.val.crossing_eq_length.symm

/-- Positions in the contiguous blocks, ordered by platform then position. -/
abbrev Slots {r : ℕ} (β : Fin r → ℕ) := Σₗ i : Fin r, Fin (β i)

noncomputable def slotOrder {n r : ℕ} (β : Fin r → ℕ) (h : (∑ i, β i) = n) :
    Fin n ≃o Slots β := Fintype.orderIsoFinOfCardEq _ (by
  change Fintype.card ((i : Fin r) × Fin (β i)) = n
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h)

/-- Canonical contiguous endpoint map. Zero blocks contain no endpoints. -/
noncomputable def endpoint {n r : ℕ} (β : Fin r → ℕ) (h : (∑ i, β i) = n) :
    Fin n → Fin r := fun a => (slotOrder β h a).1

theorem endpoint_monotone {n r : ℕ} (β : Fin r → ℕ) (h : (∑ i, β i) = n) :
    Monotone (endpoint β h) := by
  intro a b hab
  rcases Sigma.Lex.le_def.mp ((slotOrder β h).monotone hab) with hh | ⟨hh,_⟩
  · exact le_of_lt hh
  · exact le_of_eq hh

theorem endpoint_count {n r : ℕ} (β : Fin r → ℕ) (h : (∑ i, β i) = n) (i : Fin r) :
    (∑ a, if endpoint β h a = i then (1 : ℕ) else 0) = β i := by
  trans ∑ x : Slots β, if x.1 = i then (1 : ℕ) else 0
  · exact (slotOrder β h).toEquiv.sum_comp (fun x => if x.1 = i then (1 : ℕ) else 0)
  change (∑ x : (i : Fin r) × Fin (β i), if x.1 = i then (1 : ℕ) else 0) = β i
  simp only [Fintype.sum_sigma]
  change (∑ j : Fin r, ∑ _k : Fin (β j), if j = i then (1 : ℕ) else 0) = β i
  simp [mul_ite]

/-- Explicit contiguity: a platform occupies an interval of ordered endpoints. -/
theorem endpoint_contiguous {n r : ℕ} (β : Fin r → ℕ) (h : (∑ i, β i) = n)
    {a b x : Fin n} (hax : a ≤ x) (hxb : x ≤ b)
    (he : endpoint β h a = endpoint β h b) : endpoint β h x = endpoint β h a := by
  exact le_antisymm (he ▸ endpoint_monotone β h hxb) (endpoint_monotone β h hax)

/-- Any monotone endpoint map with the prescribed counts is the canonical one. -/
theorem endpoint_unique {n r : ℕ} (β : Fin r → ℕ) (h : (∑ i, β i) = n)
    {T : Fin n → Fin r} (hT : Monotone T)
    (hc : ∀ i, (∑ a, if T a = i then (1 : ℕ) else 0) = β i) : T = endpoint β h := by
  refine monotone_eq_counts (A := Fin r) hT (endpoint_monotone β h) ?_
  intro i
  convert (hc i).trans (endpoint_count β h i).symm using 1 <;>
    apply Finset.sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl

/-- The source condition on an actual permutation with fixed endpoint maps. -/
def NoWithin {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ a b, a < b → (B a = B b ∨ T (σ a) = T (σ b)) → σ a < σ b

abbrev MinimalPerms {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j) :=
  {σ : Equiv.Perm (Fin (∑ i, β i)) // NoWithin (endpoint β rfl) (endpoint α h.symm) σ}

noncomputable def permDiagram {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j) (σ : MinimalPerms β α h) : Diagrams β α :=
  ⟨⟨endpoint β rfl, endpoint α h.symm, endpoint_monotone β rfl,
    endpoint_monotone α h.symm, σ.val, σ.property⟩,
    ⟨funext (endpoint_count β rfl), funext (endpoint_count α h.symm)⟩⟩

theorem diagram_endpoints {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ}
    (h : (∑ i, β i) = ∑ j, α j) (D : Diagrams β α) :
    D.val.topPlatform = endpoint β rfl ∧ D.val.bottomPlatform = endpoint α h.symm := by
  exact ⟨endpoint_unique β rfl D.val.top_monotone (congrFun D.property.1),
    endpoint_unique α h.symm D.val.bottom_monotone (congrFun D.property.2)⟩

noncomputable def diagramPerm {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ}
    (h : (∑ i, β i) = ∑ j, α j) (D : Diagrams β α) : MinimalPerms β α h :=
  ⟨D.val.perm, by
    have hd := diagram_endpoints h D
    simpa only [NoWithin, ← hd.1, ← hd.2] using D.val.noWithin⟩

/-- Equivalence with actual permutations of Fin N, not renamed matrices. -/
noncomputable def minimalPermEquiv {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j) : MinimalPerms β α h ≃ Mat β α :=
  (show MinimalPerms β α h ≃ Diagrams β α from
    { toFun := permDiagram β α h
      invFun := diagramPerm h
      left_inv σ := by apply Subtype.ext; rfl
      right_inv D := by
        apply Subtype.ext
        have hd := diagram_endpoints h D
        rcases D with ⟨⟨T,B,hT,hB,σ,hn⟩,hm⟩
        dsimp at hd ⊢
        cases hd.1; cases hd.2; rfl }).trans (diagramEquiv β α)

/-- Genuine Young-subgroup action: a permutation stays inside each platform. -/
def Preserves {n r : ℕ} (T : Fin n → Fin r) (u : Equiv.Perm (Fin n)) : Prop :=
  ∀ a, T (u a) = T a

/-- Left top and right bottom action, with bottom-to-top permutation convention. -/
def SameDoubleCoset {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    (σ τ : Equiv.Perm (Fin n)) : Prop :=
  ∃ u v : Equiv.Perm (Fin n), Preserves T u ∧ Preserves B v ∧ τ = (v.trans σ).trans u

def permMatrix {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    (σ : Equiv.Perm (Fin n)) : Raw r c := strandMatrix (fun a => T (σ a)) B

theorem matrix_of_sameDoubleCoset {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    {σ τ : Equiv.Perm (Fin n)} (h : SameDoubleCoset T B σ τ) :
    permMatrix T B σ = permMatrix T B τ := by
  obtain ⟨u,v,hu,hv,rfl⟩ := h
  change ∀ a, T (u a) = T a at hu
  change ∀ a, B (v a) = B a at hv
  funext i j
  change (∑ a, if T (σ a) = i ∧ B a = j then (1 : ℕ) else 0) =
    ∑ a, if T (u (σ (v a))) = i ∧ B a = j then 1 else 0
  simp only [hu]
  conv_rhs => arg 2; ext a; rw [← hv a]
  exact (Equiv.sum_comp v (fun a => if T (σ a) = i ∧ B a = j then (1 : ℕ) else 0)).symm

/-- Equal cell counts produce a domain bijection matching both platform labels. -/
theorem sameDoubleCoset_of_matrix {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    {σ τ : Equiv.Perm (Fin n)} (h : permMatrix T B σ = permMatrix T B τ) :
    SameDoubleCoset T B σ τ := by
  classical
  let f := fun a => (T (τ a), B a)
  let g := fun a => (T (σ a), B a)
  have hc (x : Fin r × Fin c) : Fintype.card {a // f a = x} = Fintype.card {a // g a = x} := by
    have hh := congrFun (congrFun h x.1) x.2
    simpa [f, g, Fintype.card_subtype, permMatrix, strandMatrix, Prod.ext_iff] using hh.symm
  let e := fun x => Fintype.equivOfCardEq (hc x)
  let v := Equiv.ofFiberEquiv e
  have hv (a : Fin n) : g (v a) = f a := Equiv.ofFiberEquiv_map e a
  let u := σ.symm.trans (v.symm.trans τ)
  refine ⟨u,v,?_,?_,?_⟩
  · intro a
    have hh := congrArg Prod.fst (hv (v.symm (σ.symm a)))
    simpa [u, f, g] using hh.symm
  · intro a; exact congrArg Prod.snd (hv a)
  · apply Equiv.ext; intro a; simp [u]

theorem sameDoubleCoset_iff_matrix {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    (σ τ : Equiv.Perm (Fin n)) :
    SameDoubleCoset T B σ τ ↔ permMatrix T B σ = permMatrix T B τ :=
  ⟨matrix_of_sameDoubleCoset T B, sameDoubleCoset_of_matrix T B⟩

/-- Source Coxeter length as the number of inversions of an actual permutation. -/
def inversions {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ a, ∑ b, if a < b ∧ σ b < σ a then 1 else 0

def forced {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    (σ : Equiv.Perm (Fin n)) (a b : Fin n) : ℕ :=
  if B a < B b ∧ T (σ b) < T (σ a) then 1 else 0

theorem forced_le {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    forced T B σ a b ≤ if a < b ∧ σ b < σ a then 1 else 0 := by
  have hh : B a < B b ∧ T (σ b) < T (σ a) → a < b ∧ σ b < σ a := by
    rintro ⟨hb,ht⟩
    constructor
    · by_contra hn; exact (not_le_of_gt hb) (hB (le_of_not_gt hn))
    · by_contra hn; exact (not_le_of_gt ht) (hT (le_of_not_gt hn))
  unfold forced
  split_ifs with h h' h' <;> simp_all

theorem crossing_eq_forced {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    (σ : Equiv.Perm (Fin n)) : crossing (permMatrix T B σ) = ∑ a, ∑ b, forced T B σ a b := by
  rw [permMatrix, crossing_strandMatrix, Finset.sum_comm]
  simp only [forced, and_comm]

/-- Crossings between different platforms are unavoidable in any representative. -/
theorem crossing_le_inversions {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (σ : Equiv.Perm (Fin n)) :
    crossing (permMatrix T B σ) ≤ inversions σ := by
  rw [crossing_eq_forced]
  exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => forced_le hT hB σ a b))

/-- Equality in the universal lower bound holds exactly for the source
no-within-platform criterion; no minimality certificate is assumed. -/
theorem crossing_eq_inversions_iff {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (σ : Equiv.Perm (Fin n)) :
    crossing (permMatrix T B σ) = inversions σ ↔ NoWithin T B σ := by
  constructor
  · intro he a b hab hw
    rw [crossing_eq_forced, inversions] at he
    have hrow := (Finset.sum_eq_sum_iff_of_le
      (fun a (_ : a ∈ Finset.univ) => Finset.sum_le_sum
        (fun b _ => forced_le hT hB σ a b))).mp he a (Finset.mem_univ a)
    have hterm := (Finset.sum_eq_sum_iff_of_le
      (fun b (_ : b ∈ Finset.univ) => forced_le hT hB σ a b)).mp hrow b (Finset.mem_univ b)
    by_contra hn
    have hne : σ b ≠ σ a := fun heq => (ne_of_lt hab) (σ.injective heq).symm
    have hba := lt_of_le_of_ne (le_of_not_gt hn) hne
    have hzero : forced T B σ a b = 0 := by
      rcases hw with hw | hw <;> simp [forced, hw]
    simp only [hzero, hab, hba, and_self, if_true] at hterm
    omega
  · intro hn
    exact (show PlatformDiagram n r c from ⟨T,B,hT,hB,σ,hn⟩).crossing_eq_length

theorem permMatrix_total {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    (σ : Equiv.Perm (Fin n)) : (∑ i, ∑ j, permMatrix T B σ i j) = n := by
  change (∑ i, rowSum (permMatrix T B σ) i) = n
  simp only [permMatrix, strandMatrix_rowSum]
  rw [Finset.sum_comm]
  simp

/-- Every actual orbit has a source noWithin representative on the same fixed
platforms. Construction uses tokens and ordered endpoints, not orbit choice. -/
theorem exists_noWithin_representative {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (σ : Equiv.Perm (Fin n)) :
    ∃ τ, SameDoubleCoset T B σ τ ∧ NoWithin T B τ := by
  let D := canonical (permMatrix T B σ) (permMatrix_total T B σ)
  have hm : D.matrix = permMatrix T B σ := canonical_matrix _ _
  have ht : D.topPlatform = T := by
    refine monotone_eq_counts (A := Fin r) D.top_monotone hT ?_
    intro i
    have hrow : rowSum (permMatrix T B σ) i = ∑ a, if T a = i then (1 : ℕ) else 0 := by
      rw [permMatrix, strandMatrix_rowSum]
      exact Equiv.sum_comp σ (fun a => if T a = i then (1 : ℕ) else 0)
    convert (congrFun D.toMat.property.1 i).symm.trans
      ((congrArg (fun M => rowSum M i) hm).trans hrow) using 1 <;>
      apply Finset.sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl
  have hb : D.bottomPlatform = B := by
    refine monotone_eq_counts (A := Fin c) D.bottom_monotone hB ?_
    intro j
    have hcol : colSum (permMatrix T B σ) j = ∑ a, if B a = j then (1 : ℕ) else 0 :=
      strandMatrix_colSum _ _ j
    convert (congrFun D.toMat.property.2 j).symm.trans
      ((congrArg (fun M => colSum M j) hm).trans hcol) using 1 <;>
      apply Finset.sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl
  refine ⟨D.perm, ?_, ?_⟩
  · apply sameDoubleCoset_of_matrix
    simpa only [PlatformDiagram.matrix, permMatrix, ht, hb] using hm.symm
  · simpa only [NoWithin, ht, hb] using D.noWithin

/-- Minimal in the genuine left/right platform-preserving orbit. -/
def IsMinimal {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ τ, SameDoubleCoset T B σ τ → inversions σ ≤ inversions τ

theorem noWithin_iff_minimal {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (σ : Equiv.Perm (Fin n)) :
    NoWithin T B σ ↔ IsMinimal T B σ := by
  constructor
  · intro hn τ horbit
    have he := (crossing_eq_inversions_iff hT hB σ).mpr hn
    rw [← he, matrix_of_sameDoubleCoset T B horbit]
    exact crossing_le_inversions hT hB τ
  · intro hmin
    obtain ⟨τ,horbit,hn⟩ := exists_noWithin_representative hT hB σ
    have hupper := hmin τ horbit
    rw [← (crossing_eq_inversions_iff hT hB τ).mpr hn,
      ← matrix_of_sameDoubleCoset T B horbit] at hupper
    exact (crossing_eq_inversions_iff hT hB σ).mp
      (le_antisymm (crossing_le_inversions hT hB σ) hupper)

/-- The unique minimal representative theorem for actual double cosets. -/
theorem unique_minimal_representative {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (σ : Equiv.Perm (Fin n)) :
    ∃! τ, SameDoubleCoset T B σ τ ∧ IsMinimal T B τ := by
  obtain ⟨τ,ho,hn⟩ := exists_noWithin_representative hT hB σ
  refine ⟨τ, ⟨ho, (noWithin_iff_minimal hT hB τ).mp hn⟩, ?_⟩
  rintro ρ ⟨hρ,hmin⟩
  have hnρ := (noWithin_iff_minimal hT hB ρ).mpr hmin
  have hm : permMatrix T B ρ = permMatrix T B τ :=
    (matrix_of_sameDoubleCoset T B hρ).symm.trans (matrix_of_sameDoubleCoset T B ho)
  have he : (⟨T,B,hT,hB,ρ,hnρ⟩ : PlatformDiagram n r c) = ⟨T,B,hT,hB,τ,hn⟩ :=
    matrix_injective hm
  exact congrArg PlatformDiagram.perm he

/-- The equivalence relation is the genuine two-sided permutation action.
Matrices prove its equivalence laws; they do not define its carrier. -/
def doubleCosetSetoid {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c) :
    Setoid (Equiv.Perm (Fin n)) where
  r := SameDoubleCoset T B
  iseqv :=
    ⟨fun σ => (sameDoubleCoset_iff_matrix T B σ σ).mpr rfl,
      fun {σ τ} h => (sameDoubleCoset_iff_matrix T B τ σ).mpr
        ((sameDoubleCoset_iff_matrix T B σ τ).mp h).symm,
      fun {σ τ ρ} h₁ h₂ => (sameDoubleCoset_iff_matrix T B σ ρ).mpr
        (((sameDoubleCoset_iff_matrix T B σ τ).mp h₁).trans
          ((sameDoubleCoset_iff_matrix T B τ ρ).mp h₂))⟩

abbrev DoubleCosets {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c) :=
  Quotient (doubleCosetSetoid T B)

/-- The actual matrix of a permutation on the prescribed contiguous platforms. -/
noncomputable def prescribedMatrix {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j) (σ : Equiv.Perm (Fin (∑ i, β i))) : Mat β α :=
  ⟨permMatrix (endpoint β rfl) (endpoint α h.symm) σ, by
    constructor
    · funext i
      rw [permMatrix, strandMatrix_rowSum,
        Equiv.sum_comp σ (fun a => if endpoint β rfl a = i then (1 : ℕ) else 0)]
      exact endpoint_count β rfl i
    · funext j
      rw [permMatrix, strandMatrix_colSum]
      exact endpoint_count α h.symm j⟩

noncomputable def cosetMatrix {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j) :
    DoubleCosets (endpoint β rfl) (endpoint α h.symm) → Mat β α :=
  Quotient.lift (prescribedMatrix β α h) (by
    intro σ τ he
    apply Subtype.ext
    exact matrix_of_sameDoubleCoset _ _ he)

/-- Source double cosets, rather than a matrix-labelled surrogate, are equivalent
to prescribed-margin nonnegative matrices. -/
noncomputable def doubleCosetEquiv {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j) :
    DoubleCosets (endpoint β rfl) (endpoint α h.symm) ≃ Mat β α :=
  Equiv.ofBijective (cosetMatrix β α h) ⟨by
    intro q₁ q₂ he
    induction q₁ using Quotient.inductionOn with | h σ =>
      induction q₂ using Quotient.inductionOn with | h τ =>
        apply Quotient.sound
        apply sameDoubleCoset_of_matrix
        exact congrArg Subtype.val he,
    by
      intro M
      let σ := (minimalPermEquiv β α h).symm M
      refine ⟨Quotient.mk _ σ.val, ?_⟩
      exact (minimalPermEquiv β α h).apply_symm_apply M⟩

/-- Choose the proven unique minimum in an actual orbit. No matrix or length
certificate is accepted as an argument. -/
noncomputable def minimalRepresentative {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (q : DoubleCosets T B) : Equiv.Perm (Fin n) :=
  Classical.choose (unique_minimal_representative hT hB q.out)

theorem minimalRepresentative_spec {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (q : DoubleCosets T B) :
    SameDoubleCoset T B q.out (minimalRepresentative hT hB q) ∧
      IsMinimal T B (minimalRepresentative hT hB q) :=
  (Classical.choose_spec (unique_minimal_representative hT hB q.out)).1

/-- EK's length of a double coset: inversion length of its actual minimum. -/
noncomputable def cosetLength {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (q : DoubleCosets T B) : ℕ :=
  inversions (minimalRepresentative hT hB q)

theorem cosetLength_eq_crossing_out {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (q : DoubleCosets T B) :
    cosetLength hT hB q = crossing (permMatrix T B q.out) := by
  have hs := minimalRepresentative_spec hT hB q
  have hn := (noWithin_iff_minimal hT hB (minimalRepresentative hT hB q)).mpr hs.2
  exact ((crossing_eq_inversions_iff hT hB _).mpr hn).symm.trans
    (congrArg crossing (matrix_of_sameDoubleCoset T B hs.1).symm)

theorem doubleCosetEquiv_apply {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j)
    (q : DoubleCosets (endpoint β rfl) (endpoint α h.symm)) :
    doubleCosetEquiv β α h q = cosetMatrix β α h q := rfl

theorem cosetMatrix_val_mk {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j) (σ : Equiv.Perm (Fin (∑ i, β i))) :
    (cosetMatrix β α h (Quotient.mk _ σ)).val =
      permMatrix (endpoint β rfl) (endpoint α h.symm) σ := rfl

theorem cosetLength_eq_crossing {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j)
    (q : DoubleCosets (endpoint β rfl) (endpoint α h.symm)) :
    cosetLength (endpoint_monotone β rfl) (endpoint_monotone α h.symm) q =
      crossing (doubleCosetEquiv β α h q) := by
  rw [cosetLength_eq_crossing_out, doubleCosetEquiv_apply]
  rw [← cosetMatrix_val_mk β α h q.out]
  exact congrArg (fun z => crossing (cosetMatrix β α h z).val) (Quotient.out_eq q)

noncomputable instance {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c) :
    Fintype (DoubleCosets T B) := by
  classical
  exact Fintype.ofSurjective (Quotient.mk _) Quotient.mk_surjective

/-- Literal EK (2.1) at q=-1 on the equal-degree branch. -/
noncomputable def sourcePairing {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j) : ℤ :=
  ∑ q : DoubleCosets (endpoint β rfl) (endpoint α h.symm),
    (-1 : ℤ) ^ cosetLength (endpoint_monotone β rfl) (endpoint_monotone α h.symm) q

theorem sourcePairing_eq_pairing {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) = ∑ j, α j) : sourcePairing β α h = pairing β α := by
  unfold sourcePairing pairing
  apply Fintype.sum_equiv (doubleCosetEquiv β α h)
  intro q
  exact congrArg (fun k => (-1 : ℤ)^k) (cosetLength_eq_crossing β α h q)

/-- Includes the orthogonal unequal-degree branch of source equation (2.1). -/
noncomputable def sourcePairingAll {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) : ℤ :=
  if h : (∑ i, β i) = ∑ j, α j then sourcePairing β α h else 0

theorem sourcePairingAll_eq_pairing {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    sourcePairingAll β α = pairing β α := by
  unfold sourcePairingAll
  split_ifs with h
  · exact sourcePairing_eq_pairing β α h
  · exact (pairing_degree_mismatch β α h).symm

end OddMath.Frontier.EKPlatformBijection
