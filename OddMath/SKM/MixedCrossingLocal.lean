import OddMath.SKM.CupFamilyCoefficients

/-! # Local numerical crossing calculation for BE2 Claim 4

BE2, arXiv:1701.04133v2, Theorem 10.3, Claim 4. The underlying minimalization
step is described in Khovanov–Lauda, arXiv:0807.3250v1, §2.2, the unequal-colour
adjacent-exchange lemma: attach a crossing, then remove a bigon if the two strands
already intersect. Here we prove the literal decorated attachment and the local
oppositely oriented bigon calculation from the existing generator table.

These are NOT the global normalization or representative-family equivalence.
In particular, no invariance under general Reidemeister II is asserted.
-/
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
variable {I X : Type*} [AddCommGroup X]

/-- Literal crossing attachment below a decorated matching, with its boundary
changed by the adjacent swap. This identity does not assert reducedness. -/
theorem dLay_cross_attach (a b : List (Letter I)) (x y : Letter I)
    (ds : List (DTMove I)) :
    dLay (a ++ x :: y :: b) (.tm (.mv (.cross a.length)) :: ds) =
      (xCrL x y).map (xwhL a b) ++ dLay (a ++ y :: x :: b) ds := by
  simp only [dLay, tmLay, moveLay_cross, tLet, chStep_cross]

/-- The source rightward crossing is precisely `sigmaL` in the layer encoding. -/
theorem dLay_right_cross_attach (a b : List (Letter I)) (i j : I)
    (ds : List (DTMove I)) :
    dLay (a ++ (true, i) :: (false, j) :: b)
        (.tm (.mv (.cross a.length)) :: ds) =
      ((sigmaL j i).map ofL).map (xwhL a b) ++
        dLay (a ++ (false, j) :: (true, i) :: b) ds := by
  rw [dLay_cross_attach]
  rfl

/-- Literal rightward attachment has no integer-degree shift and has the
product of the colour parities as its parity shift. The numerical statement
also holds at equal colours; unequal colours are needed for normalization. -/
theorem right_cross_attach_degree_parity (D : Datum I X) (sy : Symmetrizer D)
    (μ : X) (a b : List (Letter I)) (i j : I) (ds : List (DTMove I)) :
    tableDegree D sy μ (dLay (a ++ (true, i) :: (false, j) :: b)
        (.tm (.mv (.cross a.length)) :: ds)) =
      tableDegree D sy μ (dLay (a ++ (false, j) :: (true, i) :: b) ds) ∧
    xpar D μ (dLay (a ++ (true, i) :: (false, j) :: b)
        (.tm (.mv (.cross a.length)) :: ds)) =
      xpar D μ (dLay (a ++ (false, j) :: (true, i) :: b) ds) +
        D.parity i * D.parity j := by
  rw [dLay_cross_attach]
  simp only [tableDegree_append, tableDegree_whisk, tableDegree_cross,
    Bool.true_eq_false, ↓reduceIte, zero_add, xpar_append, xpar_map_xwhL, xpar_cross]
  exact ⟨trivial, add_comm _ _⟩

/-- The particular opposite-orientation bigon used in the source proof has
zero table degree and zero total parity. This is a local numerical identity,
not a global bigon extraction theorem or a quotient relation. -/
theorem opposite_bigon_degree_parity (D : Datum I X) (sy : Symmetrizer D)
    (μ : X) (a b : List (Letter I)) (i j : I) (ε : Bool) (ds : List (DTMove I)) :
    tableDegree D sy μ (dLay (a ++ (ε, i) :: (!ε, j) :: b)
        (.tm (.mv (.cross a.length)) :: .tm (.mv (.cross a.length)) :: ds)) =
      tableDegree D sy μ (dLay (a ++ (ε, i) :: (!ε, j) :: b) ds) ∧
    xpar D μ (dLay (a ++ (ε, i) :: (!ε, j) :: b)
        (.tm (.mv (.cross a.length)) :: .tm (.mv (.cross a.length)) :: ds)) =
      xpar D μ (dLay (a ++ (ε, i) :: (!ε, j) :: b) ds) := by
  rw [dLay_cross_attach, dLay_cross_attach]
  constructor
  · cases ε <;> simp [tableDegree_cross]
  · simp only [xpar_append, xpar_map_xwhL, xpar_cross]
    have hz : D.parity i * D.parity j + D.parity j * D.parity i = 0 := by
      rw [mul_comm (D.parity j), ← two_mul]
      have ht : (2 : ZMod 2) = 0 := by decide
      rw [ht, zero_mul]
    rw [← add_assoc, hz, zero_add]

end OddMath.SKM
