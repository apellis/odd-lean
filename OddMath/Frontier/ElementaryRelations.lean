import OddMath.Frontier.OddSymmetricKernel

/-! EKL 1111.1320v1, Lemma 2.3. Literal finite elementary sums. -/
namespace OddMath.Frontier.ElementaryRelations
open FiniteCompleteElementary FiniteCompleteElementary.FiniteWords PlacticEvaluation
noncomputable section

variable {R : Type*} [Ring R]

private theorem sign_same {i j : ℕ} (h : Even (i+j)) :
    (-1:ℤ)^i = (-1:ℤ)^j := by
  have hh : (i+j)%2 = 0 := Nat.even_iff.mp h
  rw [← Nat.mod_add_div i 2, ← Nat.mod_add_div j 2]
  simp only [pow_add, pow_mul]
  norm_num
  have hm : i%2 = j%2 := by omega
  rw [hm]

private theorem sign_cases (i : ℕ) : (-1:ℤ)^i = 1 ∨ (-1:ℤ)^i = -1 := by
  exact neg_one_pow_eq_or ℤ i

private theorem move_right (a b : R) (s : ℤ) (hs : s*s=1)
    (h : a*b = s • (b*a)) (z : R) : b*(a*z) = s • (a*(b*z)) := by
  have hh := congrArg (fun v => s • (v*z)) h
  simpa only [smul_mul_assoc, smul_smul, hs, one_smul, _root_.mul_assoc] using hh.symm

private theorem even_step (a A B C D : R) (s : ℤ) (hs : s=1 ∨ s= -1)
    (hA : ∀ z, A*(a*z) = -s • (a*(A*z)))
    (hB : ∀ z, B*(a*z) = s • (a*(B*z)))
    (hC : ∀ z, C*(a*z) = -s • (a*(C*z)))
    (hD : ∀ z, D*(a*z) = s • (a*(D*z)))
    (hAC : A*C=C*A) (hBD : B*D=D*B)
    (hodd : B*C+s • (C*B)=s • (A*D)+D*A) :
    (a*B+A)*(a*D+C)=(a*D+C)*(a*B+A) := by
  rcases hs with rfl | rfl
  · simp only [one_smul, neg_smul] at *
    linear_combination (norm := noncomm_ring [hA,hB,hC,hD]) hAC + a*hodd + a*a*hBD
  · simp only [neg_neg, one_smul, neg_smul] at *
    linear_combination (norm := noncomm_ring [hA,hB,hC,hD]) hAC + a*hodd - a*a*hBD

private theorem odd_step (a A B C D E F : R) (s : ℤ) (hs : s=1 ∨ s= -1)
    (hA : ∀ z, A*(a*z) = -s • (a*(A*z)))
    (hB : ∀ z, B*(a*z) = s • (a*(B*z)))
    (hC : ∀ z, C*(a*z) = s • (a*(C*z)))
    (hD : ∀ z, D*(a*z) = -s • (a*(D*z)))
    (hE : ∀ z, E*(a*z) = s • (a*(E*z)))
    (hF : ∀ z, F*(a*z) = s • (a*(F*z)))
    (hBF : B*F=F*B) (hCE : C*E=E*C)
    (hlo : B*D+s • (D*B)=s • (A*E)+E*A)
    (hhi : A*F+(-s) • (F*A)=(-s) • (C*D)+D*C) :
    (a*B+A)*(a*D+F)+(-s) • ((a*D+F)*(a*B+A)) =
      (-s) • ((a*A+C)*(a*E+D))+(a*E+D)*(a*A+C) := by
  rcases hs with rfl | rfl
  · simp only [one_smul, neg_smul] at *
    linear_combination (norm := noncomm_ring [hA,hB,hC,hD,hE,hF])
      hhi + a*hBF + a*hCE + a*a*hlo
  · simp only [neg_neg, one_smul, neg_smul] at *
    linear_combination (norm := noncomm_ring [hA,hB,hC,hD,hE,hF])
      hhi + a*hBF + a*hCE - a*a*hlo

private theorem boundary_step (a A B C D : R)
    (hA : ∀ z, A*(a*z) = -(a*(A*z)))
    (hB : ∀ z, B*(a*z) = -(a*(B*z)))
    (hC : ∀ z, C*(a*z) = a*(C*z))
    (hAC : D+D=A*C+C*A) (hAB : A*B=B*A) :
    (a*C+D)+(a*C+D)=(a+A)*(a*B+C)+(a*B+C)*(a+A) := by
  have hB0 : B*a = -(a*B) := by simpa using hB 1
  have hC0 : C*a = a*C := by simpa using hC 1
  linear_combination (norm := noncomm_ring [hA,hB,hC,hB0,hC0]) hAC+a*hAB

/-- Simultaneous alphabet induction on the imported literal strict-word sums.
The degree-zero cases are proved, not inferred from the source's restricted ranges. -/
private theorem strict_relations {n : ℕ} (x : Fin n → R)
    (hx : ∀ i j, i ≠ j → x i*x j = -(x j*x i)) :
    (∀ i j, Even (i+j) → strictSum x i*strictSum x j = strictSum x j*strictSum x i) ∧
    (∀ i j, Even (i+j) →
      strictSum x i*strictSum x (j+1)+(-1:ℤ)^i • (strictSum x (j+1)*strictSum x i) =
      (-1:ℤ)^i • (strictSum x (i+1)*strictSum x j)+strictSum x j*strictSum x (i+1)) := by
  induction n with
  | zero =>
    constructor <;> intro i j h <;> cases i <;> cases j <;> simp
  | succ n ih =>
    let y : Fin n → R := fun i => x i.succ
    obtain ⟨he, ho⟩ := ih y (fun i j hij => hx i.succ j.succ
      (fun h => hij (Fin.succ_injective n h)))
    have hm (k : ℕ) (z : R) : strictSum y k*(x 0*z) =
        (-1:ℤ)^k • (x 0*(strictSum y k*z)) := by
      apply move_right
      · simp [← pow_add, ← two_mul, pow_mul]
      · exact mul_strictSum (x 0) y (fun i => hx 0 i.succ (Fin.succ_ne_zero i).symm) k
    have hz (j : ℕ) (hj : Even j) :
        strictSum x (j+1)+strictSum x (j+1) =
          strictSum x 1*strictSum x j+strictSum x j*strictSum x 1 := by
      cases j with
      | zero => simp
      | succ j =>
        have sj : (-1:ℤ)^(j+1)=1 := hj.neg_one_pow
        have sj' : (-1:ℤ)^j= -1 := by
          rw [pow_succ, mul_neg_one] at sj
          omega
        have hAC := ho 0 (j+1) (by simpa using hj)
        have hAB := he 1 j (by simpa [Nat.add_comm] using hj)
        simp only [strictSum_zero, one_mul, mul_one, pow_zero, one_smul] at hAC
        simp only [strictSum_succ, strictSum_zero, mul_one]
        apply boundary_step
        · intro z; simpa using hm 1 z
        · intro z; simpa only [sj', neg_one_smul] using hm j z
        · intro z; simpa only [sj, one_smul] using hm (j+1) z
        · exact hAC
        · exact hAB
    constructor
    · intro i j h
      cases i with
      | zero => simp
      | succ i =>
        cases j with
        | zero => simp
        | succ j =>
          have hp : Even (i+j) := by rw [Nat.even_iff] at *; omega
          have ss := sign_same hp
          simp only [strictSum_succ]
          apply even_step (s := (-1:ℤ)^i) _ _ _ _ _ (sign_cases i)
          · intro z; simpa only [pow_succ, mul_neg_one] using hm (i+1) z
          · exact hm i
          · intro z; simpa only [pow_succ, mul_neg_one, ← ss] using hm (j+1) z
          · intro z; simpa only [← ss] using hm j z
          · exact he (i+1) (j+1) h
          · exact he i j hp
          · exact ho i j hp
    · intro i j h
      cases i with
      | zero => simpa using hz j (by simpa using h)
      | succ i =>
        cases j with
        | zero =>
          have hp : Even (i+1) := by simpa using h
          simpa only [strictSum_zero, mul_one, one_mul, hp.neg_one_pow, one_smul, Nat.zero_add, add_comm] using
            (hz (i+1) hp).symm
        | succ j =>
          have hp : Even (i+j) := by rw [Nat.even_iff] at *; omega
          have ss := sign_same hp
          simp only [strictSum_succ, pow_succ, mul_neg_one]
          apply odd_step (s := (-1:ℤ)^i) _ _ _ _ _ _ _ (sign_cases i)
          · intro z; simpa only [pow_succ, mul_neg_one] using hm (i+1) z
          · exact hm i
          · intro z; simpa only [pow_succ, mul_neg_one, neg_neg] using hm (i+1+1) z
          · intro z; simpa only [pow_succ, mul_neg_one, ← ss] using hm (j+1) z
          · intro z; simpa only [← ss] using hm j z
          · intro z; simpa only [pow_succ, mul_neg_one, neg_neg, ← ss] using hm (j+1+1) z
          · exact he i (j+1+1) (by rw [Nat.even_iff] at *; omega)
          · exact he (i+1+1) j (by rw [Nat.even_iff] at *; omega)
          · exact ho i j hp
          · simpa only [pow_succ, mul_neg_one] using ho (i+1) (j+1) h

/-- Same-parity elementary sums commute in every finite alphabet, including degree zero. -/
theorem elementary_even (n i j : ℕ) (h : Even (i+j)) :
    elementaryPoly n i*elementaryPoly n j = elementaryPoly n j*elementaryPoly n i := by
  simpa only [elementaryPoly_eq_strictSum] using
    (strict_relations (tildeGenerator (n := n)) tilde_anticommute).1 i j h

/-- EKL's odd relation, extended to all natural indices by the literal-sum induction. -/
theorem elementary_odd (n i j : ℕ) (h : Even (i+j)) :
    elementaryPoly n i*elementaryPoly n (j+1)+(-1:ℤ)^i • (elementaryPoly n (j+1)*elementaryPoly n i) =
    (-1:ℤ)^i • (elementaryPoly n (i+1)*elementaryPoly n j)+elementaryPoly n j*elementaryPoly n (i+1) := by
  simpa only [elementaryPoly_eq_strictSum] using
    (strict_relations (tildeGenerator (n := n)) tilde_anticommute).2 i j h

/-- The genuine i=0 corollary, with no division by two. -/
theorem elementary_one_even (n m : ℕ) :
    elementaryPoly n 1*elementaryPoly n (2*m)+elementaryPoly n (2*m)*elementaryPoly n 1 =
    (2:ℤ) • elementaryPoly n (2*m+1) := by
  have hh := elementary_odd n 0 (2*m) (by simp [even_two_mul])
  simpa only [elementaryPoly_zero, one_mul, mul_one, pow_zero, one_smul,
    Nat.zero_add, two_zsmul] using hh.symm

open OddSymmetricKernel

/-- The commuting relation on the actual joint-kernel subtype elements. -/
theorem elementary_even_kernel (n i j : ℕ) (h : Even (i+j)) :
    (⟨elementaryPoly (n+2) i, elementary_mem n i⟩ : kernelSubring n) *
      ⟨elementaryPoly (n+2) j, elementary_mem n j⟩ =
    (⟨elementaryPoly (n+2) j, elementary_mem n j⟩ : kernelSubring n) *
      ⟨elementaryPoly (n+2) i, elementary_mem n i⟩ := by
  apply Subtype.ext
  exact elementary_even (n+2) i j h

/-- The odd defining relation inside the actual joint-kernel subring. -/
theorem elementary_odd_kernel (n i j : ℕ) (h : Even (i+j)) :
    (⟨elementaryPoly (n+2) i, elementary_mem n i⟩ : kernelSubring n) *
      ⟨elementaryPoly (n+2) (j+1), elementary_mem n (j+1)⟩ +
    (-1:ℤ)^i • ((⟨elementaryPoly (n+2) (j+1), elementary_mem n (j+1)⟩ : kernelSubring n) *
      ⟨elementaryPoly (n+2) i, elementary_mem n i⟩) =
    (-1:ℤ)^i • ((⟨elementaryPoly (n+2) (i+1), elementary_mem n (i+1)⟩ : kernelSubring n) *
      ⟨elementaryPoly (n+2) j, elementary_mem n j⟩) +
    (⟨elementaryPoly (n+2) j, elementary_mem n j⟩ : kernelSubring n) *
      ⟨elementaryPoly (n+2) (i+1), elementary_mem n (i+1)⟩ := by
  apply Subtype.ext
  exact elementary_odd (n+2) i j h

/-- The integral anticommutator corollary in the actual joint kernel. -/
theorem elementary_one_even_kernel (n m : ℕ) :
    (⟨elementaryPoly (n+2) 1, elementary_mem n 1⟩ : kernelSubring n) *
      ⟨elementaryPoly (n+2) (2*m), elementary_mem n (2*m)⟩ +
    (⟨elementaryPoly (n+2) (2*m), elementary_mem n (2*m)⟩ : kernelSubring n) *
      ⟨elementaryPoly (n+2) 1, elementary_mem n 1⟩ =
    (2:ℤ) • (⟨elementaryPoly (n+2) (2*m+1), elementary_mem n (2*m+1)⟩ : kernelSubring n) := by
  apply Subtype.ext
  exact elementary_one_even (n+2) m

end
end OddMath.Frontier.ElementaryRelations
