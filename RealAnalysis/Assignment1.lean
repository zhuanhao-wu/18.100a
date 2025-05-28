import Mathlib
import Mathlib.SetTheory.Cardinal.Defs

universe u
variable {α : Type u}

-- this is the class exercise
-- TODO: is this problem of Nonempty set a restriction of how bij is defined in Lean 4?
open Function
theorem bij_inv_of_bij {A B: Set α} {f: A→B} [Nonempty A]:
  Bijective f → Bijective (invFun f) := by
  intro h_bij
  -- by definition, bijective := injective ∧ surjective
  constructor
  · -- first by definition injective means
    -- f⁻¹ y₁ = f⁻¹ y₂ → y₁ = y₂
    intro y₁ y₂ hf
    -- we also know h_bij is surjective so we can find x₁ and x₂ for the inverse function
    obtain h_surj := h_bij.surjective
    -- now this is the technical details about the inverse function
    -- as it uses choose, so we need to go extra steps
    unfold invFun at hf
    -- so x₁ and x₂ are in the range of f
    have h₁ := h_surj y₁
    have h₂ := h_surj y₂
    rw [dif_pos h₁, dif_pos h₂] at hf
    -- now due to injective property of f
    have h1 := Exists.choose_spec h₁
    have h2 := Exists.choose_spec h₂
    have: f h₁.choose = f h₂.choose := by
      rw [hf, h2]
    rw [h1, h2] at this
    exact this
  · -- now we need to show surjective
    intro x
    generalize hy: f x = y
    use y
    unfold invFun
    have : ∃ (x: A), f x = y := by
      -- we know f is surjective, so we can find x such that f x = y
      obtain h_surj := h_bij.surjective
      exact h_surj y
    rw [dif_pos this]
    have hx := Exists.choose_spec this
    -- now injective property of f
    have : f x = f this.choose := by
      rw [hy, hx]
    have h_inj := h_bij.injective this
    rw [h_inj]

open Cardinal in
theorem odd_same_card:
  #{k : ℕ | ∃i : ℕ, k = 2*i + 1} = #ℕ := by
  unfold Cardinal.mk Quotient.mk'
  apply Quotient.sound
  -- now we are talking about show bijective
  symm
  constructor
  let toFun (i: ℕ): {k | ∃ i, k = 2 * i + 1} := ⟨2 * i + 1, by simp⟩
  let invFun (i: {k | ∃ i, k = 2 * i + 1}) := (i.val - 1) / 2
  apply Equiv.mk toFun invFun
  · intro x
    unfold toFun invFun
    simp
  · intro x
    unfold toFun invFun
    obtain ⟨x, hx⟩ := x
    simp at hx
    obtain ⟨i, hi⟩ := hx
    simp
    rw [hi]
    simp


/-
You may want to complete [Theorem Proving in Lean 4 (TPIL)](https://lean-lang.org/theorem_proving_in_lean4/) and [Mathematics in Lean 4](https://leanprover-community.github.io/mathematics_in_lean/) to understsand the proofs.
-/

/-
**Exercise 0.3.6:** Prove:
a) 𝐴∩(𝐵∪𝐶)=(𝐴∩𝐵)∪(𝐴∩𝐶).
b) 𝐴∪(𝐵∩𝐶)=(𝐴∪𝐵)∩(𝐴∪𝐶).

Try to not use the `simp` tactic for this problem at least once.
-/
theorem exercise_0_3_6_a {A B C: Set α}:
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  -- two sets are equal if they are subsets of each other,
  ext x
  apply Iff.intro
  -- case 1: x ∈ A ∩ (B ∪ C) -> x ∈ A ∧ x ∈ (B ∪ C)
  · intro h
    -- unfold the notation definition in hypothesis h
    dsimp [· ∩ ·, · ∪ ·] at h
    unfold Set.inter Set.union at h
    dsimp [· ∈ ·] at h
    unfold Set.Mem at h
    -- unfold the definitions in the goal
    dsimp [· ∩ ·, · ∪ ·]
    unfold Set.inter Set.union
    dsimp [· ∈ ·]
    unfold Set.Mem
    -- following the basic logic
    -- ctrl+click on and_or_left you will see the definition
    -- now this proposition follows from the underlying theory used in lean 4 (refer to TPIL)
    rw [and_or_left] at h
    exact h
  · -- case 2
    intro h
    -- with `simp` tactics we can complete this proof easily
    simp at *
    rwa [and_or_left]


theorem exercise_0_3_6_b {A B C: Set α}:
  A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  -- or we can even go further
  ext x
  -- with the following simp, we are left with a bunch of conjunctions and disjunctions
  simp
  -- tauto automatically checks logic tautology
  tauto

/-
**Exercise 0.3.11:** Prove by induction that 𝑛 < 2^𝑛 for all 𝑛∈ℕ.
-/
theorem exercise_0_3_11 {n: ℕ}: n < 2^n := by
  induction' n with n ih
  · simp
  · -- we would start from a higher base case
    induction' n with n ih
    · simp
    · rw [Nat.pow_succ]
      have h := Nat.mul_lt_mul_of_pos_right (k := 2) ih (by simp)
      apply lt_of_le_of_lt _ h
      rw [Nat.mul_two]
      apply Nat.add_le_add_left
      simp


/-
**Exercise 0.3.12:** Show that for a finite set 𝐴 of cardinality 𝑛,the cardinality of P(𝐴)is 2^𝑛

NOTE
Set.ncard returns 0 if the set is empty *or* infinite.
And if we want to encode the cardinality of a finite set, we would use `Set.encard` instead.
But for now, we will just use both `Set.Finite` and `Set.ncard` to encode the property in the problem statement.

There are other possible proofs where we do induction on the set directly.
-/
theorem exercise_0_3_12 (n: ℕ):
  ∀ (A: Set α),
  A.Finite →
  A.ncard = n → (𝒫 A).ncard = 2^n
  := by
  -- this is how it is done in everyday work
  intro A hF hN
  rw [Set.ncard_powerset _ hF, hN]


-- but since we are learning, we need to use the definitions learned in class
theorem exercise_0_3_12' (n: ℕ):
  ∀ (A: Set α),
  A.Finite →
  A.ncard = n → (𝒫 A).ncard = 2^n := by
  -- again we will use induction on n
  induction' n with n ih
  · intro A hF h_ncard
    -- if ncard = 0 and A is finite, then A is empty
    -- c.f. Definition 0.3.27 in the book
    rw [Set.ncard_eq_zero hF] at h_ncard
    rw [h_ncard]
    -- since the powerset of an empty set is a singleton set, it's cardinality is 1
    simp
  · sorry


/-
**Exercise 0.3.15:** Prove that 𝑛^3 +5𝑛 is divisible by 6 for all 𝑛∈ℕ.
-/
theorem exercise_0_3_15 {n: ℕ}: 6 ∣ n^3 + 5*n := by
  induction' n with n ih
  · simp
  · have this: (n + 1)^3 + 5*(n + 1) = n^3 + 5*n + (3*(n*(n + 1)) + 6) := by
      ring
    -- we split the induction hypothesis into two parts
    -- 1. n^3 + 5*n is divisible by 6 following the induction hypothesis
    rw [this]
    apply Nat.dvd_add ih
    -- next 3 (n*(n + 1)) + 6 is divisible by 6
    -- because n*(n + 1) is even
    have h_even: Even (n*(n + 1)) := Nat.even_mul_succ_self n
    rw [even_iff_exists_two_mul] at h_even
    obtain ⟨k, hk⟩ := h_even
    rw [hk]
    ring_nf
    simp

/-
**Exercise 0.3.19:**
Give an example of a countably infinite collection of finite sets 𝐴1, 𝐴2, ..., whose union is not a finite set.
-/
theorem exercise_0_3_19:
  ∃(A : ℕ → Set ℕ), (∀n, (A n).Finite) ∧
  (⋃ n, A n).Infinite := by
  use fun n => {n}
  simp
  have h_is_nat: (⋃ (n:ℕ), {n}) = Set.univ := by
    ext x
    constructor
    · simp
    · simp

  rw [h_is_nat]
  unfold Set.Infinite Set.Finite
  simp
  rw [Cardinal.infinite_iff]
  simp

/-
**Exercise 6:**
In this exercise, you will prove that
  |{q ∈ Q : q > 0}| = |N|.
In what follows, we will use the following theorem without proof.
Note that the stated theorem corresponds to
1. a natural number has a unique factorization into prime numbers,
- Nat.factorization

-/
open Cardinal in
theorem exercise_6:
  #{q: ℚ // q > 0}  = #ℕ := by
  sorry
