import FormalConjectures.OEIS.«92243»

/-!
# OEIS A092243, conjecture 1: a proof

Upstream statement (FormalConjectures/OEIS/92243.lean, `OeisA92243.conjecture1`, tagged `research open`):

```
theorem conjecture1 : ∃ n > 250000, a n > 0
```

Here `a n` is the prime-gap "tug of war" score defined upstream (imported, not copied, so the definitions
are exactly upstream's). We prove the statement with the witness `n = 261150`, where `a 261150 = 1`.

Credit: the numerical fact comes from N. J. A. Sloane's OEIS table a092243_1.txt (n = 1..965562), which
shows a(261150) = 1. It was rechecked independently here with two sieves (Python and C).

Method:
1. `count_eq_length_filterRange`: `Nat.count p N` equals the length of `(List.range N).filter p`.
2. `count_getElem_filterRange`: the `i`-th element `q` of that list satisfies `Nat.count p q = i`.
3. Hence `Nat.nth p i = q` (Mathlib's `Nat.nth_count`). This turns the noncomputable `Nat.nth Nat.Prime`
   into a computable list of primes.
4. Rewrite `a 261150` term-by-term into a computable sum over an array of the primes below 3666582, and
   evaluate that sum with `native_decide`.

`native_decide` trusts the Lean compiler. In Lean 4.33.1 this shows up in `#print axioms` as the per-call axioms
`OeisA92243.len_primesL._native.native_decide.ax_1_1` and `OeisA92243.scoreC_pos._native.native_decide.ax_1_1`,
which assert `decide (261150 < primesL.length) = true` and `decide (0 < scoreC 261150) = true`.
It is used only for these two concrete computations.
-/

namespace OeisA92243

open Finset

/-- The list of `x < N` with `p x`, in increasing order. A named function, so that lemmas about it can be
applied to `filterRange Nat.Prime bound` without Lean unfolding (and trying to evaluate) the list. -/
def filterRange (p : ℕ → Prop) [DecidablePred p] (N : ℕ) : List ℕ :=
  (List.range N).filter (fun x => decide (p x))

/-- `Nat.count p N` is the length of `filterRange p N`. -/
theorem count_eq_length_filterRange (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    Nat.count p N = (filterRange p N).length := by
  induction N with
  | zero => simp [filterRange]
  | succ N ih =>
    rw [Nat.count_succ, ih]
    unfold filterRange
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases h : p N <;> simp [h]

/-- The `i`-th element of `filterRange p N` has exactly `i` smaller elements satisfying `p`. -/
theorem count_getElem_filterRange (p : ℕ → Prop) [DecidablePred p] (N i : ℕ)
    (hi : i < (filterRange p N).length) :
    Nat.count p ((filterRange p N)[i]) = i := by
  induction N generalizing i with
  | zero => simp [filterRange] at hi
  | succ N ih =>
    have hsplit : filterRange p (N + 1) =
        filterRange p N ++ (if p N then [N] else []) := by
      unfold filterRange
      rw [List.range_succ, List.filter_append]
      by_cases h : p N <;> simp [h]
    have hi2 : i < (filterRange p N ++ (if p N then [N] else [])).length := hsplit ▸ hi
    have hget : (filterRange p (N + 1))[i] = (filterRange p N ++ (if p N then [N] else []))[i] := by
      simp only [hsplit]
    rw [hget]
    by_cases hlt : i < (filterRange p N).length
    · rw [List.getElem_append_left hlt]
      exact ih i hlt
    · have hpN : p N := by
        by_contra hpN
        simp [hpN] at hi2
        omega
      have hi' : i = (filterRange p N).length := by
        simp [hpN] at hi2
        omega
      rw [List.getElem_append_right (by omega)]
      simp [hpN, hi', count_eq_length_filterRange]

/-- Membership in `filterRange`. -/
theorem mem_filterRange (p : ℕ → Prop) [DecidablePred p] (N x : ℕ) :
    x ∈ filterRange p N ↔ x < N ∧ p x := by
  simp [filterRange]

/-- `Nat.nth p i` is the `i`-th element of `filterRange p N`, whenever that element exists. -/
theorem nth_eq_getElem_filterRange (p : ℕ → Prop) [DecidablePred p] (N i : ℕ)
    (hi : i < (filterRange p N).length) :
    Nat.nth p i = (filterRange p N)[i] := by
  have hp : p (filterRange p N)[i] := ((mem_filterRange p N _).mp (List.getElem_mem hi)).2
  conv_lhs => rw [← count_getElem_filterRange p N i hi]
  exact Nat.nth_count hp

/-- The search bound `3666582`. Irreducible: elaborating terms such as `(filterRange Nat.Prime 3666582)[i]` with
the raw literal makes Lean unfold `List.range` on it and hit the recursion limit. -/
@[irreducible] def bound : ℕ := 3666582

/-- The primes below `bound = 3666582` (the 261151st prime, `p_261150` 0-indexed, is `3666581`).
Irreducible, so that elaboration never tries to unfold (and evaluate) the 261151-element list;
it is only ever evaluated by compiled code inside `native_decide`. -/
@[irreducible] def primesL : List ℕ := filterRange Nat.Prime bound

theorem primesL_eq : primesL = filterRange Nat.Prime bound := by unfold primesL; rfl

/-- The same primes as an array, for constant-time indexing in the computation. -/
@[irreducible] def primesA : Array ℕ := primesL.toArray

theorem primesA_eq : primesA = primesL.toArray := by unfold primesA; rfl

theorem len_primesL : 261150 < primesL.length := by native_decide

theorem nth_prime_eq (i : ℕ) (hi : i < primesL.length) : Nat.nth Nat.Prime i = primesA[i]! := by
  have hi' : i < (filterRange Nat.Prime bound).length := primesL_eq ▸ hi
  have h1 : Nat.nth Nat.Prime i = (filterRange Nat.Prime bound)[i]'hi' :=
    nth_eq_getElem_filterRange Nat.Prime bound i hi'
  have hA : i < primesA.size := by
    rw [primesA_eq, List.size_toArray]
    exact hi
  have h2 : primesA[i]! = primesA[i]'hA := getElem!_pos primesA i hA
  have h3 : primesA[i]'hA = (filterRange Nat.Prime bound)[i]'hi' := by
    simp only [primesA_eq, List.getElem_toArray, primesL_eq]
  rw [h2, h3]
  exact h1

/-- Computable version of the score, reading primes from `primesA`. -/
def scoreC (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 2 n,
    (((primesA[k]! - primesA[k - 1]! : ℕ) : ℤ) - ((primesA[k - 1]! - primesA[k - 1 - 1]! : ℕ) : ℤ)).sign

theorem a_eq_scoreC : a 261150 = scoreC 261150 := by
  unfold a scoreC
  rw [if_neg (by norm_num)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  have h := len_primesL
  unfold primeGap
  rw [nth_prime_eq k (by omega), nth_prime_eq (k - 1) (by omega), nth_prime_eq (k - 1 - 1) (by omega)]

theorem scoreC_pos : 0 < scoreC 261150 := by native_decide

/-- **OEIS A092243, conjecture 1** (upstream `OeisA92243.conjecture1`, same statement): the tug-of-war
score is positive for some `n > 250000`. Witness: `n = 261150`. -/
theorem conjecture1_proof : ∃ n > 250000, a n > 0 :=
  ⟨261150, by norm_num, by rw [a_eq_scoreC]; exact scoreC_pos⟩

end OeisA92243

/- Audit: the proved statement is syntactically identical (`Expr ==`) to upstream's `conjecture1`. -/
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some c1 := env.find? `OeisA92243.conjecture1 | throwError "upstream conjecture1 not found"
  let some c2 := env.find? `OeisA92243.conjecture1_proof | throwError "proof not found"
  unless c1.type == c2.type do throwError "TYPE MISMATCH between conjecture1 and conjecture1_proof"
  logInfo m!"OK: type of conjecture1_proof == type of upstream conjecture1: {c2.type}"

#print axioms OeisA92243.conjecture1_proof
