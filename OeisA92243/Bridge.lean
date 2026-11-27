/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Mrigank.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import OeisA92243.Checks
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Soundness: from the kernel computation to the tug-of-war score

`OeisA92243.certs_ok` (checked by the kernel) says that running the certificate gives the state
`(3666539, 3666581, 1, 261151)`. This file proves what that means:

  `partialScore 261150 = 1`,

where `partialScore m = ∑ k ∈ Icc 2 m, sign(g k - g (k-1))` is the upstream sum, written with
`Nat.nth Nat.Prime` exactly as in upstream's `a` (after unfolding `primeGap`).

Steps:
1. `isP_iff`: on a block, the gcd test is a primality test (under the side conditions).
2. Bootstrap: the primes below 48 are `small` (`small_complete`), so the 14 low blocks are sound;
   they find exactly `sp` above 3 (`low_primes`), so every prime below 2209 is in `sp`
   (`sp_complete`), so the 367 high blocks are sound.
3. The blocks tile `[4, 3666582)` (`contig_*`, `blocksEnd_*`), so the numbers kept by all blocks,
   in order, are the primes in `[4, 3666582)`.
4. Folding `step` over the primes `p_2, ..., p_m` from `(p_0, p_1, 0, 2)` gives
   `(p_(m-1), p_m, partialScore m, m + 1)` (`fold_primes`), and `p_i` is the `i`-th element of the
   list of primes below `N` (`nth_eq_getElem_filterRange`, via Mathlib's `Nat.nth_count`).

Everything is proved for general bounds; the numbers 3666582 and 261150 only enter at the end,
through `exact`/`rw` (never `simp` or `decide`, which could try to unfold a 3.6-million-element list).
-/

namespace OeisA92243

/-! ## 1. The gcd test is a primality test -/

theorem dvd_prodL {q : ℕ} {ps : List ℕ} (h : q ∈ ps) : q ∣ prodL ps := by
  induction ps with
  | nil => simp at h
  | cons r rs ih =>
    simp only [prodL]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.dvd_mul_right q _
    · exact (ih h).mul_left r

theorem prime_dvd_prodL {p : ℕ} (hp : p.Prime) {ps : List ℕ} (h : p ∣ prodL ps) :
    ∃ q ∈ ps, p ∣ q := by
  induction ps with
  | nil =>
    have h1 : p ∣ 1 := by simpa only [prodL] using h
    exact absurd (Nat.eq_one_of_dvd_one h1) hp.ne_one
  | cons r rs ih =>
    simp only [prodL] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact ⟨r, by simp, h⟩
    · obtain ⟨q, hq, hpq⟩ := ih h
      exact ⟨q, by simp [hq], hpq⟩

/-- **The gcd test.** For `n` in `[lo, hi)`: `gcd n (∏ ps) = 1` iff `n` is prime, provided every
element of `ps` lies in `(0, lo)` and every prime `q` with `q * q < hi` is in `ps`. -/
theorem isP_iff {ps : List ℕ} {lo hi n : ℕ} (hlo : 2 ≤ lo) (hps : ∀ q ∈ ps, 0 < q ∧ q < lo)
    (hcompl : ∀ q, q.Prime → q * q < hi → q ∈ ps) (hn1 : lo ≤ n) (hn2 : n < hi) :
    isP (prodL ps) n = true ↔ n.Prime := by
  unfold isP
  rw [Nat.beq_eq]
  constructor
  · intro hg
    by_contra hnp
    have hq := Nat.minFac_prime (show n ≠ 1 by omega)
    have hsq := Nat.minFac_sq_le_self (show 0 < n by omega) hnp
    have hlt : n.minFac * n.minFac < hi := by
      have := lt_of_le_of_lt hsq hn2
      rwa [pow_two] at this
    have h1 : n.minFac ∣ Nat.gcd n (prodL ps) :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (dvd_prodL (hcompl _ hq hlt))
    rw [hg] at h1
    exact hq.ne_one (Nat.eq_one_of_dvd_one h1)
  · intro hp
    by_contra hg
    have hd : Nat.gcd n (prodL ps) ∣ n := Nat.gcd_dvd_left _ _
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact hg h
    · have hnQ := Nat.gcd_dvd_right n (prodL ps)
      rw [h] at hnQ
      obtain ⟨q, hq, hnq⟩ := prime_dvd_prodL hp hnQ
      obtain ⟨hq0, hqlo⟩ := hps q hq
      have := Nat.le_of_dvd hq0 hnq
      omega

/-- On a block satisfying the side conditions, the gcd filter is the prime filter. -/
theorem blockFilter_eq (c : Cert) (hlo : 2 ≤ c.1)
    (hps : ∀ q ∈ sp.take c.2.2.1, 0 < q ∧ q < c.1)
    (hcompl : ∀ q, q.Prime → q * q < c.1 + c.2.1 → q ∈ sp.take c.2.2.1) :
    blockFilter c = (List.range' c.1 c.2.1).filter (fun n => decide n.Prime) := by
  unfold blockFilter spProd
  apply List.filter_congr
  intro n hn
  rw [List.mem_range'_1] at hn
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact isP_iff hlo hps hcompl hn.1 hn.2

/-- A prime `q` with `q * q < b * b` is below `b`. -/
theorem lt_of_mul_self_lt {q b : ℕ} (h : q * q < b * b) : q < b := by
  by_contra hge
  have := Nat.mul_self_le_mul_self (Nat.le_of_not_lt hge)
  omega

/-! ## 2. Bootstrap: the low blocks, then completeness of `sp`, then the high blocks -/

/-- Every prime below 48 is in `small`. -/
theorem small_complete (q : ℕ) (hq : q.Prime) (h : q < 48) : q ∈ small := by
  interval_cases q <;> first | decide | (exfalso; norm_num at hq)

theorem low_sound : ∀ c ∈ certsLow,
    blockFilter c = (List.range' c.1 c.2.1).filter (fun n => decide n.Prime) := by
  intro c hc
  have h := List.all_eq_true.mp lowOK_all c hc
  simp [lowOK] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine blockFilter_eq c h1 h2 ?_
  intro q hq hqq
  have hq48 : q < 48 := lt_of_mul_self_lt (by omega)
  rcases h4 q (small_complete q hq hq48) with h | h
  · have h' : (q * q).blt (c.1 + c.2.1) = true := Eq.mpr Nat.blt_eq hqq
    rw [h] at h'
    exact absurd h' Bool.false_ne_true
  · exact h

theorem flatMap_blockFilter {cs : List Cert}
    (h : ∀ c ∈ cs, blockFilter c = (List.range' c.1 c.2.1).filter (fun n => decide n.Prime)) :
    cs.flatMap blockFilter =
      (cs.flatMap (fun c => List.range' c.1 c.2.1)).filter (fun n => decide n.Prime) := by
  rw [List.filter_flatMap]
  exact List.flatMap_congr h

theorem contig_flatMap : ∀ (lo : ℕ) (cs : List Cert), contig lo cs = true →
    lo ≤ blocksEnd lo cs ∧
      cs.flatMap (fun c => List.range' c.1 c.2.1) = List.range' lo (blocksEnd lo cs - lo)
  | lo, [], _ => by simp [blocksEnd]
  | lo, (l, n, k, t) :: cs, h => by
    simp only [contig, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := contig_flatMap (l + n) cs h2
    simp only [blocksEnd, List.flatMap_cons, ih2]
    subst h1
    refine ⟨by omega, ?_⟩
    rw [List.range'_append_1]
    congr 1
    omega

/-- The primes in `[4, 2209)` are `sp` without `2, 3`. -/
theorem primes_4_2209 :
    (List.range' 4 (2209 - 4)).filter (fun n => decide n.Prime) = sp.drop 2 := by
  have hl := contig_flatMap 4 certsLow contig_low
  rw [blocksEnd_low] at hl
  rw [← hl.2, ← flatMap_blockFilter low_sound, low_primes]

/-- Every prime below 2209 is in `sp`. -/
theorem sp_complete (q : ℕ) (hq : q.Prime) (h : q < 2209) : q ∈ sp := by
  by_cases h4 : q < 4
  · have h2 := hq.two_le
    interval_cases q
    · exact two_mem_sp
    · exact three_mem_sp
  · have hmem : q ∈ (List.range' 4 (2209 - 4)).filter (fun n => decide n.Prime) :=
      List.mem_filter.mpr ⟨List.mem_range'_1.mpr ⟨by omega, by omega⟩, by simpa using hq⟩
    rw [primes_4_2209] at hmem
    exact List.mem_of_mem_drop hmem

theorem high_sound : ∀ c ∈ certsHigh,
    blockFilter c = (List.range' c.1 c.2.1).filter (fun n => decide n.Prime) := by
  intro c hc
  have h := List.all_eq_true.mp highOK_all c hc
  simp only [highOK, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have htake : sp.take c.2.2.1 = sp := List.take_of_length_le (by rw [sp_length]; omega)
  have hb := List.all_eq_true.mp sp_bounds
  simp only [Bool.and_eq_true, Nat.blt_eq] at hb
  refine blockFilter_eq c (by omega) ?_ ?_
  · intro q hq
    rw [htake] at hq
    have := hb q hq
    exact ⟨this.1, by omega⟩
  · intro q hq hqq
    rw [htake]
    exact sp_complete q hq (lt_of_mul_self_lt (by omega))

/-! ## 3. The blocks tile the range; a successful run is a fold -/

/-- If the certificate run succeeds, folding `step` over everything the blocks keep gives the
final state. -/
theorem runChecked_fold : ∀ (s : State) (cs : List Cert) (t : State), runChecked s cs = some t →
    (cs.flatMap blockFilter).foldl step s = t
  | s, [], t, h => by
    simp only [runChecked, Option.some.injEq] at h
    simp [h]
  | s, c :: cs, t, h => by
    unfold runChecked at h
    split at h
    · next hc =>
      rw [List.flatMap_cons, List.foldl_append, hc]
      exact runChecked_fold _ cs t h
    · simp at h

theorem range'_join {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    List.range' a (b - a) ++ List.range' b (c - b) = List.range' a (c - a) := by
  have := @List.range'_append_1 a (b - a) (c - b)
  rwa [show a + (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at this

/-- All blocks together keep exactly the primes in `[4, 3666582)`, in order. -/
theorem certs_flat :
    certs.flatMap blockFilter = (List.range' 4 (3666582 - 4)).filter (fun n => decide n.Prime) := by
  have hl := contig_flatMap 4 certsLow contig_low
  have hh := contig_flatMap 2209 certsHigh contig_high
  rw [blocksEnd_low] at hl
  rw [blocksEnd_high] at hh
  rw [certs_split, List.flatMap_append, flatMap_blockFilter low_sound,
    flatMap_blockFilter high_sound, hl.2, hh.2, ← List.filter_append,
    range'_join (a := 4) (b := 2209) (c := 3666582) (by omega) (by omega)]

/-! ## 4. The fold computes the upstream sum -/

/-- The upstream sum, with `primeGap` unfolded: `a m = partialScore m` for `m ≥ 2`. -/
noncomputable def partialScore (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 2 m,
    (((Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1) : ℕ) : ℤ) -
      ((Nat.nth Nat.Prime (k - 1) - Nat.nth Nat.Prime (k - 1 - 1) : ℕ) : ℤ)).sign

theorem foldl_step_count : ∀ (xs : List ℕ) (s : State),
    (xs.foldl step s).2.2.2 = s.2.2.2 + xs.length
  | [], s => by simp
  | x :: xs, s => by
    rw [List.foldl_cons, foldl_step_count xs]
    simp only [step, List.length_cons]
    omega

theorem fold_primes (m : ℕ) :
    ((List.range' 2 m).map (Nat.nth Nat.Prime)).foldl step
        (Nat.nth Nat.Prime 0, Nat.nth Nat.Prime 1, 0, 2) =
      (Nat.nth Nat.Prime m, Nat.nth Nat.Prime (m + 1), partialScore (m + 1), m + 2) := by
  induction m with
  | zero => simp [partialScore]
  | succ m ih =>
    rw [List.range'_concat, List.map_append, List.foldl_append, ih]
    have e : 2 + 1 * m = m + 1 + 1 := by omega
    have hS : partialScore (m + 1 + 1) = partialScore (m + 1) +
        ((((Nat.nth Nat.Prime (m + 1 + 1) - Nat.nth Nat.Prime (m + 1) : ℕ) : ℤ) -
          ((Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m : ℕ) : ℤ)).sign) := by
      unfold partialScore
      rw [Finset.sum_Icc_succ_top (a := 2) (b := m + 1) (by omega)]
      simp
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    rw [e, hS]

/-! ### The list of primes below `N` -/

/-- The list of `x < N` with `p x`, in increasing order. -/
def filterRange (p : ℕ → Prop) [DecidablePred p] (N : ℕ) : List ℕ :=
  (List.range N).filter (fun x => decide (p x))

theorem count_eq_length_filterRange (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    Nat.count p N = (filterRange p N).length := by
  induction N with
  | zero => simp [filterRange]
  | succ N ih =>
    rw [Nat.count_succ, ih]
    unfold filterRange
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases h : p N <;> simp [h]

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
    have hget : (filterRange p (N + 1))[i] =
        (filterRange p N ++ (if p N then [N] else []))[i] := by
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

theorem filterRange_split (M : ℕ) :
    filterRange Nat.Prime (4 + M) = [2, 3] ++ (List.range' 4 M).filter (fun n => decide n.Prime) := by
  unfold filterRange
  rw [List.range_eq_range', ← List.range'_append_1, List.filter_append]
  congr 1

/-- The primes in `[4, 4 + M)` are `p_2, p_3, ...`, in order. -/
theorem primes_from_4 (M : ℕ) :
    (List.range' 4 M).filter (fun n => decide n.Prime) =
      (List.range' 2 ((List.range' 4 M).filter (fun n => decide n.Prime)).length).map
        (Nat.nth Nat.Prime) := by
  generalize hLp : (List.range' 4 M).filter (fun n => decide n.Prime) = Lp
  have hsplit := filterRange_split M
  rw [hLp] at hsplit
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range']
  have hi : 2 + 1 * i < (filterRange Nat.Prime (4 + M)).length := by
    rw [hsplit]; simp; omega
  rw [nth_eq_getElem_filterRange Nat.Prime (4 + M) (2 + 1 * i) hi]
  have h3 : (filterRange Nat.Prime (4 + M))[2 + 1 * i]? = Lp[i]? := by
    rw [hsplit, show 2 + 1 * i = i + 1 + 1 by omega]
    simp
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem h1] at h3
  exact (Option.some.inj h3).symm

/-- **Generic soundness of the fold.** If folding `step` over the primes in `[4, 4 + M)` from
`(2, 3, 0, 2)` gives `t`, then the score component of `t` is the upstream sum up to `t`'s count − 1. -/
theorem score_of_fold (M : ℕ) (t : State)
    (h : ((List.range' 4 M).filter (fun n => decide n.Prime)).foldl step (2, 3, 0, 2) = t) :
    t.2.2.1 = partialScore (t.2.2.2 - 1) := by
  have hL := primes_from_4 M
  generalize hLp : (List.range' 4 M).filter (fun n => decide n.Prime) = Lp at h hL
  have hf := fold_primes Lp.length
  rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, ← hL, h] at hf
  subst hf
  simp

/-! ## 5. The result -/

/-- **The kernel computation, interpreted:** the upstream sum up to `n = 261150` is `1`. -/
theorem partialScore_261150 : partialScore 261150 = 1 := by
  have h := runChecked_fold _ _ _ certs_ok
  rw [certs_flat] at h
  have := score_of_fold _ _ h
  exact this.symm

end OeisA92243
