# OEIS A092243, conjecture 1: a Lean 4 proof

**Statement** ([formal-conjectures](https://github.com/google-deepmind/formal-conjectures) `FormalConjectures/OEIS/92243.lean`,
theorem `OeisA92243.conjecture1`, tagged `research open` at commit `9097e2f`):

```lean
theorem conjecture1 : ∃ n > 250000, a n > 0
```

`a n` is the prime-gap "tug of war" score of [OEIS A092243](https://oeis.org/A092243). It starts at 0. At stage k ≥ 2 it
goes up by 1 if the k-th prime gap is larger than the previous gap, down by 1 if it is smaller, and stays the same if they are
equal. The OEIS entry asks: *"Is s > 0 for some n > 250000?"* (up to n = 250000 the score is "overwhelmingly negative").

**Answer: yes.** `a 261150 = 1`; this is the first n > 250000 with a positive score (`a 261149 = 0`).

This repository contains `OeisA92243.lean`, a machine-checked proof of the exact upstream statement.

## What is (and is not) new
- The numerical fact is **not new**. N. J. A. Sloane's table linked from the OEIS entry,
  [a092243_1.txt](https://oeis.org/A092243/a092243_1.txt) (n = 1..965562), already shows a(261150) = 1.
- What this repository adds is a **formal proof** of the formal-conjectures statement, which was still tagged
  `research open`. As of 2026-11-26 we found no other machine-checked proof of it.

## How the proof works
The file **imports** the upstream module `FormalConjectures.OEIS.«92243»` instead of copying its definitions, so `a` and
`primeGap` are exactly upstream's. An in-file audit compares the proved theorem's type with upstream `conjecture1`'s type
using `Expr ==` and fails the build on any mismatch.

1. `count_eq_length_filterRange`: `Nat.count p N` is the length of `(List.range N).filter p`.
2. `count_getElem_filterRange`: the i-th element q of that list has `Nat.count p q = i`.
3. `nth_eq_getElem_filterRange`: hence, by Mathlib's `Nat.nth_count`, `Nat.nth p i` is the i-th element of the list. This turns
   the noncomputable `Nat.nth Nat.Prime` into a computable list of the primes below 3666582
   (p₂₆₁₁₅₀ = 3666581, with primes counted from 0).
4. `a_eq_scoreC`: `a 261150` equals a computable sum over an array of those primes. Proved in the kernel.
5. Two concrete facts are evaluated with `native_decide`: `261150 < primesL.length` and `0 < scoreC 261150`.

## Axioms
```
'OeisA92243.conjecture1_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OeisA92243.len_primesL._native.native_decide.ax_1_1,
 OeisA92243.scoreC_pos._native.native_decide.ax_1_1]
```
**The last two are `native_decide` axioms.** They trust the Lean compiler for the two computations in step 5. Everything else
is checked by Lean's kernel. There is no `sorry`, no custom axiom, and no `implemented_by`/`unsafe`.

## Verification
- Lean: `./verify.sh` clones formal-conjectures at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (Lean 4.33.1 and its
  pinned Mathlib), builds the upstream module unchanged, and compiles the proof. The compile step takes about 45 s.
- Independent numerical checks, exact integers: `python3 checks/check1.py 270000` (Python sieve) and
  `cc -O2 -o check2 checks/check2.c && ./check2` (C sieve) both give
  a(261149) = 0 and a(261150) = 1. Both agree with Sloane's table. An independent reviewer also matched all 965,562 rows of the
  table with its own code.

## Credits and disclosure
- Sequence: Joseph L. Pe (2002), OEIS A092243. The question and the data table: N. J. A. Sloane (OEIS).
- Formal statement: The Formal Conjectures Authors (google-deepmind/formal-conjectures, Apache-2.0).
- AI disclosure: the Lean proof and the check scripts were written with an AI assistant (Anthropic's Claude, via Claude Code)
  at the direction of the repository owner. They were reviewed by an independent Claude instance and by Google's Gemini; both
  accepted. They have not yet been reviewed by a human expert.

License: Apache-2.0 (see `LICENSE`).
