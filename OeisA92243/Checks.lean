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
module

public import OeisA92243.Certs

/-!
# Small kernel checks on the certificate

These are the finite facts the soundness proof (`OeisA92243/Bridge.lean`) needs about the
certificate data: side conditions of every block, that the blocks tile `[4, 3666582)`, and that
the 14 low blocks find exactly the primes of `sp` above 3. Each check is a separate small
`decide +kernel` (a few MB of kernel memory each).

Side conditions. For a block `[lo, hi)` sieved with the list `ps = sp.take k`, the soundness lemma
`OeisA92243.isP_iff` needs: `2 ≤ lo`; every `q ∈ ps` satisfies `0 < q < lo`; and every prime `q` with
`q * q < hi` lies in `ps`.
* Low blocks (`hi ≤ 2304 = 48²`): such a `q` is a prime below 48, i.e. in `small`; `lowOK` checks
  that every `q ∈ small` with `q * q < hi` is in `ps`.
* High blocks (`k = 329`, so `ps = sp`; `2209 ≤ lo`, `hi ≤ 2209²`): such a `q` is a prime below 2209,
  and those are all in `sp` because the low blocks found them.
-/

@[expose] public section

namespace OeisA92243

/-- The 15 primes below 48. (That these are all of them is proved in `Bridge.lean`.) -/
def small : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

/-- Side conditions for a low block (see the module docstring). -/
def lowOK (c : Cert) : Bool :=
  Nat.ble 2 c.1 && (sp.take c.2.2.1).all (fun q => Nat.blt 0 q && Nat.blt q c.1) &&
    Nat.ble (c.1 + c.2.1) 2304 &&
    small.all (fun q => !(Nat.blt (q * q) (c.1 + c.2.1)) || (sp.take c.2.2.1).contains q)

/-- Side conditions for a high block (see the module docstring). -/
def highOK (c : Cert) : Bool :=
  Nat.ble 2209 c.1 && Nat.beq c.2.2.1 329 && Nat.ble (c.1 + c.2.1) 4879681

theorem lowOK_all : certsLow.all lowOK = true := by decide +kernel
theorem highOK_all : certsHigh.all highOK = true := by decide +kernel
theorem contig_low : contig 4 certsLow = true := by decide +kernel
theorem blocksEnd_low : blocksEnd 4 certsLow = 2209 := by decide +kernel
theorem contig_high : contig 2209 certsHigh = true := by decide +kernel
theorem blocksEnd_high : blocksEnd 2209 certsHigh = 3666582 := by decide +kernel
/-- The kernel sieves `[4, 2209)` again: the primes found are exactly `sp` without `2, 3`. -/
theorem low_primes : certsLow.flatMap blockFilter = sp.drop 2 := by decide +kernel
theorem sp_bounds : sp.all (fun q => Nat.blt 0 q && Nat.blt q 2209) = true := by decide +kernel
theorem sp_length : sp.length = 329 := by decide +kernel
theorem two_mem_sp : 2 ∈ sp := by decide +kernel
theorem three_mem_sp : 3 ∈ sp := by decide +kernel

end OeisA92243

end
