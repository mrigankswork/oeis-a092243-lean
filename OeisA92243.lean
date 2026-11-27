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

public import OeisA92243.Bridge

/-!
# OEIS A092243, conjecture 1: kernel-only proof (library root)

* `OeisA92243/Compute.lean`: computable definitions (core Lean only).
* `OeisA92243/Certs/*.lean`, `OeisA92243/Certs.lean`: the certificate, one `decide +kernel` theorem
  per block, composed into `OeisA92243.certs_ok`.
* `OeisA92243/Checks.lean`: small kernel checks (side conditions, tiling, low primes).
* `OeisA92243/Bridge.lean`: soundness, ending in `OeisA92243.partialScore_261150`.
* `Challenge.lean` / `Solution.lean` (separate libraries): the upstream statement, and its proof.

The previous version, which used `native_decide`, is at git tag `v0.1`.
-/
