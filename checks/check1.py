# Independent check #1 (Python, simple Eratosthenes sieve). Follows the upstream Lean definitions literally:
# p_i = i-th prime, 0-indexed (p_0 = 2); primeGap k = p_k - p_{k-1} (ℕ, with k-1 truncated at 0);
# a(n) = 0 if n <= 1 else sum_{k=2}^{n} sign(primeGap k - primeGap (k-1)).
import sys
N = int(sys.argv[1]); B = 4_000_000
sieve = bytearray([1]) * B; sieve[0] = sieve[1] = 0
for i in range(2, int(B**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(range(i*i, B, i)))
P = [i for i in range(B) if sieve[i]]
assert len(P) > N + 1
def gap(k): return P[k] - P[k-1] if k >= 1 else 0
a = 0; first = None
for k in range(2, N + 1):
    d = gap(k) - gap(k-1); a += (d > 0) - (d < 0)
    if k > 250000 and a > 0 and first is None: first = (k, a, P[k])
    if k == N: print("a(%d) = %d" % (N, a))
print("first n > 250000 with a(n) > 0:", first, "| primes needed up to p_n =", first and P[first[0]])
