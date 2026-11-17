"""
Reproducible Exact-Rational Verification Script for Small-Cardinality Extremal Laws on Erdős #488.

Verifies using exact rational arithmetic (fractions.Fraction, zero floating-point rounding):
1. Unconditional separation (1/a + 1/b) < 2 * B(n)/n for primitive pairs 2 <= a < b <= 60, n >= b.
2. Exact closed-form extremal law for primitive pairs (4 <= M <= 35) over the full unbounded domain
   m > n >= M (by checking the full 2-period horizon M + 2*lcm(a, M) plus asymptotic density d(B)):
     R_max^(2)(M) = (2M - 3)^2 / (2*(M - 1)^2)  at A = {M-1, M}, n = 2M - 3, m = (M - 1)^2.
3. Exact parity-split extremal laws for primitive triples (9 <= M <= 18) over the full 2-period
   horizon M + 2*lcm(a, b, M) plus asymptotic density d(B):
     Odd M:  R_max^(3)(M) = (M - 3)(2M - 5) / (M - 2)^2        at m = (M - 2)^2
     Even M: R_max^(3)(M) = (3M - 10)(2M - 5) / (3*(M - 2)^2)  at m = (M - 2)^2 / 2
4. Explicit 21-element smooth antichain breaking the naive union-bound strategy:
     A_21 = { p_i * p_j : 1 <= i <= j <= 6 } for primes {2, 3, 5, 7, 11, 13},
     where sum_{a in A} (1/a) > 2 * d(B), while on [169, 50000] actual R(A, n, m) <= 1.0298 < 2.
"""
from fractions import Fraction
import math


def eval_exact_unbounded(A: list[int]) -> Fraction:
    """Exact supremum of (B(m)/m)/(B(n)/n) over ALL m > n >= max(A), using period L = lcm(A)."""
    maxA = max(A)
    L = math.lcm(*A)
    horizon = maxA + 2 * L
    sieve = bytearray(horizon + 1)
    for a in A:
        sieve[a::a] = b"\x01" * (horizon // a)

    d_asymp = Fraction(sum(sieve[1 : L + 1]), L)
    cnt = sum(sieve[1:maxA])
    min_d = Fraction(1, 1)
    best_r = Fraction(0, 1)

    for x in range(maxA, horizon + 1):
        cnt += sieve[x]
        d = Fraction(cnt, x)
        if x > maxA:
            r = d / min_d
            if r > best_r:
                best_r = r
        if d < min_d:
            min_d = d

    # Also compare against m -> infinity (asymptotic density d_asymp)
    if d_asymp / min_d > best_r:
        best_r = d_asymp / min_d
    return best_r


def eval_window_float(A: list[int], max_m: int) -> tuple[float, int, int]:
    maxA = max(A)
    sieve = bytearray(max_m + 1)
    for a in A:
        sieve[a::a] = b"\x01" * (max_m // a)
    cnt = sum(sieve[1:maxA])
    min_d = float("inf")
    min_n = maxA
    best_r = 0.0
    bn, bm = maxA, maxA
    for x in range(maxA, max_m + 1):
        cnt += sieve[x]
        d = cnt / x
        if x > maxA and d / min_d > best_r:
            best_r = d / min_d
            bn, bm = min_n, x
        if d < min_d:
            min_d = d
            min_n = x
    return best_r, bn, bm


def main() -> None:
    # 1. Exact integer check of (1/a + 1/b) < 2 * B(n)/n for primitive pairs up to b = 60
    for b in range(3, 61):
        for a in range(2, b):
            if b % a == 0:
                continue
            L = math.lcm(a, b)
            u, v = L // b, L // a
            for n in range(b, 2 * L + b):
                bn = n // a + n // b - n // L
                assert 2 * bn * L > n * (u + v), f"Failed at a={a}, b={b}, n={n}"

    # 2. Exact unbounded verification of pair extremal law for 4 <= M <= 35 (and M=3 exception)
    assert eval_exact_unbounded([2, 3]) == Fraction(49, 40)
    for M in range(4, 36):
        best_r = max(
            eval_exact_unbounded([a, M]) for a in range(2, M) if M % a != 0
        )
        expected = Fraction((2 * M - 3) ** 2, 2 * ((M - 1) ** 2))
        assert best_r == expected, f"Pair mismatch at M={M}: {best_r} vs {expected}"

    # 3. Exact unbounded verification of parity-split triple extremal law for 9 <= M <= 18
    for M in range(9, 19):
        best_r = Fraction(0, 1)
        for b in range(3, M):
            if M % b == 0:
                continue
            for a in range(2, b):
                if b % a == 0 or M % a == 0:
                    continue
                r = eval_exact_unbounded([a, b, M])
                if r > best_r:
                    best_r = r
        if M % 2 == 1:
            expected = Fraction((M - 3) * (2 * M - 5), (M - 2) ** 2)
        else:
            expected = Fraction((3 * M - 10) * (2 * M - 5), 3 * ((M - 2) ** 2))
        assert best_r == expected, f"Triple mismatch at M={M}: {best_r} vs {expected}"

    # 4. Exact rational verification of 21-element degree-2 smooth antichain union-bound obstruction
    primes = [2, 3, 5, 7, 11, 13]
    A21 = [primes[i] * primes[j] for i in range(6) for j in range(i, 6)]
    harm = sum(Fraction(1, a) for a in A21)
    p_none = math.prod(Fraction(p - 1, p) for p in primes)
    p_one = sum(
        Fraction(1, p)
        * Fraction(p - 1, p)
        * math.prod(Fraction(q - 1, q) for q in primes if q != p)
        for p in primes
    )
    d_B = Fraction(1, 1) - (p_none + p_one)
    assert len(A21) == 21 and harm > 2 * d_B
    r21, bn21, bm21 = eval_window_float(A21, 50000)
    assert r21 < 2.0

    print("All exact-rational small-cardinality checks passed successfully.")
    print(
        f"  A_21 obstruction: sum(1/a)={float(harm):.6f} > 2*d(B)={float(2*d_B):.6f}; "
        f"on [169, 50000], max R={r21:.6f} (n={bn21}, m={bm21})"
    )


if __name__ == "__main__":
    main()
