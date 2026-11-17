"""
Reproducible Verification Script for Small-Cardinality Extremal Laws on Erdős Problem #488.

Verifies:
1. Unconditional separation (1/a + 1/b) < 2 * B(n)/n for primitive pairs 2 <= a < b <= 60, n >= b.
2. Exact closed-form extremal law for primitive pairs (M >= 4):
     R_max^(2)(M) = (2M - 3)^2 / (2*(M - 1)^2)  at A = {M-1, M}, n = 2M - 3, m = (M - 1)^2.
3. Exact parity-split extremal laws for primitive triples (M >= 9):
     Odd M:  R_max^(3)(M) = (M - 3)(2M - 5) / (M - 2)^2        at m = (M - 2)^2
     Even M: R_max^(3)(M) = (3M - 10)(2M - 5) / (3*(M - 2)^2)  at m = (M - 2)^2 / 2
4. Explicit 21-element smooth antichain breaking the naive union-bound strategy:
     A_21 = { p_i * p_j : 1 <= i <= j <= 6 } for primes {2, 3, 5, 7, 11, 13},
     where sum_{a in A} (1/a) > 2 * d(B), while actual R(A, n, m) remains ~ 1.0298 < 2.
"""
import math


def eval_ratio(A: list[int], max_m: int) -> tuple[float, int, int]:
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
    for b in range(3, 61):
        for a in range(2, b):
            if b % a == 0:
                continue
            L = math.lcm(a, b)
            ub = 1.0 / a + 1.0 / b
            for n in range(b, 2 * L + b):
                bn = n // a + n // b - n // L
                assert 2.0 * bn / n > ub, f"Failed at a={a}, b={b}, n={n}"

    for M in range(4, 41):
        best_r = 0.0
        for a in range(2, M):
            if M % a == 0:
                continue
            r, _, _ = eval_ratio([a, M], 3 * M * M)
            best_r = max(best_r, r)
        expected = ((2 * M - 3) ** 2) / (2 * ((M - 1) ** 2))
        assert abs(best_r - expected) < 1e-12, f"Pair mismatch at M={M}: {best_r} vs {expected}"

    for M in range(9, 21):
        best_r = 0.0
        for b in range(3, M):
            if M % b == 0:
                continue
            for a in range(2, b):
                if b % a == 0 or M % a == 0:
                    continue
                r, _, _ = eval_ratio([a, b, M], M * M * M)
                best_r = max(best_r, r)
        if M % 2 == 1:
            expected = (M - 3) * (2 * M - 5) / ((M - 2) ** 2)
        else:
            expected = (3 * M - 10) * (2 * M - 5) / (3 * ((M - 2) ** 2))
        assert abs(best_r - expected) < 1e-12, f"Triple mismatch at M={M}: {best_r} vs {expected}"

    primes = [2, 3, 5, 7, 11, 13]
    A21 = [primes[i] * primes[j] for i in range(6) for j in range(i, 6)]
    harm = sum(1.0 / a for a in A21)
    p_none = math.prod(1.0 - 1.0 / p for p in primes)
    p_one = sum(
        (1.0 / p) * (1.0 - 1.0 / p) * math.prod(1.0 - 1.0 / q for q in primes if q != p)
        for p in primes
    )
    d_B = 1.0 - (p_none + p_one)
    assert len(A21) == 21 and harm > 2.0 * d_B
    r21, bn21, bm21 = eval_ratio(A21, 50000)
    assert r21 < 2.0

    print("All small-cardinality checks passed successfully.")
    print(f"  A_21 obstruction: sum(1/a)={harm:.6f} > 2*d(B)={2*d_B:.6f}, actual R={r21:.6f} (n={bn21}, m={bm21})")


if __name__ == "__main__":
    main()
