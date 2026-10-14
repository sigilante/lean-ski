#!/usr/bin/env python3
"""Evaluate the load bound of Ski/ZK/SpongeAlign.lean at Plonky3 0.8's sponge.

`loadG_δs_countP` bounds the mean, over a uniform permutation of K states,
of `loadG`, the number of first commitments whose chains reach one index
value.  Divided by the permutation count, its right side reads

    E[loadG] <= G * ( (s0 - 1)
                      + N X^L N^t (S F)^e / ( e! (K - M)^e ffac(s0, t) ) )

with m = pre0.length + 1, M = m + t (L + 1), S = 0 + 1 + ... + (M - 1),
e = t - 1 - (m + 2 L) and ffac(s0, t) = s0 (s0 - 1) ... (s0 - t + 1).
Lean proves it for every t >= 1 and s0; this script picks t and s0 to
minimize it (s0 in closed form for each t, t by a scan).  The parameters are the header's: BabyBear p, width 16, rate
8, so K = p^16 and F = K / p^7 (the capacity tail drops its first
element), N = p^8 blocks for the chain's first block, G = p groups (the
commitment's first element ends the prefix), and later blocks below
X = 9 p^8.  The prefix length is assumed, not derived from the transcript.

Usage: scripts/sponge_load.py [--prefix 16] [L ...]   (default L: 1 3 10 100)
"""
import argparse
from math import lgamma, log, log1p, exp

P = 2013265921  # BabyBear


def log_tail_coeff(L, m, t, lp=log(P)):
    """log A, where the bound's second term is A / ffac(s0, t), or None for e < 0."""
    e = t - 1 - (m + 2 * L)
    if e < 0:
        return None
    K, F, N, X = 16 * lp, 9 * lp, 8 * lp, log(9) + 8 * lp
    M = m + t * (L + 1)
    lKM = K + log1p(-M / P**16)  # log(K - M)
    S = log(M * (M - 1) / 2)
    return N + L * X + t * N + e * (S + F) - lgamma(e + 1) - e * lKM


def log_ffac(s0, t):
    """log of s0 (s0 - 1) ... (s0 - t + 1), by its series in t / s0.

    lgamma(s0 + 1) - lgamma(s0 - t + 1) cancels catastrophically in floating
    point at s0 near 2^60; the series t log s0 + sum log(1 - j/s0) is exact
    to the dropped term, below t^4 / s0^3, which is under 1e-9 here."""
    assert t * t < s0
    return t * log(s0) - t * (t - 1) / (2 * s0) - (t - 1) * t * (2 * t - 1) / (12 * s0 * s0)


def log_bound(L, m, t, lp=log(P)):
    """Natural log of the bound at t, s0 chosen near its optimum, or None.

    For fixed t the bound is G ((s0 - 1) + A / ffac(s0, t)) with ffac about
    s0^t, minimized at s0 = (t A)^(1 / (t + 1)); the value is then evaluated
    with the series for ffac."""
    lA = log_tail_coeff(L, m, t, lp)
    if lA is None:
        return None
    ls0 = (log(t) + lA) / (t + 1)
    s0 = exp(ls0)
    if t * t >= s0:
        return None
    tail = lA - log_ffac(s0, t)
    return lp + log((s0 - 1) + exp(min(tail, 700))), t, s0


def best(L, m, tmax=2_000_000):
    """Minimize over t from the smallest with e >= 0, in steps of about 0.1 percent."""
    out = None
    t = m + 2 * L + 1
    while t < tmax:
        r = log_bound(L, m, t)
        if r is not None and (out is None or r[0] < out[0]):
            out = r
        t += max(1, t // 1000)
    assert out[1] < tmax / 2, "optimum near the search cap"
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefix", type=int, default=16, help="m = pre0.length + 1")
    ap.add_argument("L", type=int, nargs="*", default=[1, 3, 10, 100])
    a = ap.parse_args()
    print(f"prefix m = {a.prefix}, n1 = p^8 = 2^{8 * log(P) / log(2):.1f}")
    print(f"{'L':>4} {'t':>6} {'log2 s0':>8} {'log2 E[loadG]':>14}")
    for L in a.L:
        v, t, s0 = best(L, a.prefix)
        print(f"{L:>4} {t:>6} {log(s0) / log(2):>8.1f} {v / log(2):>14.1f}")


if __name__ == "__main__":
    main()
