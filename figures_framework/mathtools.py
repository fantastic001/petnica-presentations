from __future__ import annotations

import math

import numpy as np


def normal_pdf(x: np.ndarray, mean: float, deviation: float) -> np.ndarray:
    scale = 1 / (deviation * math.sqrt(2 * math.pi))
    return scale * np.exp(-0.5 * ((x - mean) / deviation) ** 2)


def binomial_pmf(trials: int, probability: float) -> np.ndarray:
    if not 0 <= probability <= 1:
        raise ValueError(f"probability must be in [0,1], got {probability}")
    else:
        return np.array(
            [
                math.comb(trials, k)
                * probability ** k
                * (1 - probability) ** (trials - k)
                for k in range(trials + 1)
            ]
        )


def poisson_pmf(mean: float, values: np.ndarray) -> np.ndarray:
    return np.array(
        [
            math.exp(-mean) * mean ** int(value) / math.factorial(int(value))
            for value in values
        ]
    )


def harmonic_number(size: int) -> float:
    return sum(1 / k for k in range(1, size + 1))


def polynomial_features(x: np.ndarray, degree: int) -> np.ndarray:
    return np.vander(x, degree + 1, increasing=True)


def fit_polynomial(
    x: np.ndarray,
    y: np.ndarray,
    degree: int,
    regularization: float = 1e-8,
) -> np.ndarray:
    features = polynomial_features(x, degree)
    identity = np.eye(degree + 1)
    return np.linalg.solve(
        features.T @ features + regularization * identity, features.T @ y
    )


def logarithmic_sample(size: int, count: int = 1500) -> np.ndarray:
    if size <= 0:
        raise ValueError(f"size must be positive, got {size}")
    else:
        return np.unique(
            np.logspace(0, math.log10(size), count).astype(int)
        )
