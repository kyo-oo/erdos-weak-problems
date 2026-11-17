# -*- coding: utf-8 -*-
"""OFFICIAL DeepMind FunSearch cap_set DATA loader (W72-142C).

Provenance (see ../../../../OFFICIAL_PROVENANCE.md):
  source repo : github.com/google-deepmind/funsearch (fresh clone 2026-11-17)
  source path : cap_set/n8_size512.txt
  commit      : cc53f274237d7ab05c19df939edbc1f9616a7c19 (HEAD at clone)
  license     : Apache-2.0 (see funsearch/LICENSE in the clone)

The data file holds the official FunSearch cap-set artifact for n=8: 512
rows, one Python-literal list of 8 ints in {0,1,2} per line. This module is
new glue code (the notebook itself never reloads the artifact); it loads the
file byte-faithfully from the fresh clone and exposes it as an int32
ndarray of shape (512, 8). No value is transformed.
"""

import ast
import os

import numpy as np

_DATA_REL = os.path.join("funsearch", "cap_set", "n8_size512.txt")
_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, "..", "..", ".."))
DEFAULT_PATH = os.path.join(_REPO_ROOT, _DATA_REL)


def load_n8_size512(path: str = DEFAULT_PATH) -> np.ndarray:
    """Returns the official n=8 size-512 cap set as an int32 array (512, 8).

    The file is parsed exactly as published: one Python-literal list per
    line, 512 lines, each with 8 entries in {0, 1, 2}.
    """
    with open(path, encoding="utf-8") as f:
        rows = [ast.literal_eval(line.strip()) for line in f if line.strip()]
    arr = np.array(rows, dtype=np.int32)
    if arr.shape != (512, 8):
        raise ValueError(f"n8_size512.txt: expected (512, 8), got {arr.shape}")
    if not np.all((arr >= 0) & (arr <= 2)):
        raise ValueError("n8_size512.txt: entries outside {0,1,2}")
    return arr
