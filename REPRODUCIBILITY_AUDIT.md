# Reproducibility audit for v0.5

The proof and both enumeration programs are unchanged from source commit `091b67ba72748efe682b435123ff2bbf19c54468`. The following checks were performed on Linux, separately from the original Windows checks.

| Check | Result |
|---|---|
| SHA-256 of `Profiles.lean` | `7776a7b0e763a44700d3d81530fb675dbb70a3113168c3bd4785108c28f9e546` |
| Official Lean 4.28.0, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` | Clean build exit 0; four public statements each use only `propext`, `Classical.choice`, and `Quot.sound` |
| C++17 enumeration with upper parameter 9 | Output exactly matches `results.csv`: 28 parameter pairs, 2,330,176 labeled extensions, 1,581 subdecks, 276 classified extensions |
| Python with NetworkX 3.5 | Output exactly matches `small_results.txt` for the six pairs tested |
| Separate check of exceptional pair | Comparison with all 156 unlabeled six-vertex graphs in the NetworkX graph atlas confirms ally 4 and adversary 5, with maximal feasible blocker profiles (2, 2) and (4, 0) |

The Lean check covers the family for `c >= 4`. The exceptional case `(c,b) = (3,2)` is supported separately by computation and is not covered by the Lean theorem. The 2009 benchmark comparison is a literature check, not a claim of peer review or absolute priority.

To rerun the packaged programs, follow the commands in the [README](README.md).
