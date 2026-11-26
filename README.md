# Exact ally and adversary reconstruction numbers of two cliques joined by a partial matching

**Research preprint v0.5 — AI-assisted, machine-checked, not peer reviewed.**
Human authorship/attribution and independent review remain pending. Repository ownership is not an authorship claim.

## Result

Let F(c,c,b) consist of two disjoint cliques of order c joined by a matching of size b. For c >= 4, 2 <= b < c, and s = c-b:

- Ally reconstruction number: min(b+2,s+3) when s >= 2; max(5,c) when s = 1.
- Adversary reconstruction number: c+2.
- Exact criterion for blocked subdecks: the multiplicity pair (a,d) is componentwise at most one of (2(s+1),0), (0,2(b+1)), or (b,s+1).

The exceptional case c=3,b=2 is checked separately by finite enumeration (ally=4, adversary=5); it is not covered by the general Lean theorem. This is not a solution of the general graph reconstruction conjecture.

## Files

- [Manuscript PDF](manuscript.pdf), [LaTeX source](manuscript.tex)
- [Lean formalization](Profiles.lean), [verification log](verification.log)
- [Literature comparison](PRIOR_ART.md)
- [C++ exhaustive verifier](verify.cpp), [results](results.csv), [enumeration log](enumeration.log)
- [Independent Python/NetworkX verifier](verify_small.py), [results](small_results.txt)

## Reproduce

With Lean 4.28.0 installed (see lean-toolchain), run:

```sh
lean -o Profiles.olean Profiles.lean
```

On Windows, this was run using the official Lean 4.28.0 release. The source has 2,300 physical lines and 114 theorem declarations, with exit code zero, no admitted declarations, and only the standard Lean axioms propext, Classical.choice, and Quot.sound in the final theorem dependency lists. Six linter warnings concern unused variables/simp arguments. A separate Linux rebuild and rerun of both enumeration programs are documented in [the reproducibility audit](REPRODUCIBILITY_AUDIT.md). The source SHA-256 is:

`7776a7b0e763a44700d3d81530fb675dbb70a3113168c3bd4785108c28f9e546`

The public-facing theorem declarations in namespace CliqueMatching include canonical_deck, identifying_subdeck_iff, exact_ally_reconstruction_number, and exact_adversary_reconstruction_number. These use graph isomorphism and quantify over arbitrary finite simple graphs.

```sh
g++ -O3 -std=c++17 verify.cpp -o verify
./verify 9
python -m pip install networkx==3.5
python verify_small.py
```

The C++ verification covers 28 parameter pairs and 2,330,176 labeled extensions (including duplicate representations). This replicates 21 published ally/adversary pairs through c = 8 and extends the computational check to seven pairs at c = 9. The Python graph-isomorphism check covers six small pairs. The source is included; large generated binaries and the Lean installation are excluded.

## Prior work and limitations

The graph family and earlier lower bounds are due to Harary and Plantholt (1985) and [McMullen and Radziszowski (2007)](https://www.cs.rit.edu/~spr/PUBL/paper52.pdf#page=8). The 2007 mixed competitor supplies the adversary lower bound c + 2. [Rivshin and Radziszowski (2009), §2 and Table 5](https://www.cs.rit.edu/~spr/PUBL/paper59.pdf#page=6), already reported both exact numbers for all 21 cases through c = 8 and called out the c + 2 adversary pattern. Sathiyabama and Monikandan, *Discrete Mathematics* 349 (2026), 114881, DOI [10.1016/j.disc.2025.114881](https://doi.org/10.1016/j.disc.2025.114881), Theorem 9 and Corollary 10, give lower bounds for a construction containing this entire family. The complete article was examined. Some of their numerical lower bounds already attain our exact value; our contribution in those cases is the matching upper bound. The contribution here is the general proofs of both exact formulas, including the adversary upper bound, and the full blocker criterion, not discovery of the adversary pattern or the finite numbers. See PRIOR_ART.md and Section 7 of the manuscript.

Targeted public literature and GitHub searches did not reveal an earlier general proof of the two formulas or the full blocker criterion, but do not prove absolute priority. This is an AI-assisted research draft, not an accepted paper. AI assistance was used extensively in discovery, proof development, formalization, verification, and writing. Independent human review and authorship responsibility are required before journal submission. The supplied third-party publisher PDF is not distributed here.
