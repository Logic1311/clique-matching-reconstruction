# Literature comparison — 26 November 2026 (JST)

## Direct comparison with Sathiyabama and Monikandan

S. Sathiyabama and S. Monikandan, *On the reconstruction number of generalized join of graphs*, Discrete Mathematics 349 (2026), 114881. DOI: 10.1016/j.disc.2025.114881. The full article (11 pages) was inspected. Section 5, pp. 7–8, Theorem 9 and Corollary 10 are directly relevant.

Their construction includes our entire family, via base graph K2, k=b, n=s=c-b. Each base vertex is replaced by a clique of size b+1 with b matched endpoints, then the single unmatched vertex is replaced by a clique of size s. The resulting graph is F(c,c,b). Theorem 9 provides rn >= min(b+1,s+2), strictly when b>=s+1. In conjunction with McMullen and Radziszowski's 2007 bound rn>=4, the compared lower bounds are 4 for b=2,s>=2; b+1 for 3<=b<=s; s+3 for b>=s+1,s>=2; and 4 for s=1. Our corresponding exact values are 4, b+2, s+3, and max(5,c). Thus some prior lower bounds already have the correct numerical value. We supply the matching upper bounds, complete blocker criterion, and adversary number; do not claim the original family or existing lower-bound witnesses as new. Section 6 studies restricted class reconstruction numbers, not the unrestricted quantities here. No exact formula or equivalent blocker theorem was located in the supplied full text.

McMullen and Radziszowski (2007), §2.2.4, Theorem 5 and Table 2, provide the earlier lower bound and six computed ally values, and explicitly leave the general exact calculation open. Their construction includes the mixed unbalanced competitor F(c+1,c-1,b). The 2010 survey by Asciak et al. was also checked. The 2026 article's introduction states that Brewster et al. (2012) exclude H_n^k; the 2012 full text has not been inspected. Public arXiv index and GitHub searches did not identify an identical general result, but cannot establish absolute priority.

## Release status

Mathematical manuscript v0.4 and two enumeration checks are complete for the stated domain. The verified Lean source and verification log are included in this package; the proof itself was not changed for the literature revision. The exceptional case c=3,b=2 is checked by finite enumeration, outside the general Lean theorem. The publisher PDF supplied by the user is not part of the research distribution. Human authorship and independent review remain pending. This package does not assert that publication is guaranteed.
