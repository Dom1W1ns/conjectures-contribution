# Partial contribution: Erdős 686, multiplier 25

`script.lean` combines every original Lean proof result found in this research
workspace. The complete result is the **fixed-length k=6 exclusion**. The k=5
case and the all-length question remain unresolved.

| Source | Public results | Scope |
|---|---|---|
| `work/session4/K6.lean` | `k6_exclusion` | Excludes multiplier 25 for all natural n,m with n+6≤m. |
| New `work/publication686/K6RatioBridge.lean` | `k6_ratio_exclusion` | Puts that exclusion directly into the question's rational-ratio form, proving the denominator positive before clearing it. |
| `work/session6/PrimeTransport.lean` | `common_prime_le_width`, `lower_prime_le_width`, `upper_prime_le_width`, `lower_block_not_prime`, `upper_block_not_prime` | Necessary conditions for disjoint blocks; upper-prime transport excludes prime 5, and the nonprimality conclusions require their stated span hypotheses. |
| `work/session9/QuotientBridge.lean` | `centeredFive_product`, `quotient_discriminant`, `centeredFive_to_quotient` | Exact identities and the forward passage from the centered k=5 equation to the sextic square equation, when x≠0. No point completeness or exclusion. |
| `work/session6/GapSquareTransport.lean` | `dvd_shifted_prod_sub_prod`, `square_dvd_of_coprime_product_complement`, `square_dvd_transport_of_coprime_complement` | General commutative-ring divisibility results under the explicit coprimality and exact product-ratio hypotheses. |
| `work/session7/HigherContactCertificate.lean` | `higherContact_monomial_dvd`, `higherContact_remainder_dvd`, `higherContact_certificate_dvd` | General semiring divisibility implications. No instantiated higher-contact certificate, height bound, or arithmetic normalization is asserted. |
| `work/session13/NormRelationBridge.lean` | `five_nsmul`, `relation_injective`, `relation_finrank_le` | Abstract F2-linear algebra: a coefficient-five identity implies joint injectivity and a dimension bound. Ideal class groups and arithmetic correspondences are not instantiated. |

All declarations use `Contribution.Erdos686TwentyFive` or its
`NormRelationBridge` subnamespace. The original six bodies and proofs are
preserved. Their imports are consolidated, the redundant direct Lean tactic
import is omitted because the Mathlib imports supply it, and development-time
`#print` commands are removed from the contribution file. No heartbeat limit
is changed. The additional rational-ratio lemma depends on the existing k=6
theorem rather than duplicating its argument.

`source_manifest.json` records source hashes, all 32 named declarations, and the
classification of all 23 original/export/audit Lean files discovered. The
`K6Audit.lean` and `PrimeTransportAudit.lean` wrappers and all exported copies
match their canonical modules after removing diagnostic print commands; they
contain no additional proof results. The unfinished platform `Challenge.lean`
skeleton is deliberately excluded, as are the Lean runtime and Mathlib sources.
