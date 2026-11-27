import Pairing.Contraction

/-!
# Moved to `Pairing.Contraction`

The contraction lemma (sketch §1) is pure matching combinatorics, so it now lives in the core
library as `core/Pairing/Contraction.lean`, with every declaration name unchanged. This module
only re-exports it, so that `import Clifford.Contraction` keeps working. New code should import
`Pairing.Contraction`.
-/
