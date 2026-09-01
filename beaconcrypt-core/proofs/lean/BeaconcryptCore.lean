import BeaconcryptCore.Extraction
import BeaconcryptCore.Refinement.RatchetControlRestore
import BeaconcryptCore.Refinement.RatchetEffectRefinement
import BeaconcryptCore.Verification.ProofObligations

/-!
# Beaconcrypt-core verification root

This is the maintained root of the Lean verification project.

Hax creates this file only when it is absent; subsequent extraction leaves it unchanged.

Keep every handwritten proof family reachable from this module so `import BeaconcryptCore` checks and exposes the complete reviewed proof surface.
-/
