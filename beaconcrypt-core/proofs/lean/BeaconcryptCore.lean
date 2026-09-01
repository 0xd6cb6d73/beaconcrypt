import BeaconcryptCore.Extraction
import BeaconcryptCore.Refinement.PqxdhSession
import BeaconcryptCore.Refinement.PqxdhCommitment
import BeaconcryptCore.Refinement.RatchetControlRestore
import BeaconcryptCore.Refinement.RatchetEffectRefinement
import BeaconcryptCore.Model.Pqxdh.Instance
import BeaconcryptCore.Model.Pqxdh.InstanceCommit
import BeaconcryptCore.Model.Pqxdh.Acceptance
import BeaconcryptCore.Model.Pqxdh.Runs
import BeaconcryptCore.Computational.CtxReduction
import BeaconcryptCore.Computational.CtxRetainedTagProjection
import BeaconcryptCore.Computational.CtxAuthClassification
import BeaconcryptCore.Computational.CtxRomAuth
import BeaconcryptCore.Computational.CtxPrefixIsolation
import BeaconcryptCore.Computational.CtxSealSampling
import BeaconcryptCore.Computational.CtxTransitionReduction
import BeaconcryptCore.Computational.VCVioFeasibility
import BeaconcryptCore.Verification.ProofObligations

/-!
# Beaconcrypt-core verification root

This is the maintained root of the Lean verification project.

Hax creates this file only when it is absent; subsequent extraction leaves it unchanged.

Keep every handwritten proof family reachable from this module so `import BeaconcryptCore` checks and exposes the complete reviewed proof surface.
-/
