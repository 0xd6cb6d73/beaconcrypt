import BeaconcryptCore.Computational.RawCtxSelectedParentTable

/-!
Public HKDF projections use the same retained predecessor response and the entire prior lookup, including earlier comparison responses. Masking only the predecessor's second32 projection removes its unavailable next-chain coordinate. Its first32 key and final12 nonce remain the original coordinates; every other address uses the unchanged prior lookup. These equations identify direct exposure, not a small-probability guess or a security property of public HKDF. The later freshness gate must exclude direct ancestor disclosure. All retained context is private; snapshots and persistence are outside this experiment.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentPublic
open RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

noncomputable def reply (prior : Prior) (entry : Entry) (target : RootOutput)
    (query : JointKdfViewQuery) : JointKdfViewSpec.Range query :=
  if query.address = entry.address then projected entry target query.projection
  else query.project (prior query.address)

/-- Every public projection is of the exact same retained full response. -/
theorem table (prior : Prior) (entry : Entry) (target : RootOutput) (query : JointKdfViewQuery) :
    reply prior entry target query = query.project (lookup prior entry target query.address) := by
  by_cases same : query.address = entry.address <;>
    simp [reply, lookup, JointKdfViewQuery.project, same, projection_parts]

/-- Before direct exposure the complete public reply is independent of the retained second32 coordinate. -/
theorem before (prior : Prior) (entry : Entry) (left right : RootOutput)
    (query : JointKdfViewQuery) (safe : publicExposure entry query = false) :
    reply prior entry left query = reply prior entry right query := by
  rcases query with ⟨input, domain, projection⟩
  cases projection <;> simp_all [publicExposure, reply, projected]

/-- Direct predecessor second32 exposure returns the actual unavailable chain bytes. -/
theorem exposed (prior : Prior) (entry : Entry) (target : RootOutput)
    (query : JointKdfViewQuery) (hit : publicExposure entry query = true) :
    (reply prior entry target query).toList = target.toList := by
  rcases query with ⟨input, domain, projection⟩
  cases projection <;> simp_all [publicExposure, reply, projected]
  rfl

end BeaconcryptCore.Computational.RawCtxSelectedParentPublic

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPublic.table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPublic.table

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPublic.before' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPublic.before

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPublic.exposed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPublic.exposed
