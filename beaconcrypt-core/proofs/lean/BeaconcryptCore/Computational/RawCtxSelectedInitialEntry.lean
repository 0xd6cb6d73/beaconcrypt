import BeaconcryptCore.Computational.RawCtxFreshChainCut

/-!
A retained initialization entry omits first32 entirely. Its second32 and final12 coordinates reconstruct the same full76 value when the private selected chain is supplied; initial64 is exactly that value's shared prefix. A matching public first32 projection is direct disclosure. This is private coupling bookkeeping, not an adversary interface or a claim that a reached source output is uniform.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedInitialEntry
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

structure Entry where
  address : JointKdfAddress
  otherChain : RootOutput
  nonce : NonceOutput

noncomputable def realize (entry : Entry) (target : RootOutput) : FullOutput :=
  PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.symm
    (target, entry.otherChain, entry.nonce)

def fromOutput (address : JointKdfAddress) (output : FullOutput) : Entry :=
  ⟨address, JointKdfProjection.second32.project output,
    JointKdfProjection.final12.project output⟩

/-- The same full response is recovered without storing the selected first32 in the entry. -/
theorem realize_fromOutput (address : JointKdfAddress) (output : FullOutput) :
    realize (fromOutput address output) (JointKdfProjection.first32.project output) = output := by
  exact PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.symm_apply_apply output

def projected (entry : Entry) (target : RootOutput) :
    (projection : JointKdfProjection) → List.Vector UInt8 projection.width
  | .first32 => target
  | .second32 => entry.otherChain
  | .final12 => entry.nonce

/-- Each public view selects its exact coordinate from the same reconstructed full response. -/
theorem projection_parts (entry : Entry) (target : RootOutput) (projection : JointKdfProjection) :
    projection.project (realize entry target) = projected entry target projection := by
  cases projection <;> simp [realize, projected]
  all_goals rfl

noncomputable def publicReply (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (target : RootOutput) (query : JointKdfViewQuery) : JointKdfViewSpec.Range query :=
  if query.address = entry.address then projected entry target query.projection
  else query.project (productionStream source.crypto query.address)

def publicExposure (entry : Entry) (query : JointKdfViewQuery) : Bool :=
  decide (query.address = entry.address ∧ query.projection = .first32)

/-- The cached public view keeps the same full76 and the real source at every other address. -/
theorem public_table (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (target : RootOutput) (query : JointKdfViewQuery) :
    publicReply source entry target query =
      if query.address = entry.address then query.project (realize entry target)
      else query.project (productionStream source.crypto query.address) := by
  simp only [publicReply, JointKdfViewQuery.project, projection_parts]

/-- Before matching first32 disclosure, every public reply is independent of the missing initial chain. -/
theorem public_before (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (left right : RootOutput) (query : JointKdfViewQuery) (safe : publicExposure entry query = false) :
    publicReply source entry left query = publicReply source entry right query := by
  rcases query with ⟨input, domain, projection⟩
  cases projection <;> simp_all [publicExposure, publicReply, projected]

/-- A matching first32 view discloses the selected initial chain, although the request input is its root. -/
theorem public_exposed (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (target : RootOutput) (query : JointKdfViewQuery) (exposed : publicExposure entry query = true) :
    (publicReply source entry target query).toList = target.toList := by
  rcases query with ⟨input, domain, projection⟩
  cases projection <;> simp_all [publicExposure, publicReply, projected]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Retaining a real initializer response leaves every public evaluation exactly the fixed source. -/
theorem public_source (source : FixedHkdfSha512NoSaltSource) (address : JointKdfAddress)
    (query : JointKdfViewQuery) :
    publicReply source (fromOutput address (productionStream source.crypto address))
      (JointKdfProjection.first32.project (productionStream source.crypto address)) query =
        query.project (productionStream source.crypto query.address) := by
  rw [public_table, realize_fromOutput]
  by_cases same : query.address = address <;> simp [fromOutput, same]

/-- Initial64 is precisely selected first32 followed by the retained other directional chain. -/
theorem initial_prefix (entry : Entry) (target : RootOutput) :
    initialPrefix (realize entry target) = target ++ entry.otherChain := by
  apply List.Vector.toList_injective
  change (target.toList ++ entry.otherChain.toList ++ entry.nonce.toList).take 64 =
    target.toList ++ entry.otherChain.toList
  simp [List.take_append]

/-- The actual source initializer obtains both directional values from this same ratchet-domain entry. -/
theorem source_initial_chains (source : FixedHkdfSha512NoSaltSource) (input : Pqxdh.Bytes) :
    Pqxdh.rootChains source.crypto input =
      ((JointKdfProjection.first32.project
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address input))).toList,
        (fromOutput (FixedHkdfDomain.ratchet.address input)
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address input))).otherChain.toList) := by
  exact rootChains_eq_initialProjection source.crypto source.prefixConsistent input

end BeaconcryptCore.Computational.RawCtxSelectedInitialEntry

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.realize_fromOutput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.realize_fromOutput

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.projection_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.projection_parts

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.public_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.public_table

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.public_before' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.public_before

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.public_exposed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.public_exposed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.public_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.public_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.initial_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.initial_prefix

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.source_initial_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialEntry.source_initial_chains
