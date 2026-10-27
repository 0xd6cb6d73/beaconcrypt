import BeaconcryptCore.Computational.RawCtxFreshChainCut

/-!
The predecessor request retains one exact full76 response. Its material coordinates and request address are private coupling provenance; the unavailable second32 coordinate reconstructs that same response on every retry and public projection. A matching public second32 view is direct ancestor-output exposure even when its input differs from the selected chain. First32 and final12 views retain their actual coordinates.

This bookkeeping does not resurrect a disposed native secret or add a live reveal capability. Structural target-independence does not establish a reached uniform cut, exclude byte-value aliases or erase earlier authorized knowledge. Source KDF/library equations and complete local work remain explicit. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentEntry
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

structure Entry where
  address : JointKdfAddress
  material : Material

noncomputable def realize (entry : Entry) (target : RootOutput) : FullOutput :=
  materialChainEquiv.symm (entry.material, target)

def fromOutput (address : JointKdfAddress) (output : FullOutput) : Entry :=
  ⟨address, material output⟩

/-- The retained predecessor entry reconstructs the same complete response, not a new chain or nonce draw. -/
theorem realize_fromOutput (address : JointKdfAddress) (output : FullOutput) :
    realize (fromOutput address output) (nextChain output) = output :=
  materialChainEquiv.symm_apply_apply output

/-- The hidden second32 coordinate and both retained material coordinates are projections of one full response. -/
theorem parts (entry : Entry) (target : RootOutput) :
    (material (realize entry target), nextChain (realize entry target)) = (entry.material, target) :=
  materialChainEquiv.apply_symm_apply (entry.material, target)

def projected (entry : Entry) (target : RootOutput) :
    (projection : JointKdfProjection) → List.Vector UInt8 projection.width
  | .first32 => entry.material.1
  | .second32 => target
  | .final12 => entry.material.2

/-- Each actual public projection has its exact stored coordinate; only second32 contains the unavailable next chain. -/
theorem projection_parts (entry : Entry) (target : RootOutput) (projection : JointKdfProjection) :
    projection.project (realize entry target) = projected entry target projection := by
  cases projection with
  | first32 => exact congrArg (fun pair => pair.1.1) (parts entry target)
  | second32 => exact congrArg Prod.snd (parts entry target)
  | final12 => exact congrArg (fun pair => pair.1.2) (parts entry target)

/-- Retrying the predecessor derivation returns the same chain/material pair and cannot draw another next chain. -/
theorem decoded_response (entry : Entry) (target : RootOutput) :
    RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse (realize entry target)) =
      (RawCtxFreshChainCut.concreteChain target, RawCtxFreshChainCut.concreteMaterial entry.material) := by
  rw [RawCtxFreshChainCut.decoded_parts]
  exact congrArg (fun pair => (RawCtxFreshChainCut.concreteChain pair.2,
    RawCtxFreshChainCut.concreteMaterial pair.1)) (parts entry target)

noncomputable def publicReply (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (target : RootOutput) (query : JointKdfViewQuery) : JointKdfViewSpec.Range query :=
  if query.address = entry.address then projected entry target query.projection
  else query.project (productionStream source.crypto query.address)

def publicExposure (entry : Entry) (query : JointKdfViewQuery) : Bool :=
  decide (query.address = entry.address ∧ query.projection = .second32)

/-- The public response is a projection of the same retained predecessor entry, and all other addresses remain the actual source. -/
theorem public_table (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (target : RootOutput) (query : JointKdfViewQuery) :
    publicReply source entry target query =
      if query.address = entry.address then query.project (realize entry target)
      else query.project (productionStream source.crypto query.address) := by
  simp only [publicReply, JointKdfViewQuery.project, projection_parts]

/-- Before an actual matching second32 projection, the public reply cannot depend on the retained hidden chain. -/
theorem public_before (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (left right : RootOutput) (query : JointKdfViewQuery) (safe : publicExposure entry query = false) :
    publicReply source entry left query = publicReply source entry right query := by
  rcases query with ⟨input, domain, projection⟩
  cases projection <;> simp_all [publicExposure, publicReply, projected]

/-- A matching predecessor second32 request returns the actual selected chain bytes, even though its input need not equal those bytes. -/
theorem public_exposed (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (target : RootOutput) (query : JointKdfViewQuery) (exposed : publicExposure entry query = true) :
    (publicReply source entry target query).toList = target.toList := by
  rcases query with ⟨input, domain, projection⟩
  cases projection <;> simp_all [publicExposure, publicReply, projected]
  rfl

/-- Retaining an actual predecessor output agrees with the original fixed public function on every address and projection. -/
theorem public_source (source : FixedHkdfSha512NoSaltSource) (address : JointKdfAddress)
    (query : JointKdfViewQuery) :
    publicReply source (fromOutput address (productionStream source.crypto address))
      (nextChain (productionStream source.crypto address)) query =
        query.project (productionStream source.crypto query.address) := by
  rw [public_table, realize_fromOutput]
  by_cases same : query.address = address <;> simp [fromOutput, same]

noncomputable def stream (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (target : RootOutput) (address : JointKdfAddress) : FullOutput :=
  if address = entry.address then realize entry target else productionStream source.crypto address

noncomputable def nativeStep (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (target : RootOutput) (chain : RatchetChain) : RatchetChain × RatchetMaterial :=
  RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
    (stream source entry target (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain))))

noncomputable def labelStep (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (challenge : RatchetKdfResponse) : RawCtxSelectedChain.Slot → RawCtxSelectedChain.Slot × RatchetMaterial
  | .hidden => RawCtxSelectedChain.step source challenge .hidden
  | .known chain =>
      if RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) = entry.address then
        (.hidden, RawCtxFreshChainCut.concreteMaterial entry.material)
      else RawCtxSelectedChain.step source challenge (.known chain)

/-- The retained predecessor returns the unavailable marker on retries; interpretation recovers the complete same-table source response, including target/predecessor cycles. -/
theorem step_table (source : FixedHkdfSha512NoSaltSource) (entry : Entry)
    (target : RootOutput) (slot : RawCtxSelectedChain.Slot) :
    nativeStep source entry target (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain target) slot) =
      Prod.map (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain target)) id
        (labelStep source entry (RawCtxKdfRequestTable.fullResponse
          (stream source entry target (RawCtxKdfRequestTable.address
            (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))) slot) := by
  cases slot <;> simp only [nativeStep, labelStep, RawCtxSelectedChain.interpret, RawCtxSelectedChain.step, Prod.map, id_eq]
  split_ifs <;> simp_all [stream, decoded_response, RawCtxKdfRequestTable.fullResponse_source]

/-- Retaining the original predecessor response changes no complete source value, even when another request aliases its address. -/
theorem stream_source (source : FixedHkdfSha512NoSaltSource) (address request : JointKdfAddress) :
    stream source (fromOutput address (productionStream source.crypto address))
      (nextChain (productionStream source.crypto address)) request = productionStream source.crypto request := by
  by_cases same : request = address <;> simp [stream, fromOutput, same]
  exact realize_fromOutput address (productionStream source.crypto address)

end BeaconcryptCore.Computational.RawCtxSelectedParentEntry

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.realize_fromOutput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.realize_fromOutput

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.parts

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.projection_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.projection_parts

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.decoded_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.decoded_response

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.public_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.public_table

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.public_before' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.public_before

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.public_exposed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.public_exposed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.public_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.public_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.step_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.step_table

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentEntry.stream_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentEntry.stream_source
