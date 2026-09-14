import BeaconcryptCore.Computational.RawCtxSelectedInitialEntry
import BeaconcryptCore.Computational.RawCtxSelectedChain
import BeaconcryptCore.Computational.RawCtxKdfRequestTable

/-!
One initial first32 coordinate is omitted from the retained full76 entry, while its other directional chain and optional analysis nonce remain present. The full retained lookup preserves every prior address. Both actual initial64 and subsequent76 derivations use the same ratchet domain: a known private input equal to the initializer root therefore reconstructs the selected first32 as material, and must not be declared target-free. The explicit initializerQuery flag identifies this case for separate ancestor/alias accounting. Only full76 comparison bookkeeping uses the nonce; no actual64 initializer nonce is invented.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedInitialTable
open RawCtxSelectedInitialEntry RawCtxSelectedChain
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev Prior := JointKdfAddress → FullOutput

noncomputable def lookup (prior : Prior) (entry : Entry) (target : RootOutput)
    (address : JointKdfAddress) : FullOutput :=
  if address = entry.address then realize entry target else prior address

noncomputable def nativeStep (prior : Prior) (entry : Entry) (target : RootOutput)
    (chain : RatchetChain) : RatchetChain × RatchetMaterial :=
  RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
    (lookup prior entry target (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain))))

noncomputable def step (prior : Prior) (entry : Entry) (target : RootOutput)
    (challenge : RatchetKdfResponse) : Slot → Slot × RatchetMaterial
  | .hidden => let decoded := RawCtxInterpretedReceive.decodeResponse challenge
      (.known decoded.1, decoded.2)
  | .known chain => let decoded := nativeStep prior entry target chain
      (.known decoded.1, decoded.2)

/-- The complete same-table KDF response commutes with the selected-chain representation, including retries of the initializer address. -/
theorem step_table (prior : Prior) (entry : Entry) (target : RootOutput) (slot : Slot) :
    nativeStep prior entry target (interpret (RawCtxFreshChainCut.concreteChain target) slot) =
      Prod.map (interpret (RawCtxFreshChainCut.concreteChain target)) id
        (step prior entry target (RawCtxKdfRequestTable.fullResponse
          (lookup prior entry target (RawCtxKdfRequestTable.address
            (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))) slot) := by
  cases slot <;> rfl

def initializerQuery (entry : Entry) : Slot → Bool
  | .hidden => false
  | .known chain => decide (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) = entry.address)

/-- Only outside an actual known initializer-address request is this label KDF step independent of the hidden first32 coordinate. -/
theorem step_before (prior : Prior) (entry : Entry) (left right : RootOutput)
    (challenge : RatchetKdfResponse) (slot : Slot) (safe : initializerQuery entry slot = false) :
    step prior entry left challenge slot = step prior entry right challenge slot := by
  cases slot with
  | hidden => rfl
  | known chain => simp_all [initializerQuery, step, nativeStep, lookup]

/-- An original source entry reconstructs every real fixed-HKDF response, with the same shared ratchet domain. -/
theorem lookup_source (source : FixedHkdfSha512NoSaltSource) (address request : JointKdfAddress) :
    lookup (productionStream source.crypto) (fromOutput address (productionStream source.crypto address))
      (JointKdfProjection.first32.project (productionStream source.crypto address)) request =
      productionStream source.crypto request := by
  simp only [lookup, realize_fromOutput]
  split <;> simp_all [fromOutput]

noncomputable def view (fallback : Prior) (cache : RawCtxKdfRequestTable.Table) : Prior :=
  fun address => (cache address).getD (fallback address)

/-- A recorded full76 comparison output retains every previous cache/fallback response while separating only first32. -/
theorem view_recorded (fallback : Prior) (cache : RawCtxKdfRequestTable.Table)
    (address request : JointKdfAddress) (output : FullOutput) :
    view fallback (cache.cacheQuery address output) request =
      lookup (view fallback cache) (fromOutput address output)
        (JointKdfProjection.first32.project output) request := by
  simp only [lookup, realize_fromOutput]
  by_cases same : request = address <;> simp [view, fromOutput, same, QueryCache.cacheQuery_of_ne]
  subst request
  simp

noncomputable def publicReply (prior : Prior) (entry : Entry) (target : RootOutput)
    (query : JointKdfViewQuery) : JointKdfViewSpec.Range query :=
  if query.address = entry.address then projected entry target query.projection
  else query.project (prior query.address)

/-- Public projections select their exact coordinate of the same retained full76 response. -/
theorem public_table (prior : Prior) (entry : Entry) (target : RootOutput) (query : JointKdfViewQuery) :
    publicReply prior entry target query = query.project (lookup prior entry target query.address) := by
  by_cases same : query.address = entry.address <;>
    simp [publicReply, lookup, JointKdfViewQuery.project, same, projection_parts]

/-- Public projections outside first32 at the initializer address retain the full prior lookup and do not read the selected coordinate. -/
theorem public_before (prior : Prior) (entry : Entry) (left right : RootOutput)
    (query : JointKdfViewQuery) (safe : publicExposure entry query = false) :
    publicReply prior entry left query = publicReply prior entry right query := by
  rcases query with ⟨input, domain, projection⟩
  cases projection <;> simp_all [publicExposure, publicReply, projected]

/-- Direct public first32 exposure returns the actual selected initial-chain bytes. -/
theorem public_exposed (prior : Prior) (entry : Entry) (target : RootOutput)
    (query : JointKdfViewQuery) (hit : publicExposure entry query = true) :
    (publicReply prior entry target query).toList = target.toList := by
  rcases query with ⟨input, domain, projection⟩
  cases projection <;> simp_all [publicExposure, publicReply, projected]
  rfl

end BeaconcryptCore.Computational.RawCtxSelectedInitialTable

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialTable.step_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialTable.step_table

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialTable.step_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialTable.step_before

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialTable.lookup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialTable.lookup_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialTable.view_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialTable.view_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialTable.public_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialTable.public_table

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialTable.public_before' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialTable.public_before

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialTable.public_exposed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialTable.public_exposed
