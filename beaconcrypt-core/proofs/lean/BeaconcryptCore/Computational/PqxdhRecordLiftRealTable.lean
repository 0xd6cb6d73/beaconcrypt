-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable

/-! Deterministic native full76 responses populate private coordinate annotations. Callback erasure uses complete table extension and stored-output facts, never independent keys or a public random-HKDF replacement. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftRealTable
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable
open PqxdhFullSecretInputKdf PqxdhSecretInputKdf PqxdhRefinement PqxdhJointKdfGame
variable {Slot Context : Type}

/-- The exact complete receive callback erases under any persistent extension containing its returned full76 output. -/
theorem receive_store (seeds : Seeds Slot) (before after : Table Slot) (mono : before ≤ after)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (present : PendingPresent before pending) (output : FullOutput)
    (found : after pending.request = some output) :
    RawCtxInterpretedReceive.normalResume (erasePending seeds before pending)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)) =
      eraseEffect seeds after (RawCtxChainReceive.normalResume pending
        (advance pending.request 1, pending.request)) := by
  rw [← PqxdhRecordLiftMaterialTable.pending_mono seeds before after mono pending present,
    RawCtxFreshChainCut.decoded_parts,
    ← successor_chain seeds after pending.request
      (available_mono before after mono pending.request present.1.2) output found]
  have stored : material after pending.request =
      RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output) := by
    simp only [material, found]
    rfl
  rw [← stored, erasePending, eraseEffect, RawCtxInterpretedReceive.normalResume_map (material after) _
      (chain seeds after (advance pending.request 1), pending.request),
    RawCtxChainReceive.normalResume_native (chain seeds after) (chain seeds after)
      pending (advance pending.request 1, pending.request)]

def request (seeds : Seeds Slot) (table : Table Slot) (coordinate : Label Slot) :
    SymmetricRatchetKdfRequest := RawCtxChainSend.nativeRequest (chain seeds table coordinate)

def output (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (table : Table Slot) (coordinate : Label Slot) : FullOutput :=
  PqxdhJointKdf.productionStream source.crypto (RawCtxKdfRequestTable.address (request seeds table coordinate))

/-- Stored full outputs are exactly the deterministic native result at their currently interpreted predecessor input. -/
def Consistent (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot) (table : Table Slot) : Prop :=
  ∀ coordinate value, table coordinate = some value → value = output source seeds table coordinate

/-- A real callback records its actual deterministic output, including when the coordinate was already present. -/
def record [DecidableEq Slot] (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (table : Table Slot) (coordinate : Label Slot) : Table Slot :=
  table.cacheQuery coordinate (output source seeds table coordinate)

/-- Coordinate cache hits agree with the repeated native call by consistency; they require no key-distinctness condition. -/
theorem record_mono [DecidableEq Slot] (source : FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (table : Table Slot) (consistent : Consistent source seeds table)
    (coordinate : Label Slot) : table ≤ record source seeds table coordinate := by
  intro prior value found
  by_cases same : prior = coordinate
  · subst prior
    simp only [record, QueryCache.cacheQuery_self, consistent coordinate value found]
  · exact (QueryCache.cacheQuery_of_ne table _ same).trans found

/-- Available input bytes and their deterministic native response survive extension of the private coordinate table. -/
theorem output_mono (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (before after : Table Slot) (mono : before ≤ after) (coordinate : Label Slot)
    (available : Available before coordinate) :
    output source seeds after coordinate = output source seeds before coordinate := by
  simp only [output, request, chain_mono seeds before after mono coordinate available]

/-- The real response invariant is derived again after recording, with no distinct-coordinate or distinct-key condition. -/
theorem consistent_record [DecidableEq Slot] (source : FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (table : Table Slot) (consistent : Consistent source seeds table)
    (closed : Closed table) (coordinate : Label Slot) (available : Available table coordinate) :
    Consistent source seeds (record source seeds table coordinate) := by
  intro prior value found
  by_cases same : prior = coordinate
  · subst prior
    have returned : value = output source seeds table coordinate := by
      simpa only [record, QueryCache.cacheQuery_self, Option.some.injEq] using found.symm
    exact returned.trans (output_mono source seeds table _ (record_mono source seeds table consistent coordinate)
      coordinate available).symm
  · have old : table prior = some value :=
      (QueryCache.cacheQuery_of_ne table _ same).symm.trans found
    exact (consistent prior value old).trans (output_mono source seeds table _
      (record_mono source seeds table consistent coordinate) prior (closed prior value old)).symm

/-- The predecessor domain remains closed after a real callback, whether it is a first call or a retry. -/
theorem closed_record [DecidableEq Slot] (source : FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (table : Table Slot) (consistent : Consistent source seeds table)
    (closed : Closed table) (coordinate : Label Slot) (available : Available table coordinate) :
    Closed (record source seeds table coordinate) := by
  intro prior value found
  by_cases same : prior = coordinate
  · subst prior
    exact available_mono table _ (record_mono source seeds table consistent coordinate) coordinate available
  · exact available_mono table _ (record_mono source seeds table consistent coordinate) prior
      (closed prior value ((QueryCache.cacheQuery_of_ne table _ same).symm.trans found))

/-- Empty annotations satisfy real functional consistency without a key-distribution hypothesis. -/
theorem consistent_empty (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot) :
    Consistent source seeds (∅ : Table Slot) := by
  simp [Consistent]

/-- The typed output used by the callback is exactly the unchanged native full76 response. -/
theorem output_source (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (table : Table Slot) (coordinate : Label Slot) :
    RawCtxKdfRequestTable.fullResponse (output source seeds table coordinate) =
      RawCtxSourceHkdf.response source.crypto (request seeds table coordinate) :=
  RawCtxKdfRequestTable.fullResponse_source source (request seeds table coordinate)

/-- Distinct labels whose interpreted native requests alias obtain equal real full76 outputs. -/
theorem output_alias (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (table : Table Slot) (left right : Label Slot)
    (same : request seeds table left = request seeds table right) :
    output source seeds table left = output source seeds table right := by
  simp only [output, same]

/-- The complete source send callback erases under arbitrary persistent storage of its full76 reply. -/
theorem send_store (seeds : Seeds Slot) (before after : Table Slot) (mono : before ≤ after)
    (pending : RawCtxChainSend.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (available : SendAvailable before pending) (present : SlotsPresent before pending.entry.receive_slots)
    (value : FullOutput) (found : after pending.request = some value) :
    RawCtxInterpretedSend.resume (eraseSendPending seeds before pending)
      (ok (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse value))) =
      ok (eraseSeal seeds after (RawCtxChainSend.ready pending (advance pending.request 1, pending.request))) := by
  rw [← PqxdhRecordLiftMaterialTable.send_pending_mono seeds before after mono pending available present,
    RawCtxFreshChainCut.decoded_parts,
    ← successor_chain seeds after pending.request
      (available_mono before after mono pending.request available.2) value found]
  have stored : material after pending.request =
      RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material value) := by
    simp only [material, found]
    rfl
  rw [← stored]
  rfl

/-- Retain all 76 native reply bytes as one correlated output. -/
def fromResponse (reply : RatchetKdfResponse) : FullOutput :=
  ⟨absBytes reply.bytes, by simp only [absBytes, List.length_map]; have length := reply.bytes.property; scalar_tac⟩

/-- Abstracting a typed full76 reply loses no byte. -/
theorem from_fullResponse (value : FullOutput) :
    fromResponse (RawCtxKdfRequestTable.fullResponse value) = value := by
  apply Subtype.ext
  exact RawCtxKdfRequestTable.fullResponse_bytes value

/-- Native reply reconstruction preserves the entire typed response. -/
theorem fullResponse_from (reply : RatchetKdfResponse) :
    RawCtxKdfRequestTable.fullResponse (fromResponse reply) = reply := by
  have bytes : absBytes (RawCtxKdfRequestTable.fullResponse (fromResponse reply)).bytes = absBytes reply.bytes :=
    RawCtxKdfRequestTable.fullResponse_bytes (fromResponse reply)
  have arrays := Subtype.ext ((absBytes_inj_iff _ _).mp bytes)
  exact congrArg RatchetKdfResponse.mk arrays

/-- Every logical callback makes its actual native KDF query, including cache hits and failed-opening retries. The returned bytes are then cached privately. -/
noncomputable def callback [DecidableEq Slot] (seeds : Seeds Slot) (coordinate : Label Slot) :
    StateT (Table Slot) (OracleComp RawCtxSharedPrimitive.KdfSpec) FullOutput := fun table => do
  let reply ← RawCtxSharedPrimitive.KdfSpec.query (request seeds table coordinate)
  let value := fromResponse reply
  pure (value, table.cacheQuery coordinate value)

/-- Exactly one native KDF query is present for every callback, regardless of whether its coordinate is cached. -/
theorem callback_bound [DecidableEq Slot] (seeds : Seeds Slot) (table : Table Slot) (coordinate : Label Slot) :
    ((callback seeds coordinate).run table).IsQueryBoundP (fun _ => True) 1 := by
  simp [callback, StateT.run]

/-- Actual deterministic source KDF interpretation preserves the entire supplied native poststate and returns the real coordinate update. -/
theorem callback_real [DecidableEq Slot] {PrimitiveState : Type}
    (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot) (table : Table Slot) (coordinate : Label Slot)
    (native : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT PrimitiveState ProbComp))
    (before after : PrimitiveState)
    (actual : (native (request seeds table coordinate)).run before =
      pure (RawCtxSourceHkdf.response source.crypto (request seeds table coordinate), after)) :
    (simulateQ native ((callback seeds coordinate).run table)).run before =
      pure ((output source seeds table coordinate, record source seeds table coordinate), after) := by
  simp only [callback, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  change ((native (request seeds table coordinate)).run before >>= fun result =>
    pure ((fromResponse result.1, table.cacheQuery coordinate (fromResponse result.1)), result.2)) = _
  rw [actual, pure_bind, ← output_source, from_fullResponse]
  rfl

/-- Recording a real result establishes every operational lookup obligation, with no probabilistic or security premise. -/
theorem record_facts [DecidableEq Slot] (source : FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (table : Table Slot) (consistent : Consistent source seeds table)
    (closed : Closed table) (coordinate : Label Slot) (available : Available table coordinate) :
    table ≤ record source seeds table coordinate ∧
      (record source seeds table coordinate) coordinate = some (output source seeds table coordinate) ∧
      Closed (record source seeds table coordinate) ∧
      Consistent source seeds (record source seeds table coordinate) :=
  ⟨record_mono source seeds table consistent coordinate, QueryCache.cacheQuery_self _ _ _,
    closed_record source seeds table consistent closed coordinate available,
    consistent_record source seeds table consistent closed coordinate available⟩

/-- The literal real full76 receive response realizes the entire source callback under the recorded interpretation. -/
theorem receive_real [DecidableEq Slot] (source : FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (table : Table Slot) (consistent : Consistent source seeds table)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (present : PendingPresent table pending) :
    RawCtxInterpretedReceive.normalResume (erasePending seeds table pending)
      (RawCtxInterpretedReceive.decodeResponse
        (RawCtxSourceHkdf.response source.crypto (request seeds table pending.request))) =
      eraseEffect seeds (record source seeds table pending.request)
        (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request)) := by
  rw [← output_source]
  exact receive_store seeds table _ (record_mono source seeds table consistent pending.request)
    pending present _ (QueryCache.cacheQuery_self _ _ _)

/-- Real send likewise preserves both chains, the full skip cache, and same-output key/nonce correlations. -/
theorem send_real [DecidableEq Slot] (source : FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (table : Table Slot) (consistent : Consistent source seeds table)
    (pending : RawCtxChainSend.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (available : SendAvailable table pending) (present : SlotsPresent table pending.entry.receive_slots) :
    RawCtxInterpretedSend.resume (eraseSendPending seeds table pending)
      (ok (RawCtxInterpretedReceive.decodeResponse
        (RawCtxSourceHkdf.response source.crypto (request seeds table pending.request)))) =
      ok (eraseSeal seeds (record source seeds table pending.request)
        (RawCtxChainSend.ready pending (advance pending.request 1, pending.request))) := by
  rw [← output_source]
  exact send_store seeds table _ (record_mono source seeds table consistent pending.request)
    pending available present _ (QueryCache.cacheQuery_self _ _ _)

end BeaconcryptCore.Computational.PqxdhRecordLiftRealTable

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.receive_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.receive_store
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.record_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.record_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.output_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.output_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.consistent_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.consistent_record
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.closed_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.closed_record
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.consistent_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.consistent_empty
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.output_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.output_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.output_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.output_alias
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.send_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.send_store
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.from_fullResponse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.from_fullResponse
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.fullResponse_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.fullResponse_from
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.callback_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.callback_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.callback_real
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.record_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.record_facts
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.receive_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.receive_real
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.send_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftRealTable.send_real
