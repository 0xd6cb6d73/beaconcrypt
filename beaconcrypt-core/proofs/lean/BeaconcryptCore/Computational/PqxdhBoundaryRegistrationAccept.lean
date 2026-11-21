-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentNative
import BeaconcryptCore.Computational.PqxdhHeadlineBridges
import BeaconcryptCore.Computational.PqxdhRegistrationAdmission
import BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint

/-! PB-03 raw registration admission: actual ordered verification and core validation, unchanged native root interpreter, complete optional token and CE state. The public Rust adapter control remains reviewed transcription; local extracted validation equations are explicit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept
open PqxdhServerRootPreparation PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhJointGapDh (ScalarBytes)
open PqxdhBeaconPhase2Preparation (Word32 Bytes)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-- The actual nine-callback verification schedule, ending at the parser block matched to the extracted validator by B10. Raw candidate bytes and every optional reply remain arbitrary. -/
def verification {Reader E Shared : Type} (raw : Bytes) :
    OracleComp (Spec Reader E Shared) (Option (Verified Reader)) := do
  let reader ← (Spec Reader E Shared).query (.decode raw)
  match reader with
  | none => pure none
  | some reader =>
    let encoded ← (Spec Reader E Shared).query (.identity reader)
    match encoded with
    | none => pure none
    | some encoded =>
      match parseIdentity encoded with
      | none => pure none
      | some identity =>
        let valid ← (Spec Reader E Shared).query (.identityPoint identity)
        if !valid then pure none else do
          let pqSigned ← (Spec Reader E Shared).query (.pqField reader)
          match pqSigned with
          | none => pure none
          | some pqSigned =>
            let pqPayload ← (Spec Reader E Shared).query (.verify identity pqSigned)
            match pqPayload with
            | none => pure none
            | some pqPayload =>
              let preSigned ← (Spec Reader E Shared).query (.preField reader)
              match preSigned with
              | none => pure none
              | some preSigned =>
                let prePayload ← (Spec Reader E Shared).query (.verify identity preSigned)
                match prePayload with
                | none => pure none
                | some prePayload =>
                  let oneSigned ← (Spec Reader E Shared).query (.oneField reader)
                  match oneSigned with
                  | none => pure none
                  | some oneSigned =>
                    let onePayload ← (Spec Reader E Shared).query (.verify identity oneSigned)
                    match onePayload with
                    | none => pure none
                    | some onePayload =>
                      pure ((fun fields => ⟨reader, ⟨encoded, preSigned, oneSigned, pqSigned⟩,
                        fields.1, fields.2⟩) <$>
                        PqxdhHeadlineBridges.parsedBytes encoded prePayload onePayload pqPayload)

/-- Moving the final pure validation block to the extracted-validator bridge changes neither a callback nor the complete verified candidate. -/
theorem verification_source {E Shared : Type} (raw : Pqxdh.Bytes) :
    verification (Reader := Reader) (E := E) (Shared := Shared) raw = verifyInput raw := by
  unfold verification verifyInput
  refine bind_congr fun reader => ?_
  cases reader <;> try rfl
  refine bind_congr fun encoded => ?_
  cases encoded with
  | none => rfl
  | some encoded =>
      cases parsed : parseIdentity encoded <;> simp only [parsed]
      simp [PqxdhHeadlineBridges.parsedBytes, parsed]
      rfl

/-- On arbitrary verified payload bytes, the final parser block accepts exactly an extracted bundle with those bytes and the same typed result. Wrong widths have no representing bundle. -/
theorem validated_fields (identity prekey oneTime pq : Bytes)
    (fields : Ed25519PublicKey × Phase1KeyTuple) :
    PqxdhHeadlineBridges.parsedBytes identity prekey oneTime pq = some fields ↔
      ∃ (input : pqxdh.InitKex) (valid : pqxdh.VerifiedInitKex),
        absBytes input.identity_key = identity ∧ absBytes input.prekey = prekey ∧
        absBytes input.one_time_key = oneTime ∧ absBytes input.pq_key = pq ∧
        pqxdh.validate_init_kex input = ok (.Ok valid) ∧
        PqxdhHeadlineBridges.typedVerified valid = fields :=
  PqxdhHeadlineBridges.validate_init_bridge.2.1 identity prekey oneTime pq fields

/-- The ID tested by collectVerified is precisely the extracted core registration ID. This is a core equation, not the Rust debug assertion. -/
theorem registration_id (value : Verified Reader) :
    ∃ rid : pqxdh.RegistrationId,
      pqxdh.registration_id (PqxdhProtocolAcceptance.verified value.identity value.keys) = ok rid ∧
      absBytes rid.bytes = registrationId value := by
  simpa only [Pqxdh.ValidInit.rid, PqxdhProtocolAcceptance.verified,
    PqxdhRootTableInitialization.rootArray_bytes, registrationId] using
    registration_id_abs (PqxdhProtocolAcceptance.verified value.identity value.keys)

/-- Registration status, reservation, point admission, ephemeral/KEM generation, conversion and all four DH callbacks follow the actual verified candidate in source order. -/
def collection {E Shared : Type} (raw : Bytes) :
    OracleComp (PqxdhServerRootPreparation.Spec Reader E Shared) (Option (Inputs Reader E Shared)) := do
  let verified ← verification raw
  match verified with
  | none => pure none
  | some verified => collectVerified verified

/-- The whole ordered prefix is identical before any interpreter, including all early rejection and ambient generation effects. -/
theorem collection_source {E Shared : Type} (raw : Bytes) :
    collection (Reader := Reader) (E := E) (Shared := Shared) raw = collect raw := by
  simp only [collection, collect, verification_source]
  rfl

/-- The original native callback interpreter: codec checks, actual ephemeral/KEM work and joint identity DH, with the reached consumed-ID list. -/
noncomputable def preparation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Bytes) :
    StateT (List Bytes) ProbComp (Option (Inputs Reader ScalarBytes Word32)) :=
  simulateQ (PqxdhServerStaticDhSource.nativeImpl setup.joint seed (serverAux setup codec checks)
    (fun _ => pure ())) (collection raw)

/-- Native prefix equality retains the complete source result and consumed state; no assumed successful or honest candidate. -/
theorem prefix_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Bytes) :
    preparation setup codec checks seed raw = nativePrefix setup codec checks seed raw := by
  simp only [preparation, nativePrefix, collection_source]

/-- Raw adapter acceptance with exact attempt indexing and token publication. The source root client, its approved request interpreter, complete caches and consumption timing remain unchanged. -/
noncomputable def rawAccept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Bytes) : NativeGame KemSK (Option Nat) := do
  let state ← nativeGet
  let index := state.sessions
  let collected ← nativeCoins ((preparation setup codec checks seed raw).run state.server.consumed)
  nativeSet { state with sessions := index + 1, server := { state.server with consumed := collected.2 } }
  match collected.1 with
  | none => pure none
  | some input => do
      let returned ← nativeClient setup.hmac index state.server.control
        (binding setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)) input
      match returned with
      | .ok (some token) => do
          nativeModify fun current => { current with pending := Function.update current.pending index (some token) }
          pure (some index)
      | _ => pure none

/-- Complete program equality: every attempt advances its ghost ordinal, and only the actual successful root client publishes its actual token. -/
theorem accept_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Bytes) :
    rawAccept setup codec checks seed scalar raw = nativeAccept setup codec checks seed scalar raw := by
  simp only [rawAccept, nativeAccept, prefix_native]
  rfl

/-- The adapter operation in the common experiment, using its original scalar observation parameter and all native and CE bookkeeping fields. -/
noncomputable def deploymentAccept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Bytes) :
    StateT (PqxdhDeploymentNative.State KemSK) ProbComp (Option Nat) :=
  PqxdhDeploymentNative.onNative (PqxdhRegistrationSchedule.onShared
    (rawAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw))

/-- The CE accept command is exactly the source adapter operation; routing parameters do not replace or select the raw candidate. -/
theorem deployment_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (raw : Bytes) :
    PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.accept raw)) =
      deploymentAccept setup codec checks seed raw := by
  simp only [PqxdhDeploymentNative.handler, PqxdhRegistrationSchedule.handler,
    deploymentAccept, accept_native]

/-- Any continuation receives the actual optional handle and entire reinstalled CE state, including both caches, pending tokens, all owners, counters, traces and ghost fields. -/
theorem accept_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (raw : Bytes)
    (state : PqxdhDeploymentNative.State KemSK)
    (next : Option Nat × PqxdhDeploymentNative.State KemSK → ProbComp X) :
    ((PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.accept raw))).run state >>= next) =
      ((rawAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run
        state.native.shared >>= fun result => next (result.1,
          { state with native := { state.native with shared := result.2 } })) := by
  simp only [deployment_accept, deploymentAccept, PqxdhDeploymentNative.onNative,
    PqxdhRegistrationSchedule.onShared, StateT.run, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]

/-- These are source callback caps, before interpreting each callback: nine verification slots, thirteen admitted-collection slots, and twenty-two total. Primitive generation, KEM and other ambient work remain inside their unchanged callbacks. -/
theorem source_callback_caps {E Shared : Type} (raw : Bytes) (value : Verified Reader) :
    (verification (Reader := Reader) (E := E) (Shared := Shared) raw).IsTotalQueryBound 9 ∧
    (collectVerified (E := E) (Shared := Shared) value).IsTotalQueryBound 13 ∧
    (collection (Reader := Reader) (E := E) (Shared := Shared) raw).IsTotalQueryBound 22 := by
  simpa only [verification_source, collection_source] using
    And.intro (verifyInput_bound (Reader := Reader) (E := E) (Shared := Shared) raw)
      (And.intro (collectVerified_bound (E := E) (Shared := Shared) value)
        (collect_bound (Reader := Reader) (E := E) (Shared := Shared) raw))

/-- Rejection retains the consumed list; success appends exactly the returned token's fresh core registration ID. The original full native output and state remain the support premise. -/
theorem accept_consumption (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Bytes)
    (state : NativeState KemSK) (result : Option Nat × NativeState KemSK)
    (supported : result ∈ support ((rawAccept setup codec checks seed scalar raw).run state)) :
    (result.1 = none ∧ result.2.2.server.consumed = state.2.server.consumed) ∨
      ∃ index token, result.1 = some index ∧ result.2.2.pending index = some token ∧
        absBytes token.pending.registration_id.bytes ∉ state.2.server.consumed ∧
        result.2.2.server.consumed = state.2.server.consumed ++ [absBytes token.pending.registration_id.bytes] := by
  exact PqxdhRegistrationAdmission.native_accept_consumed setup codec checks seed scalar raw state result
    (by simpa only [accept_native] using supported)

/-- Exact attempt index, unchanged Server peer map and identity ID, and pending-token success/rejection footprint. No current pending token is lost on a failed attempt. -/
theorem accept_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Bytes)
    (state : NativeState KemSK) (result : Option Nat × NativeState KemSK)
    (supported : result ∈ support ((rawAccept setup codec checks seed scalar raw).run state)) :
    result.2.2.server.server = state.2.server.server ∧
      result.2.2.server.identityKeyId = state.2.server.identityKeyId ∧
      result.2.2.sessions = state.2.sessions + 1 ∧
      (∀ session, session ≠ state.2.sessions → result.2.2.pending session = state.2.pending session) ∧
      (result.1 = none → result.2.2.pending = state.2.pending) ∧
      (∀ session, result.1 = some session → session = state.2.sessions ∧ ∃ token,
        result.2.2.pending session = some token ∧
        PqxdhDeploymentCompile.identityOf codec raw = some token.pending.beacon_identity_public_key) := by
  exact PqxdhDeploymentCompileFootprint.accept_footprint setup codec checks
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) raw state.2 (result.1, result.2.2)
    (evaluate_support setup seed scalar _ state result (by
      rw [PqxdhServerAuthNative.accept_native]
      simpa only [accept_native, StateT.run] using supported))

/-- Once raw verification has produced this actual typed candidate, a consumed identity/one-time pair rejects before reservation, generation, encapsulation, conversion or DH. This does not skip earlier verification work. -/
theorem collect_replay (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (value : Verified Reader) (consumed : List Bytes)
    (used : registrationId value ∈ consumed) :
    (simulateQ (PqxdhServerStaticDhSource.nativeImpl setup.joint seed (serverAux setup codec checks)
      (fun _ => pure ())) (collectVerified value)).run consumed = pure (none, consumed) := by
  simp only [collectVerified, OptionT.run_bind, OptionT.run_monadLift, Option.elimM,
    bind_map_left, simulateQ_bind, simulateQ_spec_query, PqxdhServerStaticDhSource.nativeImpl,
    serverAux, StateT.run, PqxdhRegistrationAdmission.state_bind, pure_bind, used, ite_true,
    Option.elim_some, OptionT.run_failure, simulateQ_pure]
  rfl

end BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.verification_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.verification_source

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.validated_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.validated_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.registration_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.registration_id

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.collection_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.collection_source

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.prefix_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.prefix_native

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.accept_native

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.deployment_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.deployment_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.accept_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.accept_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.source_callback_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.source_callback_caps

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.accept_consumption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.accept_consumption

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.accept_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.accept_footprint

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.collect_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept.collect_replay
