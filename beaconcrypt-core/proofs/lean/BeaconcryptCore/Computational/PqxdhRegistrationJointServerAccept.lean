-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirthCosts

/-! The full native Server acceptance consumer uses an indexed joint-service prefix. It retains allocation on failed attempts, the actual source consumed list, literal core acceptance/root/clearing and pending-token publication. Its unchanged native root interpreter retains the existing restricted Extract-ROM idealization; no cryptographic hop is claimed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointFinish (State onNative)
open PqxdhServerRootPreparation (Inputs)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Execute the real indexed raw prefix on the current consumed set. Its complete optional result and post-consumed list remain together, and every other native coordinate is retained. -/
def prepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) : StateT (State KemSK) ProbComp
      (Option (Inputs Reader ScalarBytes Word32) × List Pqxdh.Bytes) := fun state =>
  (fun result => ((result.1, result.2.2), (result.2.1, state.2))) <$>
    (simulateQ (PqxdhRegistrationJointServerPrefix.impl setup (serverAux setup codec checks))
      (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run
        (state.1, state.2.2.server.consumed)

/-- Annotated native counterpart: the source seed is used only inside its private interpreter, with the same full shared state and callback order. -/
def sourcePrepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) : StateT (State KemSK) ProbComp
      (Option (Inputs Reader ScalarBytes Word32) × List Pqxdh.Bytes) := fun state =>
  (fun result => ((result.1, result.2.2), (result.2.1, state.2))) <$>
    (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex (serverAux setup codec checks))
      (PqxdhServerRootPreparation.collect raw)).run (state.1, state.2.2.server.consumed)

/-- The original complete post-prefix continuation: every attempt allocates its index, and only a successful literal core/root/clear/consume reply publishes a pending token. -/
noncomputable def tail (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity)
    (state : GameState KemSK) (collected : Option (Inputs Reader ScalarBytes Word32) × List Pqxdh.Bytes) :
    NativeGame KemSK (Option Nat) := do
  let index := state.sessions
  nativeSet { state with sessions := index + 1, server := { state.server with consumed := collected.2 } }
  match collected.1 with
  | none => pure none
  | some input => do
      let returned ← nativeClient setup.hmac index state.server.control
        ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, setup.serverKeyId⟩ input
      match returned with
      | .ok (some token) => do
          nativeModify fun current => { current with pending := Function.update current.pending index (some token) }
          pure (some index)
      | _ => pure none

/-- The actual full accept consumer, parameterized only by an indexed preparation implementation and the public Server binding. The root/clearing/consumption callback is the existing native source code, not an assumed primitive. -/
noncomputable def run (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity)
    (preparation : StateT (State KemSK) ProbComp (Option (Inputs Reader ScalarBytes Word32) × List Pqxdh.Bytes)) :
    StateT (State KemSK) ProbComp (Option Nat) := do
  let state ← onNative nativeGet
  let collected ← preparation
  onNative (tail setup publicIdentity state collected)

noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) :
    StateT (State KemSK) ProbComp (Option Nat) :=
  run setup publicIdentity (prepare setup codec checks identityIndex raw)

noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) : StateT (State KemSK) ProbComp (Option Nat) :=
  run setup (setup.joint.publicKeys seed) (sourcePrepare setup codec checks seed identityIndex raw)

/-- Full preparation equality retains the exact current native state alongside both private pools and histories, under the initialized private slot. -/
theorem prepare_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (owned : state.1.1.seeds[identityIndex]? = some seed) :
    (prepare setup codec checks identityIndex raw).run state =
      (sourcePrepare setup codec checks seed identityIndex raw).run state := by
  simp only [prepare, sourcePrepare, StateT.run]
  congr 1
  exact PqxdhRegistrationJointServerPrefix.prefix_source setup codec checks seed identityIndex raw
    state.1 state.2.2.server.consumed owned

/-- Replacing preparation by its same-state source equality retains the actual whole accept continuation, including every failed allocation and successful pending-token publication. -/
theorem client_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (owned : state.1.1.seeds[identityIndex]? = some seed) :
    (client setup codec checks identityIndex (setup.joint.publicKeys seed) raw).run state =
      (source setup codec checks seed identityIndex raw).run state := by
  simp only [client, source, run, StateT.run_bind]
  simp only [onNative, nativeGet, localState, StateT.run, map_pure, pure_bind]
  rw [show prepare setup codec checks identityIndex raw state = sourcePrepare setup codec checks seed identityIndex raw state from
    prepare_source setup codec checks seed identityIndex raw state owned]

/-- This fact only exposes the literal existing native accept continuation; no callback order or branch is changed. -/
theorem native_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    (nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run state = (do
      let collected ← (nativePrefix setup codec checks seed raw).run state.2.server.consumed
      (tail setup (setup.joint.publicKeys seed) state.2 collected).run state) := by
  simp only [nativeAccept, tail, StateT.run_bind]
  simp only [nativeGet, localState, nativeCoins, StateT.run, pure_bind, bind_map_left, binding, challenge]
  rfl

/-- Erasing only private service annotations recovers the entire actual native raw accept, including session allocation, consumed IDs, pending tokens, root cache and instrumentation. -/
theorem source_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) :
    (fun result => (result.1, result.2.2)) <$> (source setup codec checks seed identityIndex raw).run state =
      (nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run state.2 := by
  rw [native_run]
  simp only [source, run, StateT.run_bind]
  simp only [onNative, nativeGet, localState, StateT.run, map_pure, pure_bind, sourcePrepare, map_bind, bind_map_left,
    Functor.map_map]
  have projected := PqxdhRegistrationJointServerPrefix.program_projection setup.joint seed identityIndex
    (serverAux setup codec checks) (PqxdhServerRootPreparation.collect raw) (state.1, state.2.2.server.consumed)
  simpa only [bind_map_left, StateT.run, PqxdhServerAuthNative.nativePrefix, Prod.mk.eta, id_map'] using
    congrArg (fun work => work >>= fun collected => (tail setup (setup.joint.publicKeys seed) state.2.2 collected).run state.2) projected

/-- The seedless indexed client has the exact complete native accept distribution after erasing only its private service annotations. -/
theorem client_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (owned : state.1.1.seeds[identityIndex]? = some seed) :
    (fun result => (result.1, result.2.2)) <$> (client setup codec checks identityIndex (setup.joint.publicKeys seed) raw).run state =
      (nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run state.2 := by
  rw [client_source setup codec checks seed identityIndex raw state owned]
  exact source_native setup codec checks seed identityIndex raw state

/-- The actual complete accept charges its scalar sample, encapsulation/base work and possible 64-byte restricted Extract-table draw, including all rejected attempts. -/
theorem client_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (owned : state.1.1.seeds[identityIndex]? = some seed) :
    ((client setup codec checks identityIndex (setup.joint.publicKeys seed) raw).run state).IsTotalQueryBound (96 + caps.encapsCost) := by
  have nativeBound := PqxdhRegistrationSchedule.accept_uniform setup codec checks caps bounded seed PqxdhRegistrationSchedule.observationScalar raw state.2
  rw [← client_native setup codec checks seed identityIndex raw state owned] at nativeBound
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using nativeBound

/-- The real source prefix preserves all indexed private key slots through every permitted callback and optional failure. -/
theorem source_prepare_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (result : (Option (Inputs Reader ScalarBytes Word32) × List Pqxdh.Bytes) × State KemSK)
    (supported : result ∈ support ((sourcePrepare setup codec checks seed identityIndex raw).run state)) :
    result.2.1.1.seeds = state.1.1.seeds ∧ result.2.1.2.keys = state.1.2.keys := by
  simp only [sourcePrepare, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨answer, reached, rfl⟩ := supported
  exact run_rel
    (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex (serverAux setup codec checks))
    (fun before after => after.1.1.seeds = before.1.1.seeds ∧ after.1.2.keys = before.1.2.keys)
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ first second => ⟨second.1.trans first.1, second.2.trans first.2⟩)
    (PqxdhRegistrationJointServerPrefix.query_slots setup.joint seed identityIndex (serverAux setup codec checks))
    (PqxdhServerRootPreparation.collect raw) (state.1, state.2.2.server.consumed) answer reached

/-- Full acceptance preserves all exact private identity/KEM slots while retaining the actual changed service history and native state. Thus later operations may reuse the initialized ownership invariant. -/
theorem source_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (result : Option Nat × State KemSK)
    (supported : result ∈ support ((source setup codec checks seed identityIndex raw).run state)) :
    result.2.1.1.seeds = state.1.1.seeds ∧ result.2.1.2.keys = state.1.2.keys := by
  simp only [source, run, StateT.run_bind] at supported
  simp only [onNative, nativeGet, localState, StateT.run, map_pure, pure_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, reached, final⟩ := supported
  simp only [support_map, Set.mem_image] at final
  obtain ⟨nativeResult, _, rfl⟩ := final
  exact source_prepare_slots setup codec checks seed identityIndex raw state prepared reached

/-- The complete executable accept also preserves every exact private slot, so its source ownership premise is stable across repeated accepting or rejecting attempts. -/
theorem client_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (owned : state.1.1.seeds[identityIndex]? = some seed) (result : Option Nat × State KemSK)
    (supported : result ∈ support ((client setup codec checks identityIndex (setup.joint.publicKeys seed) raw).run state)) :
    result.2.1.1.seeds = state.1.1.seeds ∧ result.2.1.2.keys = state.1.2.keys := by
  rw [client_source setup codec checks seed identityIndex raw state owned] at supported
  exact source_slots setup codec checks seed identityIndex raw state result supported

end BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.prepare_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.client_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.native_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.source_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.source_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.client_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.client_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.client_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.source_prepare_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.source_prepare_slots

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.source_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.source_slots

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.client_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept.client_slots
