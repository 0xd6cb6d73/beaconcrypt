-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedSchedule

/-! Factor the actual registration backend into open indexed identity/KEM requests and explicitly interpreted local source work. Native work keeps its whole state and uniform draws; no macro is promoted to a primitive security assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointPreparation (Pool)
open PqxdhRegistrationJointFinish (State onPool onNative)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Next Local : Type}

abbrev Spec (KemSK : Type) := PqxdhLiveKemBirth.Spec KemSK
abbrev Client (KemSK Result : Type) := StateT (NativeState KemSK) (OracleComp (Spec KemSK)) Result

/-- Local native computation retains every native field and forwards all its uniform work through the explicit ambient channel. It has no private identity/KEM pool argument. -/
def native (work : StateT Local ProbComp Result) : StateT Local (OracleComp (Spec KemSK)) Result := fun state =>
  PqxdhLiveKemBirth.coins (work.run state)

/-- Indexed private services remain syntactically open in the actual client. -/
def pool : QueryImpl (Spec KemSK) (StateT Local (OracleComp (Spec KemSK))) := fun query state => (fun answer => (answer, state)) <$> (Spec KemSK).query query

/-- Interpret only the open private-service backend and reassociate the complete private/native state. -/
def run (setup : Setup baseSpec KemSK) (work : StateT Local (OracleComp (Spec KemSK)) Result)
    (state : Pool KemSK × Local) : ProbComp (Result × (Pool KemSK × Local)) :=
  (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) (work.run state.2)).run state.1

/-- Local work has exactly its original complete native execution and preserves both private pools and histories. -/
theorem native_run (setup : Setup baseSpec KemSK) (work : StateT Local ProbComp Result) (state : Pool KemSK × Local) :
    run setup (native work) state = (PqxdhRegistrationJointServerPrefix.onAux work).run state := by
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (PqxdhLiveKemBirth.coins (work.run state.2))).run state.1 = _
  rw [PqxdhLiveKemBirth.coins_complete]
  simp only [Functor.map_map, PqxdhRegistrationJointServerPrefix.onAux, StateT.run]

/-- A single open request has exactly the original private-service execution, retaining the complete native state. -/
theorem pool_run (setup : Setup baseSpec KemSK) (query : (Spec KemSK).Domain) (state : Pool KemSK × Local) :
    run setup (pool query) state =
      (PqxdhRegistrationJointServerPrefix.onPool (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query)).run state := by
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      ((fun answer => (answer, state.2)) <$> (Spec KemSK).query query)).run state.1 = _
  rw [simulateQ_map, simulateQ_spec_query, StateT.run_map]
  simp only [Functor.map_map, PqxdhRegistrationJointServerPrefix.onPool, StateT.run]

/-- Reassociation preserves every adaptive continuation and complete intermediate private/native state. -/
theorem run_bind (setup : Setup baseSpec KemSK) (work : StateT Local (OracleComp (Spec KemSK)) Result)
    (next : Result → StateT Local (OracleComp (Spec KemSK)) Next) (state : Pool KemSK × Local) :
    run setup (work >>= next) state =
      (run setup work state >>= fun result => run setup (next result.1) result.2) := by
  simp only [run, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]

/-- The real raw Server collector leaves indexed services open and evaluates every auxiliary callback on its actual consumed-registration state. -/
def prefixImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl (PqxdhRegistrationJointServerPrefix.Spec KemSK Reader)
      (StateT (List Pqxdh.Bytes) (OracleComp (Spec KemSK)))
  | .inl query => fun consumed => (fun answer => (answer, consumed)) <$> (Spec KemSK).query query
  | .inr query => fun consumed => PqxdhLiveKemBirth.coins ((serverAux setup codec checks query).run consumed)

/-- Every raw prefix callback has exactly its original interpreted reply and complete private/consumed poststate; local auxiliary work stays in its source position. -/
theorem prefix_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : (PqxdhRegistrationJointServerPrefix.Spec KemSK Reader).Domain)
    (state : Pool KemSK × List Pqxdh.Bytes) :
    run setup (prefixImpl setup codec checks query) state =
      (PqxdhRegistrationJointServerPrefix.impl setup (serverAux setup codec checks) query).run state := by
  cases query
  case inl request => exact pool_run setup request state
  case inr request => exact native_run setup (serverAux setup codec checks request) state

/-- The complete raw prefix keeps its entire adaptive continuation while exposing actual identity/KEM requests. -/
theorem prefix_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (program : OracleComp (PqxdhRegistrationJointServerPrefix.Spec KemSK Reader) Result)
    (state : Pool KemSK × List Pqxdh.Bytes) :
    run setup (simulateQ (prefixImpl setup codec checks) program) state =
      (simulateQ (PqxdhRegistrationJointServerPrefix.impl setup (serverAux setup codec checks)) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, run, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, run_bind, prefix_query, StateT.run_bind, ih]

/-- The actual raw preparation starts from the current consumed set and retains its complete optional result and exact consumed poststate. -/
def prepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) : Client KemSK
      (Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) := fun state =>
  (fun result => (result, state)) <$>
    (simulateQ (prefixImpl setup codec checks)
      (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run state.2.server.consumed

/-- Actual indexed preparation is recovered with its full private/native result after interpreting the open requests. -/
theorem prepare_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) :
    run setup (prepare setup codec checks identityIndex raw) state =
      (PqxdhRegistrationJointServerAccept.prepare setup codec checks identityIndex raw).run state := by
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      ((fun result => (result, state.2)) <$>
        (simulateQ (prefixImpl setup codec checks)
          (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run state.2.2.server.consumed)).run state.1 = _
  rw [simulateQ_map, StateT.run_map]
  simpa only [run, PqxdhRegistrationJointServerAccept.prepare, StateT.run, Functor.map_map] using congrArg
    (fun work => (fun result => ((result.1, result.2.2), (result.2.1, state.2))) <$> work)
    (prefix_program setup codec checks (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)
      (state.1, state.2.2.server.consumed))

/-- The full raw accept executes its original preparation, allocation, root/clearing/consumption and optional pending publication with indexed services left open. -/
noncomputable def accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) : Client KemSK (Option Nat) := do
  let before ← native nativeGet
  let collected ← prepare setup codec checks identityIndex raw
  native (PqxdhRegistrationJointServerAccept.tail setup publicIdentity before collected)

/-- Interpreting open services recovers the complete actual indexed Server accept, including every failed attempt and full private/native state. -/
theorem accept_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : State KemSK) :
    run setup (accept setup codec checks identityIndex publicIdentity raw) state =
      (PqxdhRegistrationJointServerAccept.client setup codec checks identityIndex publicIdentity raw).run state := by
  simp only [accept, run_bind, native_run, prepare_run, PqxdhRegistrationJointServerAccept.client,
    PqxdhRegistrationJointServerAccept.run, StateT.run_bind]
  rfl

/-- The existing complete command backend leaves joint identity/KEM requests open. All remaining callbacks run their literal local native code with explicit uniform forwarding. -/
noncomputable def impl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) :
    QueryImpl (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) (Client KemSK)
  | .inl (.inl query) => pool query
  | .inl (.inr query) => native (sourceBeaconTail setup codec query)
  | .inr (.accept raw) => accept setup codec checks identityIndex publicIdentity raw
  | .inr (.build index payload) => native (nativeBuild setup codec checks index payload)
  | .inr (.hmac key message) => native (PqxdhRegistrationJointPublicShared.hmac setup key message)
  | .inr (.hash bytes) => native (nativeHash bytes)
  | .inr (.reveal keyId) => native (localState fun state => (revealKernel keyId state, state))

/-- Every actual backend callback recovers the complete previously checked seedless interpreter, including optional native replies and both private service histories. -/
theorem query_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) (state : State KemSK) :
    run setup (impl setup codec checks identityIndex publicIdentity query) state =
      (PqxdhRegistrationJointServerClient.impl setup codec checks identityIndex publicIdentity query).run state := by
  rcases query with (service | tail) | shared
  case inl.inl => exact pool_run setup service state
  case inl.inr => exact native_run setup (sourceBeaconTail setup codec tail) state
  case inr =>
    cases shared <;> first
    | exact accept_run setup codec checks identityIndex publicIdentity _ state
    | exact native_run setup _ state

/-- Every complete adaptive backend program has the original full state distribution after interpreting the remaining open identity/KEM requests. -/
theorem program_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (program : OracleComp (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) Result) (state : State KemSK) :
    run setup (simulateQ (impl setup codec checks identityIndex publicIdentity) program) state =
      (simulateQ (PqxdhRegistrationJointServerClient.impl setup codec checks identityIndex publicIdentity) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, run, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, run_bind, query_run, StateT.run_bind, ih]

/-- Actual public command compilation has access only to the public Server binding, encoded live owners and native state. Private identity/KEM pools remain outside this program. -/
noncomputable def compile (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response Result)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    Client KemSK (Result × List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :=
  simulateQ (impl setup codec checks identityIndex publicIdentity) (work.run owners)

/-- Reinstall the complete owner registry after interpreting open services; no result coordinate or private history is discarded. -/
noncomputable def execute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response Result)
    (state : PqxdhRegistrationJointGeneratedFinish.EncodedState KemSK) :
    ProbComp (Result × PqxdhRegistrationJointGeneratedFinish.EncodedState KemSK) :=
  (fun result => (result.1.1, ⟨result.2.1, result.2.2, result.1.2⟩)) <$>
    run setup (compile setup codec checks identityIndex publicIdentity work state.owners) (state.pool, state.shared)

/-- The complete actual command client is the reviewed seedless scheduler with joint identity/KEM requests still open until the final interpretation. -/
theorem execute_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response Result)
    (state : PqxdhRegistrationJointGeneratedFinish.EncodedState KemSK) :
    execute setup codec checks identityIndex publicIdentity work state =
      PqxdhRegistrationJointServerClient.execute setup codec checks identityIndex publicIdentity work state := by
  simp only [execute, compile, program_run, PqxdhRegistrationJointServerClient.execute]

end BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.native_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.pool_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.pool_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.run_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.prefix_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.prefix_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.prefix_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.prefix_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.prepare_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.accept_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.accept_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.query_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.query_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.program_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.execute_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend.execute_run
