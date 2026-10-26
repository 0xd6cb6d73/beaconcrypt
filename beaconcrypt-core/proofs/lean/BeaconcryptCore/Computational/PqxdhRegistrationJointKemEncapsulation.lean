-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts

/-! Expose the actual ordered Server encapsulation callback for a later ordinary KEM challenge cut. This is an operational source hook, interpreted by the existing actual encapsulator, not a new primitive security assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Next Local : Type}

/-- The hook retains the original caller-supplied raw candidate and actual verified PQ field. It returns exactly the source optional ciphertext/shared-secret pair. -/
abbrev EncapsulationSpec : OracleSpec (Pqxdh.Bytes × PqxdhKemIndCca.MlKem768PublicKey) :=
  fun _ => Option (PqxdhBeaconPhase2Preparation.Ciphertext × PqxdhBeaconPhase2Preparation.Word32)
abbrev Spec (KemSK : Type) := PqxdhLiveKemBirth.Spec KemSK + EncapsulationSpec
abbrev Client (KemSK Result : Type) := StateT (NativeState KemSK) (OracleComp (Spec KemSK)) Result

def forward : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp (Spec KemSK)) :=
  fun query => (Spec KemSK).query (.inl query)

def lift (work : StateT Local (OracleComp (PqxdhLiveKemBirth.Spec KemSK)) Result) :
    StateT Local (OracleComp (Spec KemSK)) Result := fun state => simulateQ forward (work.run state)

/-- Interpret the exposed callback by the same real source encapsulator. Raw bytes are retained only as target-selection metadata; they do not alter its input distribution. -/
def actual (setup : Setup baseSpec KemSK) : QueryImpl (Spec KemSK) (OracleComp (PqxdhLiveKemBirth.Spec KemSK))
  | .inl query => (PqxdhLiveKemBirth.Spec KemSK).query query
  | .inr request => PqxdhLiveKemBirth.coins (encapsulate setup request.2)

/-- Only the original encapsulation callback is exposed; all earlier/later native callbacks and consumed-registration state remain in the same position. -/
def prefixImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) : QueryImpl (PqxdhRegistrationJointServerPrefix.Spec KemSK Reader)
      (StateT (List Pqxdh.Bytes) (OracleComp (Spec KemSK)))
  | .inl query => fun consumed => (fun answer => (answer, consumed)) <$> forward query
  | .inr (.encapsulate key) => fun consumed => (fun answer => (answer, consumed)) <$>
      (Spec KemSK).query (.inr (raw, key))
  | .inr query => fun consumed => simulateQ forward
      (PqxdhLiveKemBirth.coins ((serverAux setup codec checks query).run consumed))

/-- Forwarding keeps the entire original private-service program, including all adaptive continuations and uniform queries. -/
theorem forward_actual (setup : Setup baseSpec KemSK) (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) :
    simulateQ (actual setup) (simulateQ forward work) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, forward, actual, ih]

/-- Interpreting the exposed encapsulation gives the exact old raw-prefix callback, retaining the original consumed set and every optional reply. -/
theorem prefix_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (query : (PqxdhRegistrationJointServerPrefix.Spec KemSK Reader).Domain)
    (consumed : List Pqxdh.Bytes) :
    simulateQ (actual setup) ((prefixImpl setup codec checks raw query).run consumed) =
      (PqxdhRegistrationJointOpenBackend.prefixImpl setup codec checks query).run consumed := by
  rcases query with query | query
  · simp only [prefixImpl, StateT.run, simulateQ_map, forward, simulateQ_spec_query, actual,
      PqxdhRegistrationJointOpenBackend.prefixImpl]
  · cases query <;> try exact forward_actual setup _
    simp only [prefixImpl, StateT.run, simulateQ_map, simulateQ_spec_query, actual,
      PqxdhRegistrationJointOpenBackend.prefixImpl, serverAux, StateT.lift,
      PqxdhLiveKemBirth.coins, bind_pure_comp, simulateQ_map]
    rfl

/-- The entire ordered raw collector, not only its reply marginal, is recovered after actual encapsulation interpretation. -/
theorem prefix_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (work : OracleComp (PqxdhRegistrationJointServerPrefix.Spec KemSK Reader) Result)
    (consumed : List Pqxdh.Bytes) :
    simulateQ (actual setup) ((simulateQ (prefixImpl setup codec checks raw) work).run consumed) =
      (simulateQ (PqxdhRegistrationJointOpenBackend.prefixImpl setup codec checks) work).run consumed := by
  induction work using OracleComp.inductionOn generalizing consumed with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, prefix_query, ih]

/-- Open preparation starts from the same consumed-registration set and retains the full source native state around the suspended encapsulation continuation. -/
def prepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) : Client KemSK
      (Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :=
  fun state => (fun result => (result, state)) <$>
    (simulateQ (prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run state.2.server.consumed

/-- Exposing encapsulation leaves actual source preparation unchanged under its original interpreter, with the complete optional result and consumed poststate. -/
theorem prepare_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    simulateQ (actual setup) ((prepare setup codec checks identityIndex raw).run state) =
      (PqxdhRegistrationJointOpenBackend.prepare setup codec checks identityIndex raw).run state := by
  simpa only [prepare, StateT.run, simulateQ_map, PqxdhRegistrationJointOpenBackend.prepare] using
    congrArg (fun work => (fun result => (result, state)) <$> work)
      (prefix_program setup codec checks raw (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw) state.2.server.consumed)

/-- Local callbacks preserve their exact entire state and random work after the exposed interface is interpreted. -/
theorem lift_actual (setup : Setup baseSpec KemSK)
    (work : StateT Local (OracleComp (PqxdhLiveKemBirth.Spec KemSK)) Result) (state : Local) :
    simulateQ (actual setup) ((lift work).run state) = work.run state := forward_actual setup _

/-- Actual raw accept with only its encapsulation operation exposed. Every earlier and later callback stays in source order. -/
noncomputable def accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) : Client KemSK (Option Nat) := do
  let before ← lift (PqxdhRegistrationJointOpenBackend.native nativeGet)
  let collected ← prepare setup codec checks identityIndex raw
  lift (PqxdhRegistrationJointOpenBackend.native (PqxdhRegistrationJointServerAccept.tail setup publicIdentity before collected))

/-- The full raw accept is recovered, including failure and all native fields, by interpreting the one exposed public encapsulation hook. -/
theorem accept_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    simulateQ (actual setup) ((accept setup codec checks identityIndex publicIdentity raw).run state) =
      (PqxdhRegistrationJointOpenBackend.accept setup codec checks identityIndex publicIdentity raw).run state := by
  simp only [accept, PqxdhRegistrationJointOpenBackend.accept, StateT.run_bind, simulateQ_bind,
    lift_actual, prepare_actual]

/-- The original complete source backend with only actual raw-accept encapsulation exposed. All other private services, native callbacks and public evaluations use their previous implementations. -/
noncomputable def impl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) :
    QueryImpl (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) (Client KemSK)
  | .inr (.accept raw) => accept setup codec checks identityIndex publicIdentity raw
  | query => lift (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity query)

/-- Every complete source callback is unchanged when the exposed operation uses the actual encapsulator. -/
theorem query_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) (state : NativeState KemSK) :
    simulateQ (actual setup) ((impl setup codec checks identityIndex publicIdentity query).run state) =
      (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity query).run state := by
  rcases query with (service | tail) | shared
  case inl.inl => exact lift_actual setup _ state
  case inl.inr => exact lift_actual setup _ state
  case inr => cases shared <;> first | exact accept_actual setup codec checks identityIndex publicIdentity _ state | exact lift_actual setup _ state

/-- Every adaptive source program and its complete native state are recovered, not just a selected successful acceptance. -/
theorem program_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) Result) (state : NativeState KemSK) :
    simulateQ (actual setup) ((simulateQ (impl setup codec checks identityIndex publicIdentity) work).run state) =
      (simulateQ (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, query_actual, ih]

/-- The exact original source14 client with public encapsulation hooks and the unchanged complete owner/native result. -/
noncomputable def commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Result)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK) :
    OracleComp (Spec KemSK) (PqxdhRegistrationJointKemCommands.Outcome KemSK Result) :=
  (simulateQ (impl setup codec checks identityIndex publicIdentity)
    ((simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) work).run owners)).run state

/-- Actual source commands equal the exposed complete command compiler under the real public encapsulation interpreter. -/
theorem commands_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Result)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK) :
    simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity work owners state) =
      PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex publicIdentity work owners state :=
  program_actual setup codec checks identityIndex publicIdentity _ state

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.forward_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.forward_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.prefix_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.prefix_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.prefix_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.prefix_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.prepare_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.prepare_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.lift_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.lift_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.accept_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.accept_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.query_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.query_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.program_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.program_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.commands_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEncapsulation.commands_actual
