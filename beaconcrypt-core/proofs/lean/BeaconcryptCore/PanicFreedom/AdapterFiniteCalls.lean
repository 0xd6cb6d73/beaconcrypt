-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterConstructorValidity
import BeaconcryptCore.PanicFreedom.AdapterPublicBeacon
import BeaconcryptCore.PanicFreedom.AdapterPublicBeaconFinish
import BeaconcryptCore.PanicFreedom.AdapterPublicServerAccept
import BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildState

/-! Finite sequential composition of the selected extracted public operations. Replies, including ordinary rejection, are retained, and every call receives the preceding call's returned object and RNG state. Dictionaries remain fixed throughout construction and the complete sequence. No caller-supplied whole-call normality premise is used by the public certificates. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace BeaconcryptCore.PanicFreedom.AdapterFiniteCalls
open Refinement AdapterNormal AdapterPublicOrdinary beaconcrypt_public_wrapper

private def run {Call Reply State : Type} (execute : Call → State → RustM (Reply × State)) :
    List Call → State → RustM (List Reply × State)
  | [], state => ok ([], state)
  | call :: calls, state => do
    let (reply, next) ← execute call state
    let (replies, final) ← run execute calls next
    ok (reply :: replies, final)

private theorem run_preserves {Call Reply State : Type}
    (execute : Call → State → RustM (Reply × State)) (invariant : State → Prop)
    (step : ∀ call state, invariant state → Ensures (execute call state) (fun result => invariant result.2))
    (calls : List Call) (state : State) (valid : invariant state) :
    Ensures (run execute calls state) (fun result => invariant result.2) := by
  induction calls generalizing state with
  | nil => exact ⟨([], state), rfl, valid⟩
  | cons call calls ih =>
    obtain ⟨⟨reply, next⟩, called, nextValid⟩ := step call state valid
    obtain ⟨⟨replies, final⟩, continued, finalValid⟩ := ih next nextValid
    exact ⟨(reply :: replies, final), by simp only [run, called, continued, bind_tc_ok, uncurry], finalValid⟩

inductive BeaconCall where
  | bundle
  | finish (bytes : Slice U8)
  | send (bytes : Slice U8)
  | receive (bytes : Slice U8)

inductive BeaconReply where
  | bundle (bytes : core.option.Option (alloc.vec.Vec U8))
  | finish (bytes : core.option.Option (alloc.vec.Vec U8))
  | send (sealed : core.option.Option beaconcrypt_public_ordinary.shared.Encrypted)
  | receive (opened : core.option.Option beaconcrypt_public_ordinary.shared.Decrypted)

inductive ServerCall where
  | accept (bytes : Slice U8)
  | build (output : server.RegistrationOutput) (application : core.option.Option (Slice U8))
  | send (bytes : Slice U8) (key : U64)
  | receive (bytes : Slice U8)

inductive ServerReply where
  | accept (output : core.option.Option server.RegistrationOutput)
  | build (response : core.option.Option server.RegResponse)
  | send (sealed : core.option.Option beaconcrypt_public_ordinary.shared.Encrypted)
  | receive (opened : core.option.Option beaconcrypt_public_ordinary.shared.Decrypted)

section Beacon
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations] [authentication : beaconcrypt.auth.Operations]
variable [recordOps : beaconcrypt.ratchet.Operations] [beaconcrypt_record_send.ratchet.Operations]
variable [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations]
variable [PublicWrapperPlatform.Codecs]

structure BeaconContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  bundle : AdapterPublicBeacon.BundleContracts
  generation : AdapterPublicRegistrationLoops.GenerationContracts generator
  finish : AdapterPublicBeaconFinish.Contracts
  send : AdapterRecordSend.Contracts

def beaconStep {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (call : BeaconCall) (state : beacon.Beacon × R) : RustM (BeaconReply × beacon.Beacon × R) :=
  match call with
  | .bundle => do
    let (reply, changed, rng) ← beacon.Beacon.get_registration_bundle_with_rng generator state.1 state.2
    ok (.bundle reply, changed, rng)
  | .finish bytes => do
    let (reply, changed) ← beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration state.1 bytes
    ok (.finish reply, changed, state.2)
  | .send bytes => do
    let (reply, changed) ← beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message state.1 bytes
    ok (.send reply, changed, state.2)
  | .receive bytes => do
    let (reply, changed) ← beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message state.1 bytes
    ok (.receive reply, changed, state.2)

theorem beacon_bundle_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) :
    beaconStep generator .bundle (self, rng) = (do
      let (reply, changed, after) ← beacon.Beacon.get_registration_bundle_with_rng generator self rng
      ok (.bundle reply, changed, after)) := rfl

theorem beacon_finish_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) (bytes : Slice U8) :
    beaconStep generator (.finish bytes) (self, rng) = (do
      let (reply, changed) ← beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration self bytes
      ok (.finish reply, changed, rng)) := rfl

theorem beacon_send_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) (bytes : Slice U8) :
    beaconStep generator (.send bytes) (self, rng) = (do
      let (reply, changed) ← beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message self bytes
      ok (.send reply, changed, rng)) := rfl

theorem beacon_receive_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) (bytes : Slice U8) :
    beaconStep generator (.receive bytes) (self, rng) = (do
      let (reply, changed) ← beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message self bytes
      ok (.receive reply, changed, rng)) := rfl

theorem beacon_step_preserves {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : BeaconContracts generator) (call : BeaconCall) (self : beacon.Beacon) (rng : R)
    (valid : ValidBeacon self) :
    Ensures (beaconStep generator call (self, rng)) (fun result => ValidBeacon result.2.1) := by
  cases call with
  | bundle =>
    obtain ⟨⟨reply, changed, after⟩, returned, changedValid⟩ :=
      AdapterPublicBeacon.get_registration_bundle_preserves contracts.bundle generator contracts.generation self rng valid
    exact ⟨(.bundle reply, changed, after), by simp only [beaconStep, returned, bind_tc_ok, uncurry], changedValid⟩
  | finish bytes =>
    obtain ⟨⟨reply, changed⟩, returned, changedValid⟩ :=
      AdapterPublicBeaconFinish.finish_registration_preserves contracts.finish self bytes valid
    exact ⟨(.finish reply, changed, rng), by simp only [beaconStep, returned, bind_tc_ok, uncurry], changedValid⟩
  | send bytes =>
    obtain ⟨⟨reply, changed⟩, returned, changedValid⟩ :=
      AdapterPublicOrdinary.beacon_encrypt_message_preserves contracts.send self bytes valid
    exact ⟨(.send reply, changed, rng), by simp only [beaconStep, returned, bind_tc_ok, uncurry], changedValid⟩
  | receive bytes =>
    obtain ⟨⟨reply, changed⟩, returned, changedValid⟩ :=
      AdapterPublicOrdinary.beacon_decrypt_message_preserves contracts.finish.record self bytes valid
    exact ⟨(.receive reply, changed, rng), by simp only [beaconStep, returned, bind_tc_ok, uncurry], changedValid⟩

def beaconCalls {R E : Type} (generator : rand_core.TryCryptoRng R E) (calls : List BeaconCall)
    (self : beacon.Beacon) (rng : R) : RustM (List BeaconReply × beacon.Beacon × R) :=
  run (beaconStep generator) calls (self, rng)

theorem beacon_calls_nil_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beacon.Beacon) (rng : R) : beaconCalls generator [] self rng = ok ([], self, rng) := rfl

theorem beacon_calls_cons_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (call : BeaconCall) (calls : List BeaconCall) (self : beacon.Beacon) (rng : R) :
    beaconCalls generator (call :: calls) self rng = (do
      let (reply, next, after) ← beaconStep generator call (self, rng)
      let (replies, final, last) ← beaconCalls generator calls next after
      ok (reply :: replies, final, last)) := rfl

/-- Every finite list returns normally and leaves its exact returned Beacon valid for the next call. -/
theorem beacon_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : BeaconContracts generator) (calls : List BeaconCall) (self : beacon.Beacon) (rng : R)
    (valid : ValidBeacon self) :
    Ensures (beaconCalls generator calls self rng) (fun result => ValidBeacon result.2.1) :=
  run_preserves (beaconStep generator) (fun state => ValidBeacon state.1)
    (fun call state before => beacon_step_preserves generator contracts call state.1 state.2 before)
    calls (self, rng) valid

variable [AdapterBeaconConstructorPrimitive.Operations]

def constructBeaconCalls {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (calls : List BeaconCall) (rng : R) :
    RustM (core.result.Result (List BeaconReply × beacon.Beacon) beaconcrypt_constructor.error.KeyGenError × R) := do
  let (created, after) ← beaconcrypt_constructor.beacon.Beacon.try_new_with_rng generator identifier identityKey mldsaKey rng
  match created with
  | .Err error => ok (.Err error, after)
  | .Ok self => do
    let (replies, final, last) ← beaconCalls generator calls self after
    ok (.Ok (replies, final), last)

theorem constructor_beacon_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (calls : List BeaconCall) (rng : R) :
    constructBeaconCalls generator identifier identityKey mldsaKey calls rng = (do
      let (created, after) ← beaconcrypt_constructor.beacon.Beacon.try_new_with_rng generator identifier identityKey mldsaKey rng
      match created with
      | .Err error => ok (.Err error, after)
      | .Ok self => do
        let (replies, final, last) ← beaconCalls generator calls self after
        ok (.Ok (replies, final), last)) := rfl

/-- Constructor errors are normal returns; successful construction starts the complete finite sequence. -/
theorem constructor_and_beacon_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.BeaconContracts generator) (contracts : BeaconContracts generator)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (calls : List BeaconCall) (rng : R) :
    Ensures (constructBeaconCalls generator identifier identityKey mldsaKey calls rng)
      (fun result => match result.1 with | .Err _ => True | .Ok completed => ValidBeacon completed.2) := by
  obtain ⟨⟨created, after⟩, constructed, initialValid⟩ :=
    AdapterConstructorValidity.beacon_try_new_with_rng_valid generator construction identifier identityKey mldsaKey rng
  cases created with
  | Err error =>
    exact ⟨(.Err error, after), by simp only [constructBeaconCalls, constructed, bind_tc_ok, uncurry], True.intro⟩
  | Ok self =>
    obtain ⟨⟨replies, final, last⟩, called, finalValid⟩ :=
      beacon_calls_preserve generator contracts calls self after initialValid
    exact ⟨(.Ok (replies, final), last),
      by simp only [constructBeaconCalls, constructed, called, bind_tc_ok, uncurry], finalValid⟩

theorem beacon_calls_from_try_new_with_rng {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.BeaconContracts generator) (contracts : BeaconContracts generator)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (initialRng after : R)
    (self : beacon.Beacon) (calls : List BeaconCall)
    (constructed : beaconcrypt_constructor.beacon.Beacon.try_new_with_rng generator identifier identityKey mldsaKey initialRng =
      ok (.Ok self, after)) :
    Ensures (beaconCalls generator calls self after) (fun result => ValidBeacon result.2.1) :=
  (AdapterConstructorValidity.beacon_try_new_with_rng_valid generator construction identifier identityKey mldsaKey initialRng).elim
    (fun _ returned => beacon_calls_preserve generator contracts calls self after
      (Eq.mp (congrArg (fun value : core.result.Result beacon.Beacon beaconcrypt_constructor.error.KeyGenError × R =>
        match value.1 with | .Ok created => ValidBeacon created | .Err _ => True)
        (RustM.ok.inj (returned.1.symm.trans constructed))) returned.2))

variable [standard : AdapterBeaconConstructorPrimitive.Standard]

def constructBeaconHostedCalls (identifier : U64) (identityKey mldsaKey : Slice U8)
    (calls : List BeaconCall) :
    RustM (core.result.Result (List BeaconReply × beacon.Beacon) beaconcrypt_constructor.error.KeyGenError) := do
  let created ← beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey
  match created with
  | .Err error => ok (.Err error)
  | .Ok self => do
    let (replies, final, _) ← beaconCalls standard.os calls self ()
    ok (.Ok (replies, final))

theorem constructor_beacon_hosted_source (identifier : U64) (identityKey mldsaKey : Slice U8)
    (calls : List BeaconCall) : constructBeaconHostedCalls identifier identityKey mldsaKey calls = (do
      let created ← beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey
      match created with
      | .Err error => ok (.Err error)
      | .Ok self => do
        let (replies, final, _) ← beaconCalls standard.os calls self ()
        ok (.Ok (replies, final))) := rfl

theorem hosted_constructor_and_beacon_calls_preserve
    (construction : AdapterConstructors.BeaconContracts standard.os) (contracts : BeaconContracts standard.os)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (calls : List BeaconCall) :
    Ensures (constructBeaconHostedCalls identifier identityKey mldsaKey calls)
      (fun result => match result with | .Err _ => True | .Ok completed => ValidBeacon completed.2) := by
  obtain ⟨created, constructed, initialValid⟩ :=
    AdapterConstructorValidity.beacon_try_new_valid construction identifier identityKey mldsaKey
  cases created with
  | Err error =>
    exact ⟨.Err error, by simp only [constructBeaconHostedCalls, constructed, bind_tc_ok], True.intro⟩
  | Ok self =>
    obtain ⟨⟨replies, final, last⟩, called, finalValid⟩ :=
      beacon_calls_preserve standard.os contracts calls self () initialValid
    exact ⟨.Ok (replies, final),
      by simp only [constructBeaconHostedCalls, constructed, called, bind_tc_ok, uncurry], finalValid⟩

theorem beacon_calls_from_try_new
    (construction : AdapterConstructors.BeaconContracts standard.os) (contracts : BeaconContracts standard.os)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (self : beacon.Beacon) (calls : List BeaconCall)
    (constructed : beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey = ok (.Ok self)) :
    Ensures (beaconCalls standard.os calls self ()) (fun result => ValidBeacon result.2.1) :=
  (AdapterConstructorValidity.beacon_try_new_valid construction identifier identityKey mldsaKey).elim
    (fun _ returned => beacon_calls_preserve standard.os contracts calls self ()
      (Eq.mp (congrArg (fun value : core.result.Result beacon.Beacon beaconcrypt_constructor.error.KeyGenError =>
        match value with | .Ok created => ValidBeacon created | .Err _ => True)
        (RustM.ok.inj (returned.1.symm.trans constructed))) returned.2))

end Beacon

section Server
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [localOps : PublicWrapperPlatform.LocalOperations] [authentication : beaconcrypt.auth.Operations]
variable [recordOps : beaconcrypt.ratchet.Operations] [beaconcrypt_record_send.ratchet.Operations]
variable [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations]
variable [PublicWrapperPlatform.Codecs] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]

structure ServerContracts {R E : Type} (generator : rand_core.TryCryptoRng R E) : Prop where
  authentication : AdapterPublicServer.AuthenticationContracts
  agreement : AdapterPublicRegistrationLoops.AgreementContracts
  random : AdapterPublicRegistrationLoops.AgreementRngContracts generator
  replay : AdapterPublicServerAccept.ReplayContracts
  build : AdapterPublicServerBuild.Contracts
  containers : AdapterPublicServerBuildState.ContainerContracts
  lookups : LookupContracts
  send : AdapterRecordSend.Contracts
  receive : AdapterRecordReceive.Contracts

def serverStep {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (call : ServerCall) (state : server.Server × R) : RustM (ServerReply × server.Server × R) :=
  match call with
  | .accept bytes => do
    let (reply, changed, rng) ← beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng generator state.1 bytes state.2
    ok (.accept reply, changed, rng)
  | .build output application => do
    let (reply, changed) ← server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response state.1 output application
    ok (.build reply, changed, state.2)
  | .send bytes key => do
    let (reply, changed) ← beaconcrypt_public_ordinary.server.Server.encrypt_message state.1 bytes key
    ok (.send reply, changed, state.2)
  | .receive bytes => do
    let (reply, changed) ← beaconcrypt_public_ordinary.server.Server.decrypt_message state.1 bytes
    ok (.receive reply, changed, state.2)

theorem server_accept_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) (bytes : Slice U8) :
    serverStep generator (.accept bytes) (self, rng) = (do
      let (reply, changed, after) ← beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng generator self bytes rng
      ok (.accept reply, changed, after)) := rfl

theorem server_build_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) (output : server.RegistrationOutput)
    (application : core.option.Option (Slice U8)) :
    serverStep generator (.build output application) (self, rng) = (do
      let (reply, changed) ← server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self output application
      ok (.build reply, changed, rng)) := rfl

theorem server_send_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) (bytes : Slice U8) (key : U64) :
    serverStep generator (.send bytes key) (self, rng) = (do
      let (reply, changed) ← beaconcrypt_public_ordinary.server.Server.encrypt_message self bytes key
      ok (.send reply, changed, rng)) := rfl

theorem server_receive_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) (bytes : Slice U8) :
    serverStep generator (.receive bytes) (self, rng) = (do
      let (reply, changed) ← beaconcrypt_public_ordinary.server.Server.decrypt_message self bytes
      ok (.receive reply, changed, rng)) := rfl

theorem server_step_preserves {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : ServerContracts generator) (call : ServerCall) (self : server.Server) (rng : R)
    (valid : ValidServer self) :
    Ensures (serverStep generator call (self, rng)) (fun result => ValidServer result.2.1) := by
  cases call with
  | accept bytes =>
    obtain ⟨⟨reply, changed, after⟩, returned, changedValid⟩ :=
      AdapterPublicServerAccept.get_shared_secret_with_rng_preserves contracts.authentication contracts.agreement
        contracts.replay generator contracts.random self bytes rng valid
    exact ⟨(.accept reply, changed, after), by simp only [serverStep, returned, bind_tc_ok, uncurry], changedValid⟩
  | build output application =>
    obtain ⟨⟨reply, changed⟩, returned, changedValid⟩ :=
      AdapterPublicServerBuildState.build_registration_response_preserves contracts.build contracts.containers self output application valid
    exact ⟨(.build reply, changed, rng), by simp only [serverStep, returned, bind_tc_ok, uncurry], changedValid⟩
  | send bytes key =>
    obtain ⟨⟨reply, changed⟩, returned, changedValid⟩ :=
      AdapterPublicOrdinary.server_encrypt_message_preserves contracts.send contracts.lookups self bytes key valid
    exact ⟨(.send reply, changed, rng), by simp only [serverStep, returned, bind_tc_ok, uncurry], changedValid⟩
  | receive bytes =>
    obtain ⟨⟨reply, changed⟩, returned, changedValid⟩ :=
      AdapterPublicOrdinary.server_decrypt_message_preserves contracts.receive contracts.lookups self bytes valid
    exact ⟨(.receive reply, changed, rng), by simp only [serverStep, returned, bind_tc_ok, uncurry], changedValid⟩

def serverCalls {R E : Type} (generator : rand_core.TryCryptoRng R E) (calls : List ServerCall)
    (self : server.Server) (rng : R) : RustM (List ServerReply × server.Server × R) :=
  run (serverStep generator) calls (self, rng)

theorem server_calls_nil_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : server.Server) (rng : R) : serverCalls generator [] self rng = ok ([], self, rng) := rfl

theorem server_calls_cons_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (call : ServerCall) (calls : List ServerCall) (self : server.Server) (rng : R) :
    serverCalls generator (call :: calls) self rng = (do
      let (reply, next, after) ← serverStep generator call (self, rng)
      let (replies, final, last) ← serverCalls generator calls next after
      ok (reply :: replies, final, last)) := rfl

theorem server_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (contracts : ServerContracts generator) (calls : List ServerCall) (self : server.Server) (rng : R)
    (valid : ValidServer self) :
    Ensures (serverCalls generator calls self rng) (fun result => ValidServer result.2.1) :=
  run_preserves (serverStep generator) (fun state => ValidServer state.1)
    (fun call state before => server_step_preserves generator contracts call state.1 state.2 before)
    calls (self, rng) valid

variable [AdapterBeaconConstructorPrimitive.Operations] [AdapterServerConstructorPrimitive.Standard]

def constructServerCalls {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (calls : List ServerCall) (rng : R) :
    RustM (core.result.Result (List ServerReply × server.Server) beaconcrypt_server_constructor.error.KeyGenError × R) := do
  let (created, after) ← beaconcrypt_server_constructor.server.Server.try_new_with_rng generator identifier identitySeed mldsaSeed rng
  match created with
  | .Err error => ok (.Err error, after)
  | .Ok self => do
    let (replies, final, last) ← serverCalls generator calls self after
    ok (.Ok (replies, final), last)

theorem constructor_server_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (calls : List ServerCall) (rng : R) :
    constructServerCalls generator identifier identitySeed mldsaSeed calls rng = (do
      let (created, after) ← beaconcrypt_server_constructor.server.Server.try_new_with_rng generator identifier identitySeed mldsaSeed rng
      match created with
      | .Err error => ok (.Err error, after)
      | .Ok self => do
        let (replies, final, last) ← serverCalls generator calls self after
        ok (.Ok (replies, final), last)) := rfl

theorem constructor_and_server_calls_preserve {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.ServerContracts generator)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts generator)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (calls : List ServerCall) (rng : R) :
    Ensures (constructServerCalls generator identifier identitySeed mldsaSeed calls rng)
      (fun result => match result.1 with | .Err _ => True | .Ok completed => ValidServer completed.2) := by
  obtain ⟨⟨created, after⟩, constructed, initialValid⟩ :=
    AdapterConstructorValidity.server_try_new_with_rng_valid generator construction initialization identifier identitySeed mldsaSeed rng
  cases created with
  | Err error =>
    exact ⟨(.Err error, after), by simp only [constructServerCalls, constructed, bind_tc_ok, uncurry], True.intro⟩
  | Ok self =>
    obtain ⟨⟨replies, final, last⟩, called, finalValid⟩ :=
      server_calls_preserve generator contracts calls self after initialValid
    exact ⟨(.Ok (replies, final), last),
      by simp only [constructServerCalls, constructed, called, bind_tc_ok, uncurry], finalValid⟩

theorem server_calls_from_try_new_with_rng {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (construction : AdapterConstructors.ServerContracts generator)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts generator)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8)) (initialRng after : R)
    (self : server.Server) (calls : List ServerCall)
    (constructed : beaconcrypt_server_constructor.server.Server.try_new_with_rng generator identifier identitySeed mldsaSeed initialRng =
      ok (.Ok self, after)) :
    Ensures (serverCalls generator calls self after) (fun result => ValidServer result.2.1) :=
  (AdapterConstructorValidity.server_try_new_with_rng_valid generator construction initialization identifier identitySeed mldsaSeed initialRng).elim
    (fun _ returned => server_calls_preserve generator contracts calls self after
      (Eq.mp (congrArg (fun value : core.result.Result server.Server beaconcrypt_server_constructor.error.KeyGenError × R =>
        match value.1 with | .Ok created => ValidServer created | .Err _ => True)
        (RustM.ok.inj (returned.1.symm.trans constructed))) returned.2))

variable [standard : AdapterBeaconConstructorPrimitive.Standard]

def constructServerHostedCalls (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (calls : List ServerCall) :
    RustM (core.result.Result (List ServerReply × server.Server) beaconcrypt_server_constructor.error.KeyGenError) := do
  let created ← beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed
  match created with
  | .Err error => ok (.Err error)
  | .Ok self => do
    let (replies, final, _) ← serverCalls standard.os calls self ()
    ok (.Ok (replies, final))

theorem constructor_server_hosted_source (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (calls : List ServerCall) : constructServerHostedCalls identifier identitySeed mldsaSeed calls = (do
      let created ← beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed
      match created with
      | .Err error => ok (.Err error)
      | .Ok self => do
        let (replies, final, _) ← serverCalls standard.os calls self ()
        ok (.Ok (replies, final))) := rfl

theorem hosted_constructor_and_server_calls_preserve
    (construction : AdapterConstructors.ServerContracts standard.os)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts standard.os)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8)) (calls : List ServerCall) :
    Ensures (constructServerHostedCalls identifier identitySeed mldsaSeed calls)
      (fun result => match result with | .Err _ => True | .Ok completed => ValidServer completed.2) := by
  obtain ⟨created, constructed, initialValid⟩ :=
    AdapterConstructorValidity.server_try_new_valid construction initialization identifier identitySeed mldsaSeed
  cases created with
  | Err error =>
    exact ⟨.Err error, by simp only [constructServerHostedCalls, constructed, bind_tc_ok], True.intro⟩
  | Ok self =>
    obtain ⟨⟨replies, final, last⟩, called, finalValid⟩ :=
      server_calls_preserve standard.os contracts calls self () initialValid
    exact ⟨.Ok (replies, final),
      by simp only [constructServerHostedCalls, constructed, called, bind_tc_ok, uncurry], finalValid⟩

theorem server_calls_from_try_new
    (construction : AdapterConstructors.ServerContracts standard.os)
    (initialization : AdapterConstructorValidity.InitializationContracts) (contracts : ServerContracts standard.os)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8))
    (self : server.Server) (calls : List ServerCall)
    (constructed : beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed = ok (.Ok self)) :
    Ensures (serverCalls standard.os calls self ()) (fun result => ValidServer result.2.1) :=
  (AdapterConstructorValidity.server_try_new_valid construction initialization identifier identitySeed mldsaSeed).elim
    (fun _ returned => server_calls_preserve standard.os contracts calls self ()
      (Eq.mp (congrArg (fun value : core.result.Result server.Server beaconcrypt_server_constructor.error.KeyGenError =>
        match value with | .Ok created => ValidServer created | .Err _ => True)
        (RustM.ok.inj (returned.1.symm.trans constructed))) returned.2))

end Server

end BeaconcryptCore.PanicFreedom.AdapterFiniteCalls
