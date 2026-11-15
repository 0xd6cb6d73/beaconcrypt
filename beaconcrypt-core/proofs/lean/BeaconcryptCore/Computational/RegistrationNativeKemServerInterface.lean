-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication

/-! The selected Server KEM client has explicit local state, actual World effects and non-KEM native callbacks. The ambient service cannot access the private indexed KEM pool. Authentication and retention execute the existing SDK source operations; only the independently proved uniform accounting coordinate is projected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemServerInterface
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeKemServerState (State mask maskServer)
variable {ι KemSK Reader Response Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

inductive Request (n : Nat) (mlSource : RegistrationNativeMldsa.Source) where
  | get
  | put (state : State n mlSource)
  | authenticate (packet : registration.InitPacket)
  | retain (accepted : agreement.ServerAgreement)
  | world (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
  | primitive (query : RegistrationNativeKemInterface.OtherRequest)

abbrev Ambient (n : Nat) (mlSource : RegistrationNativeMldsa.Source) : OracleSpec (Request n mlSource)
  | .get => State n mlSource
  | .put _ => Unit
  | .authenticate _ => RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)
  | .retain _ => RustM (Option Nat)
  | .world query => (PqxdhRecordLiftInterface.EnvEffects n).Range query
  | .primitive query => RegistrationNativeKemInterface.OtherSpec.Range query

abbrev Spec (n : Nat) (mlSource : RegistrationNativeMldsa.Source) (KemSK : Type) :=
  RegistrationNativeKemInterface.Spec (Ambient n mlSource) KemSK

def withRole (before : State n mlSource) (role : RegistrationServerRoleBackend.State) : State n mlSource :=
  { before with server := { before.server with world := { before.server.world with auxiliary := role } } }

def server (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp
    Value) : StateT (State n mlSource) ProbComp Value := fun before =>
  (fun result => (result.1, mask { before with server := result.2 })) <$> work.run before.server

/-- Actual ordinary native callbacks cannot read the private KEM pool or the selected KEM secret. -/
noncomputable def other (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (Ambient n mlSource) (StateT (State n mlSource) ProbComp)
  | .get => fun before => pure (mask before, mask before)
  | .put after => fun _ => pure ((), mask after)
  | .authenticate packet => server
      (RegistrationServerNativeSource.authenticate setup codec route verify created packet)
  | .retain accepted => server (RegistrationServerNativeSource.retain created accepted)
  | .world query => fun before =>
      (fun result => (result.1, mask { before with server := { before.server with world :=
        { before.server.world with world := (result.2, before.server.world.world.2) } } })) <$>
        (PqxdhRecordLiftWorld.effects query).run before.server.world.world.1
  | .primitive query => fun before => (fun result => (result.1, mask (withRole before result.2))) <$>
      (RegistrationNativeKemBackend.serverOther setup checks representation created.seed query).run before.server.world.auxiliary

noncomputable def source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (Spec n mlSource KemSK) (StateT (State n mlSource × PqxdhLiveKemBirth.Pool KemSK) ProbComp) :=
  RegistrationNativeKemInterface.source setup.baseImpl setup.kem (Ambient n mlSource)
    (other setup codec checks route verify representation created)

/-- Native primitive constructors retain their original shape; non-KEM requests go only to the pool-free ambient service. -/
def lift : QueryImpl (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK)
    (OracleComp (Spec n mlSource KemSK))
  | .inl query => (Spec n mlSource KemSK).query (.inl (.primitive query))
  | .inr (.inl query) => (Spec n mlSource KemSK).query (.inr (.inl query))
  | .inr (.inr key) => (Spec n mlSource KemSK).query (.inr (.inr key))

def get : OracleComp (Spec n mlSource KemSK) (State n mlSource) :=
  (Spec n mlSource KemSK).query (.inl .get)

def put (state : State n mlSource) : OracleComp (Spec n mlSource KemSK) Unit :=
  (Spec n mlSource KemSK).query (.inl (.put state))

def modify (change : State n mlSource → State n mlSource) : OracleComp (Spec n mlSource KemSK) Unit := do
  let before ← get
  put (change before)

noncomputable def primitive (checks : Checks) : QueryImpl RegistrationAgreementShared.PrimitiveSpec
    (OracleComp (Spec n mlSource KemSK)) :=
  lift ∘ₛ RegistrationNativeKemInterface.server checks

noncomputable def agreementCore (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Spec n mlSource KemSK))
  | .convertPublic key => primitive checks (.convertPublic key)
  | .convertSecret role => primitive checks (.convertSecret role)
  | .generate role => primitive checks (.generate role)
  | .encapsulate key => primitive checks (.encapsulate key)
  | .decapsulate ciphertext => primitive checks (.decapsulate ciphertext)
  | .dh request => primitive checks (.dh request)
  | .root request => pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))

noncomputable def agreement (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Spec n mlSource KemSK)) := fun query => do
  modify fun state => { state with server := { state.server with world :=
    { state.server.world with requests := state.server.world.requests ++ RegistrationWorldAgreement.recorded query } } }
  agreementCore setup checks query

/-- This is the literal SDK authentication, owned replay lookup, reservation, native agreement and one-use retention order. -/
noncomputable def accept (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) : OracleComp (Spec n mlSource KemSK) (RustM (Option Nat)) := do
  let checked ← (Spec n mlSource KemSK).query (.inl (.authenticate packet))
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) =>
      let before ← get
      if before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
      else if checks.reserveRegistration then do
        let completed ← simulateQ (agreement setup checks)
          (RegistrationReplaySchedule.begin before.server.control authenticated before.server.consumed)
        match completed with
        | .fail error => pure (.fail error)
        | .div => pure .div
        | .ok (.ServerComplete accepted) => (Spec n mlSource KemSK).query (.inl (.retain accepted))
        | .ok _ => pure (.ok none)
      else pure (.ok none)
  | .ok _ => pure (.ok none)

/-- Parsed accept attempts advance before every authentication or replay failure; this is not a KEM-getter counter. -/
noncomputable def typedAccept (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) : OracleComp (Spec n mlSource KemSK) (RustM (Option Nat)) := do
  modify fun state => { state with parsedAccepts := state.parsedAccepts + 1 }
  accept setup checks packet

end BeaconcryptCore.Computational.RegistrationNativeKemServerInterface
