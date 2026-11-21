-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicFrontend
import BeaconcryptCore.Computational.RegistrationNativeCommonCompiler
import BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter
import BeaconcryptCore.Computational.RegistrationServerStartup
import BeaconcryptCore.Computational.CborRecordWorldSimulation

/-! This concrete first-hop interpreter runs the complete public reference frontend with one record World, one actual private generated KEM pool and actual local ML signing. Only native root preparation reaches the related-root interface; material is computed later from its retained returned root. The executable client never receives selected identity/prekey bytes or a private input classifier. It is the public reference experiment, not an asserted equality to the original source startup: the latter must prove its discarded dummy draws and permitted-state projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicInterpreter
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeRelatedRoot (RootSpec)
open RegistrationNativeWire (Wire ledgerCodec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

structure State (n : Nat) (KemSK : Type) where
  roots : RegistrationNativeReferenceInterpreter.State
  world : PqxdhRecordLiftWorld.State n
  pool : PqxdhLiveKemBirth.Pool KemSK
  receipts : List RegistrationSigningShared.Receipt

noncomputable def initial : State n KemSK :=
  ⟨RegistrationNativeReferenceInterpreter.initial, PqxdhRecordLiftWorld.initial, PqxdhLiveKemBirth.empty, []⟩

abbrev M (n : Nat) (KemSK Value : Type) := StateT (State n KemSK) (OracleComp RootSpec) Value

def coins : QueryImpl unifSpec (OracleComp RootSpec) := fun query => RootSpec.query (.inl query)

def world {Result : Type} (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Result) : M n KemSK Result := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$> simulateQ coins (work.run before.world)

noncomputable def effect (query : (EnvEffects n).Domain) : M n KemSK ((EnvEffects n).Range query) :=
  world (PqxdhRecordLiftWorld.effects query)

noncomputable def publication (setup : Setup base KemSK) (wire : Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBoundPublication.Spec (M n KemSK) := fun query => do
  let before ← get
  let result ← simulateQ effect ((RegistrationBoundSourceCompiler.compiler setup.source (ledgerCodec wire).frameWrite sign query).run before.receipts)
  modify fun current => { current with receipts := result.2 }
  pure result.1

noncomputable def common (setup : Setup base KemSK) (wire : Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePairedServerService.Common n) (M n KemSK)
  | .inl query => publication setup wire sign query
  | .inr query => effect query

/-- The public client has no ordinary role callback outside its locally lowered controller. A malformed direct request still gets a fixed optional failure. -/
def unavailable : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp := fun query => by
  cases query with
  | convertSecret _ => exact pure false
  | convertPublic _ => exact pure .None
  | generate _ => exact pure .None
  | dh _ => exact pure .None

noncomputable def kem (setup : Setup base KemSK) :
    QueryImpl (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK) (M n KemSK)
  | .inl query => StateT.lift (simulateQ coins (unavailable query))
  | .inr (.inl query) => do
      let before ← get
      let result ← world (PqxdhRecordLiftWorld.sampled
        ((PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run before.pool))
      modify fun current => { current with pool := result.2 }
      pure result.1
  | .inr (.inr key) => world (PqxdhRecordLiftWorld.sampled
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)))

/-- Material demand uses only the previously returned root, without evaluating the private input or its protection. -/
noncomputable def routedKem (setup : Setup base KemSK) :
    QueryImpl (RegistrationNativePublicFrontend.RoutedKem KemSK) (M n KemSK)
  | .inl (.inl query) => kem setup (.inl query)
  | .inl (.inr key) => kem setup (.inr (.inr key))
  | .inr query => kem setup (.inr query)

noncomputable def handler (setup : Setup base KemSK) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (M n KemSK)
  | .inl (.inl message) => do
      let root ← StateT.lift (RootSpec.query (.inr (.derive message)))
      modify fun before => { before with roots := Function.update before.roots message root }
      pure (root.map (fun _ => message))
  | .inl (.inr (.inl (.inl message))) => do
      let before ← get
      pure ((before.roots message).map fun root => RegistrationNativePairedChoice.Choice.known
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root))
  | .inl (.inr (.inl (.inr query))) => common setup wire sign query
  | .inl (.inr (.inr query)) => routedKem setup query
  | .inr query => world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route (.inr (.inr query)))

/-- This is the full public-reference experiment, including the unchanged hidden-bit/fresh ledger and every ordinary role operation. -/
noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativePublicFrontend.State source) (before : State n KemSK) :
    OracleComp RootSpec (((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) × State n KemSK) :=
  (simulateQ (handler setup wire route (RegistrationNativeMldsa.owned source credential))
    (RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work frontend)).run before

/-- The root-preparation query is reached at preparation, with the selected secrets absent from the interpreted client state. -/
theorem prepare_query (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (message : RegistrationNativeRelatedFamily.Message) (before : State n KemSK) :
    (handler setup wire route sign (.inl (.inl message))).run before = (do
      let root ← (RootSpec.query (.inr (.derive message)) : OracleComp RootSpec _)
      pure (root.map (fun _ => message), { before with roots := Function.update before.roots message root })) := by
  simp only [handler, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
    pure_bind]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePublicInterpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInterpreter.prepare_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInterpreter.prepare_query
