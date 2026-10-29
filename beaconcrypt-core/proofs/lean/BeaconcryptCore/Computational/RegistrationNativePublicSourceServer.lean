-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry

/-! The actual mixed frontend's Server operations use the same open native source interpretation. This is an exact state layout theorem before the separately named native metric view; it keeps the full opaque KEM pool, prepared-root memo and both receipt coordinates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceServer
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePublicSourceEffects (Private Extra close toPrivate)
open RegistrationNativePublicSourceCallbacks (remember services)
variable {n : Nat} {ι KemSK Value Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePublicFrontend.State source × RegistrationNativePublicInterpreter.State n KemSK

def layout (before : State n KemSK source) : RegistrationServerOpenReferenceSourceAccept.State n KemSK Extra :=
  (before.1.server, (before.1.environment, toPrivate before.2))

def rebuild (before : RegistrationNativePublicFrontend.State source)
    (after : RegistrationServerOpenReferenceSourceAccept.State n KemSK Extra) : State n KemSK source :=
  ({ before with server := after.1, environment := after.2.1 },
    RegistrationNativePublicSourceEffects.fromPrivate after.2.2)

noncomputable def run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) :
    StateT (State n KemSK source) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (close setup seed scalar
      (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign)
        ((RegistrationNativePublicFrontend.serverOpen selected work).run before.1))).run before.2

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

/-- Any adaptive Server operation in the actual mixed client has the exact existing native-source controller and full private state. -/
theorem server_layout (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : State n KemSK source) :
    Prod.map id layout <$> (run setup wire route sign seed scalar selected work).run before =
      (RegistrationServerOpenReferenceSourceAccept.close setup seed scalar remember
        (services setup wire route sign seed scalar) work).run (layout before) := by
  have native := RegistrationNativePublicSourceCallbacks.program_source setup wire route sign seed scalar selected
    ((work.run before.1.server).run before.1.environment) before.2
  apply congrArg (fun distribution => (fun result => (result.1.1.1,
    (result.1.1.2, (result.1.2, result.2)))) <$> distribution) at native
  simpa only [run, close, StateT.run, RegistrationNativePublicFrontend.serverOpen,
    simulateQ_map, state_map_apply, Functor.map_map, layout, Prod.map_def, id_eq,
    RegistrationServerOpenReferenceSourceAccept.close,
    RegistrationNativeKemReferencePrefix.lower,
    RegistrationNativePublicSourceCallbacks.implementation] using native

/-- The entire actual mixed-client Server accept, including all failed native branches, projects to the literal SDK source accept. -/
theorem accept_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (packet : registration.InitPacket) (before : State n KemSK source) :
    Prod.map id (RegistrationServerOpenReferenceSourceEntry.project setup created.seed scalar ∘ layout) <$>
      (run setup wire route sign created.seed scalar selected
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before =
      (RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run
        (RegistrationServerOpenReferenceSourceEntry.project setup created.seed scalar (layout before)) := by
  have native := congrArg (fun distribution => Prod.map id
      (RegistrationServerOpenReferenceSourceEntry.project setup created.seed scalar) <$> distribution)
    (server_layout setup wire route sign created.seed scalar selected
      (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet) before)
  have entry := RegistrationServerOpenReferenceSourceEntry.accept_native setup codec checks route verify
    representation correct created scalar remember (services setup wire route sign created.seed scalar) packet (layout before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using native.trans entry

end BeaconcryptCore.Computational.RegistrationNativePublicSourceServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceServer.server_layout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceServer.server_layout
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceServer.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceServer.accept_source
