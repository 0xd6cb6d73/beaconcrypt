-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptStore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary
/-! The literal physical acceptance program ignores only the passive indexed KEM log. Its actual original agreement capture, source container calls and authentication hash all satisfy the quotient internally. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterPhysicalFrame
variable {n : Nat} {KemSK P R Error Value : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]

noncomputable section

theorem capture (coins : QueryImpl unifSpec (StateT P ProbComp)) (generator : rand_core.TryCryptoRng R Error)
    (keys : AdapterPublicAgreementFields.Keys) (work : OracleComp RegistrationAgreementExecutor.Spec Value) (rng : R) :
    Compatible (RegistrationNativePlatformPublicAdapterAcceptReceipt.capture (n:=n) (KemSK:=KemSK) coins generator keys work rng) :=
  interpret_frame coins _ (captured_frame generator keys work rng)

variable [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable (containers : ContainerOperations (RustT (StateT P ProbComp)))

theorem agreement (coins : QueryImpl unifSpec (StateT P ProbComp)) (generator : rand_core.TryCryptoRng R Error)
    (keys : AdapterPublicAgreementFields.Keys) (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect)) (rng : R) :
    Compatible (RegistrationNativePlatformPublicAdapterAcceptReceipt.program (n:=n) (KemSK:=KemSK) containers coins generator keys self work rng) :=by
  unfold RegistrationNativePlatformPublicAdapterAcceptReceipt.program
  apply bind_frame _ _ (capture coins generator keys work rng)
  intro receipt
  apply bind_frame _ _ (lift_frame _)
  intro returned
  exact pure_frame _

theorem reservation (coins : QueryImpl unifSpec (StateT P ProbComp)) (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.server.Server) (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) (rng : R) :
    Compatible (RegistrationNativePlatformPublicAdapterAcceptLookup.reservation (n:=n) (KemSK:=KemSK) containers coins generator self control authenticated rng) :=by
  unfold RegistrationNativePlatformPublicAdapterAcceptLookup.reservation
  dsimp only
  apply bind_frame _ _ (lift_frame _)
  intro allocated
  cases allocated with
  | fail error | div=>exact pure_frame _
  | ok pair=>
    rcases pair with ⟨outcome,history⟩
    cases outcome with
    | Err error=>exact pure_frame _
    | Ok allocated=>exact map_frame _ _ (agreement containers coins generator _ _ _ rng)

theorem lookup (coins : QueryImpl unifSpec (StateT P ProbComp)) (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.RegistrationLookup) (rng : R) :
    Compatible (RegistrationNativePlatformPublicAdapterAcceptLookup.lookup (n:=n) (KemSK:=KemSK) containers coins generator self pending rng) :=by
  unfold RegistrationNativePlatformPublicAdapterAcceptLookup.lookup
  dsimp only
  apply bind_frame _ _ (lift_frame _)
  intro observed
  cases observed with
  | fail error | div=>exact pure_frame _
  | ok present=>cases present with
    | true=>exact pure_frame _
    | false=>exact reservation containers coins generator self pending.control pending.authenticated rng

variable {I : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
omit material platform ed original [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem hash (bytes : Pqxdh.Bytes) :
    Compatible (RegistrationNativePlatformPublicAdapterAuthentication.hash (n:=n) setup checks representation created bytes) :=by
  intro before
  simp only [RegistrationNativePlatformPublicAdapterAuthentication.hash,RegistrationNativePlatformSdkReification.backendLeaf,
    StateT.run,RegistrationNativePlatformPublicAdapterPhysicalBackend.erase,Functor.map_map]
  rfl

omit material platform ed original [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem pinHash (request : RegistrationNativeServerPinRecompute.Spec.Domain) :
    Compatible (RegistrationNativePlatformPublicAdapterAuthentication.pinHash (n:=n) setup checks representation created request) :=by
  unfold RegistrationNativePlatformPublicAdapterAuthentication.pinHash
  apply bind_frame _ _ (hash setup checks representation created _)
  intro digest
  exact pure_frame _

omit material platform ed original [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem pin (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    Compatible (RegistrationNativePlatformPublicAdapterAuthentication.pin (n:=n) setup checks representation created binding publicKey) :=
  program_frame _ (pinHash setup checks representation created) _

omit material platform ed original [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem callbacks (verify : MldsaTranscriptAuth.Verify) (request : RegistrationAuthenticationExecutor.Spec.Domain) :
    Compatible (RegistrationNativePlatformPublicAdapterAuthentication.callbacks (n:=n) setup checks representation created verify request) :=by
  cases request with
  | hash request=>
    unfold RegistrationNativePlatformPublicAdapterAuthentication.callbacks
    apply bind_frame _ _ (hash setup checks representation created _)
    intro digest
    exact pure_frame _
  | mldsa request | ed25519 request=>exact pure_frame _

omit material platform ed original [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem authenticate (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Compatible (RegistrationNativePlatformPublicAdapterAuthentication.authenticate (n:=n) setup checks representation created verify pin packet) :=
  program_frame _ (callbacks setup checks representation created verify) _

omit material platform ed original [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem afterPin (verify : MldsaTranscriptAuth.Verify) (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (reply : RegistrationNativeServerPinRecompute.PinReply) :
    Compatible (RegistrationNativePlatformPublicAdapterAuthentication.afterPin (n:=n) setup checks representation created verify control packet reply) :=by
  cases reply with
  | fail error | div=>exact pure_frame _
  | ok pin=>cases pin with
    | none=>exact pure_frame _
    | some pin=>exact map_frame _ _ (authenticate setup checks representation created verify pin packet)

omit material platform ed original [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem authentication_prefix (verify : MldsaTranscriptAuth.Verify) (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (publicKey : Std.Array U8 1952#usize) (packet : registration.InitPacket) :
    Compatible (RegistrationNativePlatformPublicAdapterAuthentication.prefixProgram (n:=n) setup checks representation created verify control binding publicKey packet) :=by
  unfold RegistrationNativePlatformPublicAdapterAuthentication.prefixProgram
  apply bind_frame _ _ (pin setup checks representation created binding publicKey)
  intro reply
  exact afterPin setup checks representation created verify control packet reply

theorem program (coins : QueryImpl unifSpec (StateT P ProbComp)) (verify : MldsaTranscriptAuth.Verify)
    (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R) :
    Compatible (RegistrationNativePlatformPublicAdapterAccept.program (n:=n) containers coins setup checks verify representation created generator view self input rng) :=by
  unfold RegistrationNativePlatformPublicAdapterAccept.program
  cases decoded:RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>exact pure_frame _
  | some packet=>
    apply bind_frame _ _ (interpret_frame coins _ (authentication_prefix setup checks representation created verify _ _ _ packet))
    intro checked
    cases checked with
    | fail error | div=>exact pure_frame _
    | ok result=>cases result with
      | none=>exact pure_frame _
      | some pending=>exact lookup containers coins generator self pending rng

omit original [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem finish (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (before : RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)
    (result : RustM (RegistrationNativePlatformSdkAcceptInstrumentedSource.Word R)×(Backend n KemSK×P)) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize
      (RegistrationNativePlatformPublicAdapterAcceptStore.finish view views before result)=
      RegistrationNativePlatformPublicAdapterAcceptStore.finish view views
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before)
        (result.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent result.2) :=by
  rcases result with ⟨outcome,after⟩
  cases outcome <;>rfl

theorem run (coins : QueryImpl unifSpec (StateT P ProbComp)) (verify : MldsaTranscriptAuth.Verify)
    (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (input : Slice U8) (before : RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>
      RegistrationNativePlatformPublicAdapterAcceptStore.run containers coins setup checks verify representation created generator view views input before=
      RegistrationNativePlatformPublicAdapterAcceptStore.run containers coins setup checks verify representation created generator view views input
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) :=by
  let work:=RegistrationNativePlatformPublicAdapterAccept.program (n:=n) containers coins setup checks verify representation created generator view
    before.server input before.rng
  have held:=program (n:=n) containers setup checks representation created coins verify generator view before.server input before.rng before.backend.1
  have core:=congrArg (fun computation=>computation.run before.backend.2) held
  rw [StateT.run_map] at core
  unfold RegistrationNativePlatformPublicAdapterAcceptStore.run
  change RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>
    ((fun result=>RegistrationNativePlatformPublicAdapterAcceptStore.finish view views before
      (RegistrationNativePlatformSdkAcceptInstrumentedSource.reply result.1.1.1 result.1.1.2,(result.1.2,result.2))) <$>
      ((work.run before.backend.1).run before.backend.2))=
    (fun result=>RegistrationNativePlatformPublicAdapterAcceptStore.finish view views
      (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before)
      (RegistrationNativePlatformSdkAcceptInstrumentedSource.reply result.1.1.1 result.1.1.2,(result.1.2,result.2))) <$>
      ((work.run (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase before.backend.1)).run before.backend.2)
  rw [Functor.map_map,←core,Functor.map_map]
  congr 1
  funext result
  exact finish view views before _

end
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.capture
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.agreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.reservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.reservation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.lookup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.hash
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.pinHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.pinHash
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.callbacks
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.authenticate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.afterPin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.authentication_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.authentication_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalization.run
