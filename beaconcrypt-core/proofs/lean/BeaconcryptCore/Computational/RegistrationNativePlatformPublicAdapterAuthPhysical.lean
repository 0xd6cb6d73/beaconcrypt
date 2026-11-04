-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept
import BeaconcryptCore.Refinement.AdapterPublicWrapperPin
import BeaconcryptCore.Refinement.AdapterPublicServerAuthentication
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
private theorem map_apply {S A B :Type} {m :Type→Type} [Monad m] [LawfulMonad m]
    (f :A→B) (work :StateT S m A) (before :S) :
    (f <$>work) before=Prod.map f id <$>work before :=StateT.run_map f work before
variable {n :Nat} {I KemSK P :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable (coins :QueryImpl unifSpec (StateT P ProbComp))
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created Unit)
variable (verify :MldsaTranscriptAuth.Verify)
local notation "PhysicalM"=>StateT (Backend n KemSK) (StateT P ProbComp)

noncomputable def core :QueryImpl RegistrationAuthenticationExecutor.Spec PhysicalM :=
  fun query=>RegistrationNativePlatformInterpret.state coins
    (RegistrationNativePlatformPublicAdapterAuthentication.callbacks setup checks representation created verify query)

variable [ed :AdapterInitEdPrimitive.Operations]
variable (edLaws :RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
noncomputable def native :QueryImpl AdapterInitAuthenticationStateful.NativeSpec PhysicalM
  | .inl query=>core coins setup checks representation created verify query
  | .inr (.parse input)=>pure (edLaws.parse input)
  | .inr (.open signed key)=>pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto ⟨edLaws.publicKey key,signed⟩)

theorem opened (request :registration.Ed25519VerificationRequest) :
    simulateQ (native (n:=n) coins setup checks representation created verify edLaws) (AdapterInitAuthenticationStateful.opened request)=
      pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto request) :=by
  simp only [AdapterInitAuthenticationStateful.opened,simulateQ_bind,simulateQ_spec_query,native,pure_bind]
  cases parsed:edLaws.parse (Std.Array.to_slice request.public_key) with
  | Err error=>
    have rejected:=edLaws.parseError (Std.Array.to_slice request.public_key) error parsed request.signed
    change setup.source.crypto.verify (PqxdhRefinement.absBytes request.public_key) (TranscriptAuthParts.absSlice request.signed)=none at rejected
    simp only [simulateQ_pure,RegistrationAuthenticationShared.verifyEd25519,rejected,RegistrationAuthenticationShared.openedBytes]
  | Ok key=>
    have bytes:=edLaws.parseKey (Std.Array.to_slice request.public_key) key parsed
    simp only [simulateQ_spec_query,native]
    unfold RegistrationAuthenticationShared.verifyEd25519
    rw [←bytes]
    rfl

theorem abstract_query (query :RegistrationAuthenticationExecutor.Spec.Domain) :
    (native (n:=n) coins setup checks representation created verify edLaws ∘ₛAdapterInitAuthenticationStateful.abstractNative) query=
      core coins setup checks representation created verify query :=by
  cases query with
  | hash request | mldsa request=>
    simp only [QueryImpl.apply_compose,AdapterInitAuthenticationStateful.abstractNative,simulateQ_spec_query,native]
  | ed25519 request=>
    rw [QueryImpl.apply_compose,AdapterInitAuthenticationStateful.abstractNative,opened]
    funext before
    simp only [core,RegistrationNativePlatformInterpret.state,RegistrationNativePlatformPublicAdapterAuthentication.callbacks,
      StateT.run_pure,simulateQ_pure]
    rfl

theorem afterPin (control :pqxdh.ServerState) (packet :registration.InitPacket)
    (reply :RegistrationNativeServerPinRecompute.PinReply) :
    AdapterPublicServerAuthentication.afterPin (native (n:=n) coins setup checks representation created verify edLaws) control packet reply=
      RegistrationNativePlatformInterpret.state coins
        (RegistrationNativePlatformPublicAdapterAuthentication.afterPin setup checks representation created verify control packet reply) :=by
  cases reply with
  | fail error | div=>rfl
  | ok optional=>cases optional with
    | none=>rfl
    | some pin=>
      have abstracted :native (n:=n) coins setup checks representation created verify edLaws ∘ₛAdapterInitAuthenticationStateful.abstractNative=
        core coins setup checks representation created verify :=by
        funext query
        exact abstract_query coins setup checks representation created verify edLaws query
      unfold AdapterPublicServerAuthentication.afterPin RegistrationNativePlatformPublicAdapterAuthentication.afterPin
      rw [abstracted]
      unfold core RegistrationNativePlatformPublicAdapterAuthentication.authenticate
      dsimp only
      rw [←RegistrationNativePlatformInterpret.state_simulate]
      funext before
      simp only [map_apply,RegistrationNativePlatformInterpret.state,StateT.run_map,simulateQ_map]
      rfl

variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [crypto :CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp)))]
variable [localOps :LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp)))]
variable {E :Type}
variable (recording :QueryImpl AdapterRecordRequestMonad.Spec (StateT (Backend n KemSK) (StateT P ProbComp)))
variable (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT (Backend n KemSK) (StateT P ProbComp)))

@[instance_reducible] noncomputable def children :ChildOperations (RustT PhysicalM):=
  AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication (native coins setup checks representation created verify edLaws)) recording writer

omit material platform crypto localOps in
theorem hash_child (request :registration.HashRequest) :
    ((children (n:=n) coins setup checks representation created verify edLaws recording writer).executeHash request).run=
      RegistrationNativePlatformInterpret.state coins
        (RegistrationNativePlatformPublicAdapterAuthentication.pinHash setup checks representation created request) :=by
  change (AdapterPublicWrapperChildNative.normalAuthentication
    (native (n:=n) coins setup checks representation created verify edLaws)) (.hash request)=_
  simp only [AdapterPublicWrapperChildNative.normalAuthentication,QueryImpl.apply_compose,
    AdapterInitAuthenticationStateful.native,simulateQ_map,simulateQ_spec_query,native]
  unfold core RegistrationNativePlatformInterpret.state RegistrationNativePlatformPublicAdapterAuthentication.callbacks
    RegistrationNativePlatformPublicAdapterAuthentication.pinHash
  funext before
  simp only [map_apply,bind_pure_comp,simulateQ_map,StateT.run_map,Functor.map_map]
  rfl

variable (view :AdapterPublicWrapperState.MaterialView source KemSK)
variable (edGetter :∀key,(crypto.edPublicBytes key).run=pure (.ok (view.edPublic key)))
variable (mlGetter :∀identity,(localOps.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))

include edGetter mlGetter in
theorem pin (self :beaconcrypt_public_wrapper.server.Server) :
    let :ChildOperations (RustT PhysicalM):=children coins setup checks representation created verify edLaws recording writer
    (beaconcrypt_public_request.server.Server.authentication_pin (m:=RustT PhysicalM) self).run=
      fun before=>simulateQ coins ((RegistrationNativePlatformPublicAdapterAuthentication.pin setup checks representation created
        (RegistrationNativePlatformPublicAdapterAccept.binding view self)
        (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey).run before) :=by
  let :ChildOperations (RustT PhysicalM):=children coins setup checks representation created verify edLaws recording writer
  dsimp only
  have original:=AdapterPublicWrapperPin.server_program self
    (view.edPublic (platform.arcView self.identity).identity_key.public_key)
    (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey
    (fun request=>RegistrationNativePlatformInterpret.state coins
      (RegistrationNativePlatformPublicAdapterAuthentication.pinHash setup checks representation created request))
    (edGetter (platform.arcView self.identity).identity_key.public_key)
    (mlGetter (platform.arcView self.identity).mldsa_identity)
    (hash_child coins setup checks representation created verify edLaws recording writer)
  exact original.trans (RegistrationNativePlatformInterpret.state_simulate coins
    (RegistrationNativePlatformPublicAdapterAuthentication.pinHash setup checks representation created)
    (RegistrationNativeServerPinRecompute.program (RegistrationNativePlatformPublicAdapterAccept.binding view self)
      (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey)).symm

include edGetter mlGetter in
theorem authenticate (self :beaconcrypt_public_wrapper.server.Server) (input :Slice U8) :
    letI :ChildOperations (RustT PhysicalM):=children coins setup checks representation created verify edLaws recording writer
    letI :Codecs (RustT PhysicalM):=AdapterPublicConcreteCodecs.codecs
    (AdapterPublicServerAcceptBody.authenticate (m:=PhysicalM) self input).run=
      match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
      | none=>pure (.ok .None)
      | some packet=>RegistrationNativePlatformInterpret.state coins
          (RegistrationNativePlatformPublicAdapterAuthentication.prefixProgram setup checks representation created verify self.control
            (RegistrationNativePlatformPublicAdapterAccept.binding view self)
            (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey packet) :=by
  let :ChildOperations (RustT PhysicalM):=children coins setup checks representation created verify edLaws recording writer
  let :Codecs (RustT PhysicalM):=AdapterPublicConcreteCodecs.codecs
  rw [AdapterPublicServerAuthentication.authenticate]
  cases decoded:RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>rfl
  | some packet=>
    rw [pin coins setup checks representation created verify edLaws recording writer view edGetter mlGetter self]
    unfold RegistrationNativePlatformPublicAdapterAuthentication.prefixProgram
    dsimp only
    rw [RegistrationNativePlatformInterpret.state_bind]
    apply bind_congr
    intro reply
    exact afterPin coins setup checks representation created verify edLaws self.control packet reply

include edGetter mlGetter in
theorem lookup_source (self :beaconcrypt_public_wrapper.server.Server) (input :Slice U8) :
    letI :ChildOperations (RustT PhysicalM):=children coins setup checks representation created verify edLaws recording writer
    letI :Codecs (RustT PhysicalM):=AdapterPublicConcreteCodecs.codecs
    (beaconcrypt_public_request.server.Server.authenticate_registration_lookup (m:=RustT PhysicalM) self input).run=
      match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
      | none=>pure (.ok .None)
      | some packet=>RegistrationNativePlatformInterpret.state coins
          (RegistrationNativePlatformPublicAdapterAuthentication.prefixProgram setup checks representation created verify self.control
            (RegistrationNativePlatformPublicAdapterAccept.binding view self)
            (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey packet) :=by
  let :ChildOperations (RustT PhysicalM):=children coins setup checks representation created verify edLaws recording writer
  let :Codecs (RustT PhysicalM):=AdapterPublicConcreteCodecs.codecs
  rw [AdapterPublicServerAcceptBody.authenticate_source]
  exact authenticate coins setup checks representation created verify edLaws recording writer view edGetter mlGetter self input

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.opened' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.opened
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.abstract_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.abstract_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.afterPin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.hash_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.hash_child
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.authenticate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.lookup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical.lookup_source
