-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The literal SDK Server shell uses the same source map entry for AD and mutable ratchet selection. Narrow normal get/getMut contracts expose its one-key returned Self lens; the actual driver remains effectful and all fail/div and None outcomes retain their original poststates. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterRecordRequestMonad (liftRust)
open AdapterPublicWrapperStorage
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [ops : AdapterPublicOrdinaryRequestMonad.Operations (RustT m)]

universe u v w
omit [Monad m] [LawfulMonad m] material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem call_apply {X : Type u} {F : X → Type v} {G : X → Type w}
    [∀ x,AdapterPublicWrapperLiftFunction.LiftFunction (RustT m) (F x) (G x)]
    (source : (x : X) → F x) (value : X) :
    AdapterPublicWrapperLiftFunction.call (m:=RustT m) source value=
      AdapterPublicWrapperLiftFunction.call (m:=RustT m) (source value) := rfl
omit [LawfulMonad m] material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem call_result {A : Type} (source : RustM A) :
    AdapterPublicWrapperLiftFunction.call (m:=RustT m) source=(liftRust source :RustT m A) := rfl
omit [LawfulMonad m] material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem lifted_ok {A : Type} (value : A) : (liftRust (.ok value) :RustT m A)=pure value := rfl
omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem sender (self : beaconcrypt_public_wrapper.server.Server) :
    beaconcrypt_public_ordinary_request.server.Server.identity_key_kid (m:=RustT m) self=
      pure (platform.arcView self.identity).identity_key_kid := by
  unfold beaconcrypt_public_ordinary_request.server.Server.identity_key_kid
  simp only [call_apply,call_result,alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref,lifted_ok,pure_bind]

def sendAt (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) (key : U64)
    (selected : Option (Remote ed.PublicKey)) (back : Option (Remote ed.PublicKey) → PeerMap) :
    RustT m (Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.server.Server) :=
  match selected with
  | none=>pure (none,self)
  | some remote=>do
      let result←beaconcrypt_public_ordinary_request.ratchet.encrypt_message_with_ratchet bytes key
        (platform.arcView self.identity).identity_key_kid remote.peer.binding.associated_data remote.peer.ratchet
      pure (result.1,AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some result.2))

noncomputable def receiveAt (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) (key : U64)
    (selected : Option (Remote ed.PublicKey)) (back : Option (Remote ed.PublicKey) → PeerMap) :
    RustT m (Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.server.Server) :=
  match selected with
  | none=>pure (none,self)
  | some remote=>do
      let result←beaconcrypt_public_ordinary_request.ratchet.decrypt_message_with_ratchet bytes key
        remote.peer.binding.associated_data remote.peer.ratchet
      pure (result.1,AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some result.2))

theorem send_shell (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) (key : U64)
    (back : Option (Remote ed.PublicKey) → PeerMap)
    (get : AdapterPublicOrdinaryServerLookup.read (m:=m) self.known_ids key=pure (views.peer self.known_ids key))
    (borrow : AdapterPublicOrdinaryServerLookup.borrow (m:=m) self.known_ids key=pure (views.peer self.known_ids key,back)) :
    beaconcrypt_public_ordinary_request.server.Server.encrypt_message (m:=RustT m) self bytes key=
      sendAt self bytes key (views.peer self.known_ids key) back := by
  unfold beaconcrypt_public_ordinary_request.server.Server.encrypt_message
  rw [AdapterPublicOrdinaryServerLookup.associated_data views self key get]
  cases selected:views.peer self.known_ids key with
  | none=>
    simp only [Option.map_none,pure_bind,call_apply,call_result,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,lifted_ok,sendAt]
  | some remote=>
    simp only [Option.map_some,pure_bind,call_apply,call_result,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      sender,lifted_ok]
    rw [AdapterPublicOrdinaryServerLookup.manager_mut self key (views.peer self.known_ids key) back borrow]
    simp only [selected,Option.map_some,pure_bind,sendAt]

theorem receive_shell (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8)
    (back : U64 → Option (Remote ed.PublicKey) → PeerMap)
    (get : ∀key,AdapterPublicOrdinaryServerLookup.read (m:=m) self.known_ids key=pure (views.peer self.known_ids key))
    (borrow : ∀key,AdapterPublicOrdinaryServerLookup.borrow (m:=m) self.known_ids key=pure (views.peer self.known_ids key,back key)) :
    beaconcrypt_public_ordinary_request.server.Server.decrypt_message (m:=RustT m) self bytes=
      (do
        let routed←beaconcrypt_public_ordinary_request.ratchet.encrypted_frame_sender bytes
        match routed with
        | none=>pure (none,self)
        | some key=>receiveAt self bytes key (views.peer self.known_ids key) (back key)) := by
  unfold beaconcrypt_public_ordinary_request.server.Server.decrypt_message
    beaconcrypt_public_ordinary_request.server.Server.decrypt_message_transition
  simp only [bind_assoc]
  apply bind_congr
  intro routed
  cases routed with
  | none=>simp only [pure_bind,beaconcrypt_public_ordinary_request.server.ReceiveTransition.into_option]
  | some key=>
    dsimp only
    rw [AdapterPublicOrdinaryServerLookup.associated_data views self key (get key)]
    cases selected:views.peer self.known_ids key with
    | none=>
      simp only [Option.map_none,pure_bind,beaconcrypt_public_ordinary_request.server.ReceiveTransition.into_option,receiveAt]
    | some remote=>
      simp only [Option.map_some,pure_bind]
      rw [AdapterPublicOrdinaryServerLookup.manager_mut self key (views.peer self.known_ids key) (back key) (borrow key)]
      simp only [selected,Option.map_some,pure_bind,bind_assoc,receiveAt]
      apply bind_congr
      rintro ⟨received,manager⟩
      cases received <;>simp only [pure_bind,beaconcrypt_public_ordinary_request.server.ReceiveTransition.into_option]

omit [Monad m] [LawfulMonad m] material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] ops in
private theorem manager_eq (manager : Manager) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : manager.refined.kernel=some kernel) : manager=AdapterPublicOrdinaryEnvelope.manager kernel := by
  cases manager with
  | mk refined=>cases refined with
    | mk current=>cases stored;rfl

def sendKernel (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) (key : U64)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) → PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    RustT m (Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.server.Server) := do
  let prepared←(liftRust (AdapterPublicOrdinaryEnvelope.prepareSend bytes key
    (platform.arcView self.identity).identity_key_kid remote.peer.binding.associated_data kernel) :RustT m _)
  match prepared with
  | none=>pure (none,AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some (AdapterPublicOrdinaryEnvelope.manager kernel)))
  | some context=>do
      let sent←ops.send kernel context
      pure (sent.2,AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some (AdapterPublicOrdinaryEnvelope.manager sent.1)))

noncomputable def receiveKernel (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) (key : U64)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) → PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    RustT m (Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.server.Server) := do
  let prepared←(liftRust (AdapterPublicOrdinaryEnvelope.prepareReceive bytes key) :RustT m _)
  match prepared with
  | none=>pure (none,AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some (AdapterPublicOrdinaryEnvelope.manager kernel)))
  | some view=>do
      let effect←(liftRust (record_effects.begin_record_receive kernel view.sequence view.ciphertext remote.peer.binding.associated_data view.sender) :RustT m _)
      let received←ops.receive effect
      pure (received.2,AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some (AdapterPublicOrdinaryEnvelope.manager received.1)))

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem send_kernel (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) (key : U64)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) → PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel) :
    sendAt (m:=m) self bytes key (some remote) back=sendKernel (m:=m) self bytes key remote back kernel := by
  unfold sendAt
  dsimp only
  rw [manager_eq remote.peer.ratchet kernel stored,AdapterPublicOrdinaryEnvelope.send_frame]
  simp only [sendKernel,bind_assoc]
  apply bind_congr
  intro prepared
  cases prepared <;>simp only [pure_bind,bind_assoc]

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem receive_kernel (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) (key : U64)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) → PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel) :
    receiveAt (m:=m) self bytes key (some remote) back=receiveKernel (m:=m) self bytes key remote back kernel := by
  unfold receiveAt
  dsimp only
  rw [manager_eq remote.peer.ratchet kernel stored,AdapterPublicOrdinaryEnvelope.receive_frame]
  simp only [receiveKernel,bind_assoc]
  apply bind_congr
  intro prepared
  cases prepared <;>simp only [pure_bind,bind_assoc]

variable {P E I KemSK Reader Response : Type} {base : OracleSpec I}
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
variable (reserve : Nat → StateT P ProbComp (core.result.Result Unit E))
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
omit [Monad m] [LawfulMonad m] ops in
theorem server_send (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) (key : U64)
    (back : Option (Remote ed.PublicKey) → PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinary.M P) self.known_ids key=pure (views.peer self.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinary.M P) self.known_ids key=pure (views.peer self.known_ids key,back)) :
    letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve keyView failure erased
    RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup codec reserve keyView failure erased self bytes key=
      (sendAt (m:=RegistrationNativePlatformExtractedSdkOrdinary.M P) self bytes key (views.peer self.known_ids key) back).run := by
  let : AdapterPublicOrdinaryRequestMonad.Operations (RustT (RegistrationNativePlatformExtractedSdkOrdinary.M P)) := RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve keyView failure erased
  exact congrArg RustT.run (send_shell views self bytes key back get borrow)

omit [Monad m] [LawfulMonad m] ops in
theorem server_receive (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8)
    (back : U64 → Option (Remote ed.PublicKey) → PeerMap)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve keyView failure erased
      ∀key,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinary.M P) self.known_ids key=pure (views.peer self.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve keyView failure erased
      ∀key,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinary.M P) self.known_ids key=pure (views.peer self.known_ids key,back key)) :
    letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve keyView failure erased
    RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup codec reserve keyView failure erased self bytes=
      (do
        let routed←beaconcrypt_public_ordinary_request.ratchet.encrypted_frame_sender (m:=RustT (RegistrationNativePlatformExtractedSdkOrdinary.M P)) bytes
        match routed with
        | none=>pure (none,self)
        | some key=>receiveAt (m:=RegistrationNativePlatformExtractedSdkOrdinary.M P) self bytes key (views.peer self.known_ids key) (back key)).run := by
  let : AdapterPublicOrdinaryRequestMonad.Operations (RustT (RegistrationNativePlatformExtractedSdkOrdinary.M P)) := RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve keyView failure erased
  exact congrArg RustT.run (receive_shell views self bytes back get borrow)

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.send_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.send_shell

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.receive_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.receive_shell

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.send_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.send_kernel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.receive_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.receive_kernel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_receive
