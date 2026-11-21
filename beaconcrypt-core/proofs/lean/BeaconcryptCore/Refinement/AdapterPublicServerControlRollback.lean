-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildBody
import BeaconcryptCore.Refinement.AdapterPublicServerInstall
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Every rejected normal return from the actual enclosing Server builder retains its original allocation control. Arbitrary primitive/container/allocator failures and updated external poststates remain in the computation. This proof covers malformed moved tokens and every earlier rejection without a parsing or normality premise. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerControlRollback
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerBuildBody
variable {State A : Type}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [localOps : LocalOperations (RustT (StateT State ProbComp))]
variable [crypto : CryptoOperations (RustT (StateT State ProbComp))]
variable [containers : ContainerOperations (RustT (StateT State ProbComp))]
variable [children : ChildOperations (RustT (StateT State ProbComp))]

omit localOps crypto containers children [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
def Safe (control : pqxdh.ServerState) (work : RustT (StateT State ProbComp) Reply) : Prop :=
  ∀ before after current, (.ok (.None, current), after) ∈ support ((work.run).run before) → current.control = control

omit localOps crypto containers children [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem bind_safe (control : pqxdh.ServerState) (action : RustT (StateT State ProbComp) A)
    (next : A → RustT (StateT State ProbComp) Reply) (safe : ∀ input, Safe control (next input)) :
    Safe control (action >>= next) := by
  intro before after current supported
  simp only [RustT.run_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, middle⟩, _reached, continued⟩ := supported
  cases reply with
  | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok value => exact safe value middle after current continued

omit localOps crypto containers children [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem none_safe (self : Server) : Safe (State := State) self.control (pure (.None, self)) := by
  intro before after current supported
  simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, RustM.ok.injEq] at supported
  cases supported.1.2
  rfl

omit localOps crypto containers children [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem checked_safe (self : Server) {Error : Type} (work : RustM (core.result.Result A Error))
    (next : A → RustT (StateT State ProbComp) Reply) (safe : ∀ input, Safe self.control (next input)) :
    Safe self.control (checked self work next) := by
  apply bind_safe
  intro result
  cases result with
  | Err error => exact none_safe self
  | Ok input => exact safe input

omit localOps crypto containers children [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem finish_safe (self : Server) (completion : peer.PublicationFinish (alloc.vec.Vec U8)) (inserted : Bool) :
    Safe (State := State) self.control (finish self completion inserted) := by
  rw [AdapterPublicServerInstall.finish]
  cases inserted with
  | false => exact none_safe self
  | true =>
    intro before after current supported
    simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, RustM.ok.injEq, ite_true, reduceCtorEq, false_and] at supported

omit localOps crypto children in
private theorem install_safe (self : Server) (pending : peer.PeerInsert (alloc.vec.Vec U8)) :
    Safe (State := State) self.control (install self pending) := by
  unfold install
  apply bind_safe
  intro identifier
  apply bind_safe
  rintro ⟨remote, completion⟩
  apply bind_safe
  intro binding
  apply bind_safe
  intro identity
  apply checked_safe
  intro publicKey
  apply bind_safe
  rintro ⟨entry, back⟩
  cases entry with
  | Occupied selected => exact finish_safe _ completion false
  | Vacant selected =>
    apply bind_safe
    intro stored
    apply bind_safe
    rintro ⟨changed, insertedBack⟩
    exact finish_safe _ completion true

omit localOps crypto in
private theorem publish_safe (self : Server) (pending : registration.ServerResponseReady) :
    Safe (State := State) self.control (publish self pending) := by
  unfold publish
  apply bind_safe
  intro message
  apply bind_safe
  intro buffer
  apply checked_safe
  intro published
  apply checked_safe
  exact install_safe self

omit crypto in
private theorem sign_safe (self : Server) (pending : registration.ServerResponseHash) :
    Safe (State := State) self.control (sign self pending) := by
  unfold sign
  apply bind_safe
  intro request
  apply bind_safe
  intro hash
  apply checked_safe
  intro signing
  apply bind_safe
  intro identity
  apply bind_safe
  intro request
  apply bind_safe
  intro signature
  apply bind_safe
  intro signatureView
  apply checked_safe
  exact publish_safe self

omit crypto in
private theorem write_safe (self : Server) (pending : registration.ServerRecordWrite) :
    Safe (State := State) self.control (write self pending) := by
  unfold write
  apply bind_safe
  intro request
  apply bind_safe
  intro ciphertext
  apply bind_safe
  intro ciphertextView
  apply checked_safe
  exact sign_safe self

omit crypto in
private theorem commitment_safe (self : Server) (pending : registration.ServerRecordCommitment) :
    Safe (State := State) self.control (commit self pending) := by
  unfold commit
  apply bind_safe
  rintro ⟨transcript, back⟩
  apply bind_safe
  rintro ⟨digest, updated⟩
  apply checked_safe
  exact write_safe self

omit crypto in
private theorem sealing_safe (self : Server) (pending : registration.ServerRecordAead) :
    Safe (State := State) self.control (sealRecord self pending) := by
  unfold sealRecord
  apply bind_safe
  intro request
  apply bind_safe
  intro detached
  apply bind_safe
  intro view
  apply bind_safe
  intro borrowed
  apply checked_safe
  exact commitment_safe self

omit crypto in
private theorem record_safe (self : Server) (pending : registration.ServerInitialKdf) :
    Safe (State := State) self.control (record self pending) := by
  unfold record
  apply bind_safe
  intro request
  apply bind_safe
  intro bytes
  apply bind_safe
  intro response
  apply checked_safe
  intro initialSeal
  apply bind_safe
  intro request
  apply bind_safe
  intro response
  apply checked_safe
  exact sealing_safe self

omit crypto in
private theorem reserved_safe (self : Server) (pending : registration.ServerInitialKdf) :
    Safe (State := State) self.control (reserved self pending) := by
  unfold reserved
  apply bind_safe
  rintro ⟨allocation, known⟩
  cases allocation with
  | Err error => exact none_safe { self with known_ids := known }
  | Ok unitValue => exact record_safe { self with known_ids := known } pending

omit crypto in
private theorem adHash_safe (self : Server) (pending : registration.ServerAdHash) :
    Safe (State := State) self.control (adHash self pending) := by
  unfold adHash
  apply bind_safe
  intro request
  apply bind_safe
  intro digest
  apply checked_safe
  exact reserved_safe self

omit crypto in
private theorem lookup_safe (self : Server) (pending : peer.CompletionLookup) (plaintext : Slice U8) :
    Safe (State := State) self.control (lookup self pending plaintext) := by
  unfold lookup
  apply bind_safe
  intro identifier
  apply bind_safe
  intro size
  apply bind_safe
  intro admitted
  cases admitted with
  | none => exact none_safe _
  | some length =>
    apply bind_safe
    intro occupied
    apply checked_safe
    exact adHash_safe self

theorem build (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) : Safe (State := State) self.control (AdapterPublicServerBuildBody.build self token data) := by
  unfold AdapterPublicServerBuildBody.build
  apply bind_safe
  intro application
  apply bind_safe
  intro plaintext
  apply bind_safe
  intro pin
  cases pin with
  | none => exact none_safe _
  | some pin =>
    apply checked_safe
    intro pending
    exact lookup_safe self pending plaintext

theorem actual (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (current : Server) (before after : State)
    (supported : (.ok (.None, current), after) ∈ support
      (((beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m := RustT (StateT State ProbComp)) self token data).run).run before)) : current.control = self.control := by
  rw [AdapterPublicServerBuildBody.source] at supported
  exact build self token data before after current supported
end BeaconcryptCore.Refinement.AdapterPublicServerControlRollback

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerControlRollback.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerControlRollback.build

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerControlRollback.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerControlRollback.actual
