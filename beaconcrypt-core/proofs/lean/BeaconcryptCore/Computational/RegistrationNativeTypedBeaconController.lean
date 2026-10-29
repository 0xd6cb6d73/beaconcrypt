-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFinishController
import BeaconcryptCore.Computational.RegistrationNativePublicFrontend

/-! The original scalar-free typed finish exposes the same local controller before any interpreter or observer is chosen. Consequently its successful preparation/completion cut retains arbitrary chronological instrumentation and the actual source runtime. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTypedBeaconController
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Runtime : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The scalar-free original typed finish is its literal original local AST before chronological observation. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (index : Nat) (packet : Option registration.ResponsePacket) (frontend : RegistrationNativePublicFrontend.State source)
    (owner : RegistrationNativePublicOwners.Owner source) (found : frontend.beacons[index]? = some owner) (hidden : owner.scalar = none) :
    (RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.finish index packet))).run frontend =
      (fun result => (result.1.1, { frontend with beacons := frontend.beacons.set index ({ owner with view := result.1.2 }), environment := result.2 })) <$>
        simulateQ (RegistrationNativePublicFrontend.liftLocal false)
          (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner.view).run frontend.environment) := by
  simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon,
    RegistrationNativePublicOwners.finish, found, hidden, StateT.run, simulateQ_map, Functor.map_map]


private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- A successful typed callback retains its same complete runtime in the corresponding original local finish. -/
theorem closed (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (index : Nat) (packet : Option registration.ResponsePacket) (frontend afterFrontend : RegistrationNativePublicFrontend.State source)
    (owner : RegistrationNativePublicOwners.Owner source) (found : frontend.beacons[index]? = some owner) (hidden : owner.scalar = none)
    (before after : Runtime) (application : Pqxdh.Bytes)
    (supported : ((.ok (some application), afterFrontend), after) ∈ support
      ((simulateQ implementation
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          (.inr (.finish index packet))).run frontend)).run before)) :
    ∃ afterOwner afterEnv,
      ((.ok (some application), afterOwner), (afterEnv, after)) ∈ support
        ((RegistrationNativeBeaconFinishController.lower (implementation ∘ₛ RegistrationNativePublicFrontend.liftLocal false)
          ((RegistrationBeaconReferenceFinish.finish setup source packet).run owner.view)).run (frontend.environment, before)) := by
  rw [finish_source setup checks wire sign selectedOwner selectedAccept publicPrekey index packet frontend owner found hidden] at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨finished, called, equal⟩ := supported
  have successful : finished.1.1.1 = .ok (some application) := congrArg (fun result => result.1.1) equal
  have runtime : finished.2 = after := congrArg Prod.snd equal
  refine ⟨finished.1.1.2, finished.1.2, ?_⟩
  simp only [RegistrationNativeBeaconFinishController.lower, StateT.run, support_map]
  refine ⟨finished, ?_, ?_⟩
  · simpa only [QueryImpl.simulateQ_compose, StateT.run] using called
  · exact Prod.ext (Prod.ext successful rfl) (Prod.ext rfl runtime)


/-- Successful original scalar-free typed finish supplies the same prepared Ready and subsequent completion under its complete runtime. -/
theorem finish (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (index : Nat) (packet : Option registration.ResponsePacket) (frontend afterFrontend : RegistrationNativePublicFrontend.State source)
    (owner : RegistrationNativePublicOwners.Owner source) (found : frontend.beacons[index]? = some owner) (hidden : owner.scalar = none)
    (before after : Runtime) (application : Pqxdh.Bytes)
    (supported : ((.ok (some application), afterFrontend), after) ∈ support
      ((simulateQ implementation
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          (.inr (.finish index packet))).run frontend)).run before)) :
    ∃ ready : RegistrationBeaconReferenceRoot.Ready,
    ∃ preparedOwner : RegistrationBeaconReferenceCompiler.SelectedOwner source,
    ∃ middle afterOwner afterEnv,
      ((.ok (some ready), preparedOwner), middle) ∈ support
        ((RegistrationNativeBeaconFinishController.lower (implementation ∘ₛ RegistrationNativePublicFrontend.liftLocal false)
          ((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner.view)).run (frontend.environment, before)) ∧
      ((.ok (some application), afterOwner), (afterEnv, after)) ∈ support
        ((RegistrationNativeBeaconFinishController.lower (implementation ∘ₛ RegistrationNativePublicFrontend.liftLocal false)
          ((RegistrationBeaconReferenceFinish.complete setup.source owner.view ready).run preparedOwner)).run middle) := by
  obtain ⟨afterOwner, afterEnv, completed⟩ := closed implementation setup checks wire sign selectedOwner selectedAccept publicPrekey
    index packet frontend afterFrontend owner found hidden before after application supported
  obtain ⟨ready, preparedOwner, middle, prepared, finished⟩ := RegistrationNativeBeaconFinishController.finish
    (implementation ∘ₛ RegistrationNativePublicFrontend.liftLocal false) setup source packet owner.view afterOwner application
    (frontend.environment, before) (afterEnv, after) completed
  exact ⟨ready, preparedOwner, middle, afterOwner, afterEnv, prepared, finished⟩

end BeaconcryptCore.Computational.RegistrationNativeTypedBeaconController

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTypedBeaconController.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTypedBeaconController.finish_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTypedBeaconController.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTypedBeaconController.closed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTypedBeaconController.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTypedBeaconController.finish
