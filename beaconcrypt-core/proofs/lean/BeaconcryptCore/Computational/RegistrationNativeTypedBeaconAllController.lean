-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTypedBeaconController
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryCompletion

/-! Every original typed owner finish exposes the same actual local controller, including ordinary-owner preparation translation. Its complete runtime retains chronological observation, while terminal completion uses the already translated Ready unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {n : Nat} {ι KemSK Runtime Auxiliary Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

noncomputable def translated (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) :=
  match scalar with
  | none => work
  | some scalar => simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work

noncomputable def interpreter (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT Runtime ProbComp) :=
  match scalar with
  | none => implementation ∘ₛ RegistrationNativePublicFrontend.liftLocal false
  | some scalar => (implementation ∘ₛ RegistrationNativePublicFrontend.liftLocal false) ∘ₛ
      RegistrationNativePublicOwners.ordinary setup scalar

/-- The original typed owner callback exposes the literal preparation translation before any observer is chosen. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (index : Nat) (packet : Option registration.ResponsePacket) (frontend : RegistrationNativePublicFrontend.State source)
    (owner : RegistrationNativePublicOwners.Owner source) (found : frontend.beacons[index]? = some owner) :
    (RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.finish index packet))).run frontend =
      (fun result => (result.1.1, { frontend with beacons := frontend.beacons.set index ({ owner with view := result.1.2 }), environment := result.2 })) <$>
        simulateQ (RegistrationNativePublicFrontend.liftLocal false)
          (translated setup owner.scalar
            (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner.view).run frontend.environment)) := by
  simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon,
    RegistrationNativePublicOwners.finish, found, translated, StateT.run, simulateQ_map, Functor.map_map]
  rfl

/-- Every successful typed owner callback retains its same complete runtime in its original local finish. -/
theorem closed (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (index : Nat) (packet : Option registration.ResponsePacket) (frontend afterFrontend : RegistrationNativePublicFrontend.State source)
    (owner : RegistrationNativePublicOwners.Owner source) (found : frontend.beacons[index]? = some owner)
    (before after : Runtime) (application : Pqxdh.Bytes)
    (supported : ((.ok (some application), afterFrontend), after) ∈ support
      ((simulateQ implementation
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          (.inr (.finish index packet))).run frontend)).run before)) :
    ∃ afterOwner afterEnv,
      ((.ok (some application), afterOwner), (afterEnv, after)) ∈ support
        ((RegistrationNativeBeaconFinishController.lower (interpreter implementation setup owner.scalar)
          ((RegistrationBeaconReferenceFinish.finish setup source packet).run owner.view)).run (frontend.environment, before)) := by
  rw [finish_source setup checks wire sign selectedOwner selectedAccept publicPrekey index packet frontend owner found] at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨finished, called, equal⟩ := supported
  have successful : finished.1.1.1 = .ok (some application) := congrArg (fun result => result.1.1) equal
  have runtime : finished.2 = after := congrArg Prod.snd equal
  refine ⟨finished.1.1.2, finished.1.2, ?_⟩
  simp only [RegistrationNativeBeaconFinishController.lower, StateT.run, support_map]
  refine ⟨finished, ?_, ?_⟩
  · cases scalarEq : owner.scalar <;> simpa only [interpreter, translated, scalarEq, QueryImpl.simulateQ_compose, StateT.run] using called
  · exact Prod.ext (Prod.ext successful rfl) (Prod.ext rfl runtime)


/-- Ordinary-owner translation is already reflected in the Ready and does not change its terminal completion under any complete runtime. -/
theorem complete_source (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) :
    RegistrationNativeBeaconFinishController.lower (Auxiliary := Auxiliary) (interpreter implementation setup scalar)
        ((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current) =
      RegistrationNativeBeaconFinishController.lower (interpreter implementation setup none)
        ((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (interpreter implementation setup scalar)
        (((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current).run before.1)).run before.2 =
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (interpreter implementation setup none)
        (((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current).run before.1)).run before.2
  cases scalar with
  | none => rfl
  | some scalar =>
      simp only [interpreter, QueryImpl.simulateQ_compose, RegistrationNativeOrdinaryCompletion.complete]

/-- Every successful original typed owner finish supplies its own translated Ready and same subsequent completion, with the complete actual runtime retained. -/
theorem finish (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (index : Nat) (packet : Option registration.ResponsePacket) (frontend afterFrontend : RegistrationNativePublicFrontend.State source)
    (owner : RegistrationNativePublicOwners.Owner source) (found : frontend.beacons[index]? = some owner)
    (before after : Runtime) (application : Pqxdh.Bytes)
    (supported : ((.ok (some application), afterFrontend), after) ∈ support
      ((simulateQ implementation
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          (.inr (.finish index packet))).run frontend)).run before)) :
    ∃ ready : RegistrationBeaconReferenceRoot.Ready, ∃ preparedOwner : SelectedOwner source,
    ∃ middle afterOwner afterEnv,
      ((.ok (some ready), preparedOwner), middle) ∈ support
        ((RegistrationNativeBeaconFinishController.lower (interpreter implementation setup owner.scalar)
          ((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner.view)).run (frontend.environment, before)) ∧
      ((.ok (some application), afterOwner), (afterEnv, after)) ∈ support
        ((RegistrationNativeBeaconFinishController.lower (interpreter implementation setup none)
          ((RegistrationBeaconReferenceFinish.complete setup.source owner.view ready).run preparedOwner)).run middle) := by
  obtain ⟨afterOwner, afterEnv, completed⟩ := closed implementation setup checks wire sign selectedOwner selectedAccept publicPrekey
    index packet frontend afterFrontend owner found before after application supported
  obtain ⟨ready, preparedOwner, middle, prepared, finished⟩ := RegistrationNativeBeaconFinishController.finish
    (interpreter implementation setup owner.scalar) setup source packet owner.view afterOwner application
    (frontend.environment, before) (afterEnv, after) completed
  rw [complete_source] at finished
  exact ⟨ready, preparedOwner, middle, afterOwner, afterEnv, prepared, finished⟩

end BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController.finish_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController.closed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController.complete_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController.finish
