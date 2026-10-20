-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization
import BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping

/-! The actual open registration command program uses the ordinary selected-key CCA router. Selected challenge ciphertexts stay blocked, original optional replies and complete state remain, and successful selected-secret reveals are explicit stops with an exact original-history interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option linter.deprecated false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting
open PqxdhKemIndCca PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointKemCommands (SourceSpec Budget program Outcome)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhDynamicKemJointSource (State)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Executable prechallenge source command wrapper with no separate selected-secret argument. The source comparison supplies the redacted reservation; other private keys remain local at their exact creation positions. -/
noncomputable def pre (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (state : State KemSK) :=
  (((simulateQ (PqxdhDynamicKemJointRouter.pre setup.joint setup.kem selected reservation)
    (program setup codec checks identityIndex publicIdentity client owners native)).run).run state)

/-- Executable postchallenge command wrapper. The supplied KEM candidate is used only inside the source client; all selected nonchallenge decapsulation queries still use the ordinary CCA interface. -/
noncomputable def post (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (state : State KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :=
  (((simulateQ (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected reservation challenge candidate)
    (program setup codec checks identityIndex publicIdentity client owners native)).run).run state)

/-- The complete real prechallenge wrapper is exactly the stopped actual source program, including native/owner poststate and all identity/KEM histories. Only the mathematical CCA interpreter receives the selected secret. -/
theorem pre_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret)) (state : State KemSK) :
    PqxdhPrivateKemSource.evalKem setup.baseImpl setup.kem secret
      (pre setup codec checks identityIndex publicIdentity client owners native selected
        (PqxdhDynamicKemRouter.redact selected pairs) state) =
      (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (program setup codec checks identityIndex publicIdentity client owners native)).run).run state) :=
  PqxdhDynamicKemJointRouter.pre_program setup.baseImpl setup.joint setup.kem selected pairs target secret present
    (program setup codec checks identityIndex publicIdentity client owners native) state

/-- Existing functional decapsulation and recipient correctness at the actual generated/encapsulated support discharge the complete real postchallenge equality. No challenge ciphertext is sent to the blocked CCA oracle. -/
theorem post_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (correct : MlKem768RecipientCorrectness setup.kem
      (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)))
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret)) (state : State KemSK)
    (generated : (target, secret) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (encapsulated : (challenge, candidate) ∈ support
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps target))) :
    PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem secret challenge
      (post setup codec checks identityIndex publicIdentity client owners native selected
        (PqxdhDynamicKemRouter.redact selected pairs) state challenge candidate) =
      (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (program setup codec checks identityIndex publicIdentity client owners native)).run).run state) :=
  PqxdhDynamicKemJointRouter.supported_post setup.baseImpl setup.joint setup.kem functional correct selected pairs
    target secret present generated challenge candidate encapsulated
    (program setup codec checks identityIndex publicIdentity client owners native) state

/-- For the concrete source command program, an actual successful selected-KEM disclosure is exactly the freshness stop. Missing or future handles retain their ordinary optional rejection and do not trigger it. Every event may inspect the complete returned command and private state. -/
theorem fresh_pre_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret)) (joint : PqxdhDynamicIdentityPool.SourceState)
    (event : Option (Outcome KemSK Result) × State KemSK → Prop) :
    Pr[fun result => event result ∧ result.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected) = false |
      ((simulateQ (PqxdhDynamicKemJointSource.normal setup.baseImpl setup.joint setup.kem selected pairs)
        (program setup codec checks identityIndex publicIdentity client owners native)).run).run
          (joint, PqxdhDynamicKemRouter.empty)] =
      Pr[fun result => event result ∧ PqxdhDynamicKemJointStopping.Good result.2 |
        PqxdhPrivateKemSource.evalKem setup.baseImpl setup.kem secret
          (pre setup codec checks identityIndex publicIdentity client owners native selected
            (PqxdhDynamicKemRouter.redact selected pairs) (joint, PqxdhDynamicKemRouter.empty))] :=
  PqxdhDynamicKemJointStopping.pre_event_vcvioLegacy setup.baseImpl setup.joint setup.kem selected pairs target secret present
    (program setup codec checks identityIndex publicIdentity client owners native) joint event

/-- Every prechallenge source finish attempt costs at most one selected logical CCA decapsulation; source rejection and arbitrary optional replies do not increase the cap. -/
theorem pre_decapsulations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (state : State KemSK) :
    (pre setup codec checks identityIndex publicIdentity client owners native selected reservation state).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery (budget (.inl 5)) :=
  PqxdhDynamicKemJointBounds.pre_decaps setup.joint setup.kem selected reservation
    (program setup codec checks identityIndex publicIdentity client owners native) (budget (.inl 5))
    (PqxdhRegistrationJointKemCommands.decapsulations setup codec checks identityIndex publicIdentity
      client budget certified owners native) state

/-- The concrete postchallenge program keeps the same source finish cap while never forwarding the exact selected challenge ciphertext. -/
theorem post_decapsulations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (state : State KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    (post setup codec checks identityIndex publicIdentity client owners native selected reservation state challenge candidate).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery (budget (.inl 5)) :=
  PqxdhDynamicKemJointBounds.post_decaps setup.joint setup.kem selected reservation challenge candidate
    (program setup codec checks identityIndex publicIdentity client owners native) (budget (.inl 5))
    (PqxdhRegistrationJointKemCommands.decapsulations setup codec checks identityIndex publicIdentity
      client budget certified owners native) state

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.pre_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.pre_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.post_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.post_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.fresh_pre_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.fresh_pre_event

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.pre_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.pre_decapsulations

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.post_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting.post_decapsulations
