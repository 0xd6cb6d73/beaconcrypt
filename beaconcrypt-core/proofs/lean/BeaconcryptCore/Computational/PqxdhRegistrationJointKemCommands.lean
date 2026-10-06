-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts
import BeaconcryptCore.Computational.PqxdhDynamicKemJointRouter
import BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds

/-! The existing selected-KEM construction is applied to the actual open registration command compiler. Every native field, owner, raw reply and local source draw remains in the complete continuation. Creation and decapsulation allowances come from the public source request ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option linter.deprecated false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointServiceCosts (poolClass)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

abbrev Budget := PqxdhRegistrationJointRevealCosts.SourceKind → Nat
abbrev SourceSpec (KemSK : Type) := PqxdhRegistrationJointRevealSchedule.Spec KemSK
abbrev Outcome (KemSK Result : Type) := (Result × List EncodedEntry) × NativeState KemSK

/-- Literal existing command compiler, retaining its complete owners and native poststate. Private pools are supplied only by the eventual interpreter. -/
noncomputable def program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    OracleComp (PqxdhLiveKemBirth.Spec KemSK) (Outcome KemSK Result) :=
  (PqxdhRegistrationJointOpenBackend.compile setup codec checks identityIndex publicIdentity
    (simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) client) owners).run state

/-- Every actual source creation attempts at most one indexed KEM creation, independently of all intermediate service replies, owner provenance and constructor success. -/
theorem creations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    (program setup codec checks identityIndex publicIdentity client owners state).IsQueryBoundP
      (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) (budget (.inl 1)) := by
  have cap := PqxdhRegistrationJointOpenCosts.command_program setup codec checks identityIndex publicIdentity
    client budget certified owners state .kemCreate (by decide)
  have kinds : (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) =
      (fun query => poolClass (KemSK := KemSK) query = .kemCreate) := by
    funext query
    rcases query with (coin | request) | (coin | request)
    case inl.inl => simp [PqxdhLiveKemReservation.IsCreate, poolClass]
    case inl.inr =>
      cases request <;> simp only [PqxdhLiveKemReservation.IsCreate, poolClass]
      case service index call => cases call <;> simp
      all_goals simp
    case inr.inl => simp [PqxdhLiveKemReservation.IsCreate, poolClass]
    case inr.inr => cases request <;> simp [PqxdhLiveKemReservation.IsCreate, poolClass]
  simpa only [program, kinds, PqxdhRegistrationJointOpenCosts.privateTotal] using cap

/-- Every actual attempted Beacon finish contributes at most one logical decapsulation, while all raw acceptance, malformed inputs and optional replies retain their original behavior. -/
theorem decapsulations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    (program setup codec checks identityIndex publicIdentity client owners state).IsQueryBoundP
      (PqxdhDynamicKemJointBounds.IsDecapsulation (KemSK := KemSK)) (budget (.inl 5)) := by
  have cap := PqxdhRegistrationJointOpenCosts.command_program setup codec checks identityIndex publicIdentity
    client budget certified owners state .decapsulate (by decide)
  have kinds : (PqxdhDynamicKemJointBounds.IsDecapsulation (KemSK := KemSK)) =
      (fun query => poolClass (KemSK := KemSK) query = .decapsulate) := by
    funext query
    rcases query with (coin | request) | (coin | request)
    case inl.inl => simp [PqxdhDynamicKemJointBounds.IsDecapsulation, poolClass]
    case inl.inr =>
      cases request <;> simp only [PqxdhDynamicKemJointBounds.IsDecapsulation, poolClass]
      case service index call => cases call <;> simp
      all_goals simp
    case inr.inl => simp [PqxdhDynamicKemJointBounds.IsDecapsulation, poolClass]
    case inr.inr => cases request <;> simp [PqxdhDynamicKemJointBounds.IsDecapsulation, PqxdhDynamicKemBounds.IsDecapsulation, poolClass]
  simpa only [program, kinds, PqxdhRegistrationJointOpenCosts.privateTotal] using cap

/-- The actual source-command program, including its full native/owner continuation, equals the selected-first monitored KEM source. The selected index is a creation position, with no honest owner, successful command or public-key uniqueness premise. -/
theorem selected_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (state : NativeState KemSK)
    (joint : PqxdhDynamicIdentityPool.SourceState) (count : Nat) (selected : Fin (count + 1))
    (room : budget (.inl 1) ≤ count + 1) :
    𝒮[(fun result => (some result.1, result.2)) <$>
      (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (program setup codec checks identityIndex publicIdentity client owners state)).run
          (joint, PqxdhLiveKemBirth.empty)] =
      𝒮[do
        let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
        let others ← PqxdhLiveKemSelection.sampleFamily
          (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
        let pairs := List.ofFn (selected.insertNth chosen others)
        Prod.map id (PqxdhDynamicKemJointSource.project pairs) <$>
          (((simulateQ (PqxdhDynamicKemJointSource.normal setup.baseImpl setup.joint setup.kem selected.val pairs)
            (program setup codec checks identityIndex publicIdentity client owners state)).run).run
              (joint, PqxdhDynamicKemRouter.empty))] := by
  exact PqxdhDynamicKemJointSource.selected_source setup.baseImpl setup.joint setup.kem
    (program setup codec checks identityIndex publicIdentity client owners state) count selected
    ((creations setup codec checks identityIndex publicIdentity client budget certified owners state).mono room) joint

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands.creations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands.creations

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands.decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands.decapsulations

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCommands.selected_source
