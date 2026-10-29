-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateGetter
import BeaconcryptCore.Computational.RegistrationNativeKemObservationProfile
import BeaconcryptCore.Computational.RegistrationNativeKemStartupApp

/-! The whole actual generated-startup uniform KEM hybrid derives an honest selected pair and the original broad native APP getter receipt. No supplied initial roster, parsed-counter, target-membership, cut-mark or whole-program simulation assumption remains. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidateStartup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeWire (Wire)
open PqxdhKemIndCca
variable {ι KemSK Value Output : Type} {base : OracleSpec ι} {n : Nat}

private theorem sampled_support (work : ProbComp Output) (before : PqxdhRecordLiftWorld.State n)
    (result : Output × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) : result.1 ∈ support work := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, called, returned⟩ := supported
  cases returned
  apply OracleComp.support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin work before.primitive.1.uniform
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst called

/-- Actual successful native startup derives its empty owner roster, zero parsed counter and literal configured Server identifier. -/
theorem start_facts (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    initial.state.beacons = [] ∧ initial.state.parsedAccepts = 0 ∧ initial.created.server.server.metadata.sender = serverKeyId := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, constructorSupport, continued⟩ := supported
  have actual := sampled_support
    ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ())
    (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n) constructed constructorSupport
  change (constructed.1.1, constructed.1.2) ∈ support _ at actual
  cases constructor : constructed.1.1 with
  | none => simp [constructor] at continued
  | some created =>
      rw [constructor] at actual
      obtain ⟨seed, literal, _imported⟩ := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit
        identityIndex serverKeyId none () constructed.1.2 created actual
      have sender : created.server.server.metadata.sender = serverKeyId := by rw [literal]; rfl
      simp only [constructor, mem_support_bind_iff] at continued
      obtain ⟨generated, _sampled, continued⟩ := continued
      cases generation : generated.1 with
      | none => simp [generation] at continued
      | some credential =>
          simp only [generation, mem_support_bind_iff] at continued
          obtain ⟨initialized, _native, returned⟩ := continued
          cases native : initialized.1 with
          | fail error | div => simp [native] at returned
          | ok reply => cases reply with
            | none => simp [native] at returned
            | some state =>
                simp only [native, support_pure, Set.mem_singleton_iff, Option.some.injEq] at returned
                cases returned
                exact ⟨rfl, rfl, sender⟩

/-- A win in the actual whole-startup uniform KEM hybrid derives a genuinely generated selected pair and the literal original broad APP getter-zero candidate receipt. -/
theorem winning_receipt (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (readback : RegistrationNativeWire.InitReadBack wire)
    (bounds : FreshBounds) (mode : Mode)
    (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (supported : true ∈ support (RegistrationNativeKemStartupApp.hybrid (n := n) setup checks wire route representation source ensureInit
      identityIndex serverKeyId bounds mode work budget target claim)) :
    ∃ initial chosen others record value ledger,
      some initial ∈ support (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) ∧
      chosen ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) ∧
      record ∈ support (RegistrationNativeKemCandidateObservation.run setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
        target.2 chosen others
        (RegistrationNativeKemFullSource.program setup checks wire initial.created.server.server.metadata.sender bounds mode
          (work initial.public) target.1.val) (RegistrationNativeKemServerState.project initial.state, PqxdhDynamicKemRouter.empty) 0 false) ∧
      record.value = some (value, ledger) ∧
      RegistrationNativeKemCandidateGetter.Receipt setup checks wire initial.created.server.server.metadata.sender budget target claim
        (RegistrationNativeKemOpenProvider.implementation setup checks wire route representation initial.created initial.credential
          target.2.val (List.ofFn (target.2.insertNth chosen others)) chosen.1 false)
        chosen.1 record.encapsulation.1 record.uniform record.finalState.1 value ledger := by
  obtain ⟨outcome, observed, observedSupport, returned, winning⟩ :=
    RegistrationNativeKemObservationProfile.winning_support setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget target.1.val target.2 0 (RegistrationNativeKemStartupApp.decision setup wire serverKeyId budget target claim)
        false supported
  simp only [RegistrationNativeKemObservationProfile.profile, mem_support_bind_iff] at observedSupport
  obtain ⟨initial, started, continued⟩ := observedSupport
  cases initial with
  | none =>
      simp only [mem_support_pure_iff, reduceCtorEq] at continued
  | some initial =>
      simp only [RegistrationNativeKemCandidateObservation.total, bind_assoc, pure_bind] at continued
      simp only [mem_support_bind_iff] at continued
      obtain ⟨chosen, generated, others, _sampled, record, recordSupport, terminal⟩ := continued
      simp only [mem_support_pure_iff, Option.some.injEq] at terminal
      cases terminal
      obtain ⟨value, ledger⟩ := observed
      have facts := start_facts setup source ensureInit identityIndex serverKeyId initial started
      have realWinning : RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto wire
          initial.created.server.server.metadata.sender budget target claim (value, (ledger, ())) := by
        simpa only [RegistrationNativeKemStartupApp.decision, RegistrationNativeParsedTargetCanonical.event,
          decide_eq_true_eq, facts.2.2] using winning
      refine ⟨initial, chosen, others, record, value, ledger, started, generated, recordSupport, returned, ?_⟩
      simpa only [RegistrationNativeKemCandidateGetter.Receipt, RegistrationNativeKemCandidateObservation.Record.candidate,
        Bool.false_eq_true, ite_false] using
        RegistrationNativeKemCandidateGetter.selected_getter setup checks wire route representation initial.created initial.credential
          readback bounds mode (work initial.public) budget target claim chosen others false
          (RegistrationNativeKemServerState.project initial.state) facts.2.1 facts.1 record recordSupport value ledger returned realWinning

end BeaconcryptCore.Computational.RegistrationNativeKemCandidateStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateStartup.start_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateStartup.start_facts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateStartup.winning_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateStartup.winning_receipt
