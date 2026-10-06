-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileGame
import BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports

/-! The two internal reads of the compiled program leave every private history untouched (risk 2 of the common-experiment plan). In the annotated source14 execution that the KEM, root and report theorems are stated for, an established-kernel field read and a Server kernel reveal are pure steps that return the current kernel and keep the complete annotated state, including the private identity pool with its reveal transcript and the KEM pool with its transcript; the raw-accept report instrumentation emits no report for either read. Hence they disclose no identity seed or KEM secret in the sense of the existing freshness predicates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentReadHistory
open PqxdhServerAuthExperiment PqxdhJointIdentity
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- An established-kernel read in the annotated source14 execution returns the current established kernel field and keeps the whole annotated state, including both private pools and their transcripts. -/
theorem kernel_read (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (index : Nat) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex (.inr (index, .kernel))).run state =
      pure ((state.owners[index]?).bind fun entry =>
        PqxdhRegistrationJointLiveRead.localValue .kernel entry.owner, state) := by
  change pure (PqxdhRegistrationJointLiveRead.sourceStep (index, .kernel) state) = _
  cases found : state.owners[index]? with
  | none => simp only [PqxdhRegistrationJointLiveRead.sourceStep, found, Option.bind_none]
  | some entry => simp only [PqxdhRegistrationJointLiveRead.sourceStep, found, Option.bind_some,
      PqxdhRegistrationJointLiveRead.entrySource]

/-- A Server kernel reveal in the annotated source14 execution returns the installed kernel and keeps the whole annotated state, including both private pools and their transcripts. -/
theorem server_reveal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (kid : Std.U64) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex (.inl (.inr (.reveal kid)))).run
        state =
      pure ((state.shared.2.server.server.peers kid).map RawCtxServerRouting.Peer.kernel, state) := by
  rfl

/-- The raw-accept report instrumentation emits no report for an established-kernel read. -/
theorem kernel_unreported (codec : Codec Reader Response) (count index : Nat)
    (answer : Option (PqxdhRegistrationJointLiveRead.Value KemSK)) {κ : Type} {source : OracleSpec κ} :
    PqxdhRegistrationJointRawReports.report (KemSK := KemSK) codec count (.inr (index, .kernel)) answer
      (source := source) = pure () := rfl

/-- The raw-accept report instrumentation emits no report for a Server kernel reveal. -/
theorem reveal_unreported (codec : Codec Reader Response) (count : Nat) (kid : Std.U64)
    (answer : Option beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) {κ : Type} {source : OracleSpec κ} :
    PqxdhRegistrationJointRawReports.report (KemSK := KemSK) codec count (.inl (.inr (.reveal kid))) answer
      (source := source) = pure () := rfl

end BeaconcryptCore.Computational.PqxdhDeploymentReadHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReadHistory.kernel_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReadHistory.kernel_read

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReadHistory.server_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReadHistory.server_reveal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReadHistory.kernel_unreported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReadHistory.kernel_unreported

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentReadHistory.reveal_unreported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentReadHistory.reveal_unreported
