-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityClient
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionCosts
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityExecution

/-! The concrete suppressed clients retain the complete original all-reply resource matrix. Each selected bundle ordinal is a fixed member of a finite reduction family and adds no random query. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills
open PqxdhJointIdentity PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhDeploymentCompileCaps (transported compile_full_certified)
open PqxdhJointPhase1Reports (SourceClass)
open PqxdhDeploymentPublicationSuppressionCosts
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- Actual generated Server initialization and the full compiled adaptive source client, with one fixed suppression ordinal. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (ordinal : Nat) (runtime : A) :=
  PqxdhDeploymentPublicationSuppressionInitialized.sourceClient setup codec checks ensureInit none ordinal
    (compileFull setup codec route bounds mode adversary) runtime

/-- The terminal reports read only the complete execution's returned public transcript. -/
def transcript := @PqxdhDeploymentPublicationSuppressionInitialized.finalTranscript
  KemSK A (PqxdhDeploymentPublicationSecurityExecution.Result X)
  (fun result => result.1.2.transcript)

/-- The executable selected client followed by public accepted-candidate reports at every generated identity position. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (count ordinal : Nat) (runtime : A) :=
  PqxdhDeploymentPublicationSecurityClient.terminal codec (count + 1) transcript
    (source setup codec checks route ensureInit bounds mode adversary ordinal runtime)

/-- The original constructor and owner commands create at most the original generated identity capacity. -/
theorem creates (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (ordinal : Nat) (runtime : A) :
    (source setup codec checks route ensureInit bounds mode adversary ordinal runtime).IsQueryBoundP
      (SourceClass PqxdhDynamicIdentityPool.IsCreate) (budget.create + 1) := by
  simpa [source, transported, Nat.add_comm] using
    sourceClient_creates setup codec checks ensureInit none ordinal
      (compileFull setup codec route bounds mode adversary) runtime (transported bounds budget)
      (compile_full_certified setup codec route bounds mode adversary budget respects)

/-- Each selected client pays the unchanged signing and converted-DH caps on every typed reply. -/
theorem service (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (ordinal : Nat) (runtime : A) (signing : Bool) :
    (source setup codec checks route ensureInit bounds mode adversary ordinal runtime).IsQueryBoundP
      (SourceClass (PqxdhDynamicIdentityRouting.dynamicClass
        (PqxdhJointIdentityFamily.IsClass (if signing then .sign else .staticDh))))
      (if signing then 3 * budget.bundle else budget.finish + budget.accept) := by
  have bounded := sourceClient_private setup codec checks ensureInit none ordinal
    (compileFull setup codec route bounds mode adversary) runtime (transported bounds budget)
    (compile_full_certified setup codec route bounds mode adversary budget respects)
    (if signing then .signing else .staticDh) (by cases signing <;> decide)
  have converted := (isQueryBoundP_congr_pred
    (PqxdhRegistrationJointReportedAuthentication.service_class signing)).mp bounded
  cases signing <;> simpa [source, PqxdhRegistrationJointOpenCosts.privateTotal, transported] using converted

/-- No private identity or KEM field is exposed by the actual compiled selected client. -/
theorem unread (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (ordinal : Nat) (runtime : A) :
    (source setup codec checks route ensureInit bounds mode adversary ordinal runtime).IsQueryBoundP
      (SourceClass (fun query => PqxdhRegistrationJointIdentityCosts.dynamicKind query = .other)) 0 :=
  sourceClient_unread setup codec checks ensureInit none ordinal
    (compileFull setup codec route bounds mode adversary) runtime (transported bounds budget)
    (compile_full_certified setup codec route bounds mode adversary budget respects) (by rfl) (by rfl)

/-- Literal source coins, local KEM work and runtime initialization retain the full original syntactic uniform allowance. -/
theorem uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (ordinal : Nat) (runtime : A) :
    (source setup codec checks route ensureInit bounds mode adversary ordinal runtime).IsQueryBoundP
      (SourceClass (PqxdhDynamicIdentityRouting.dynamicClass (PqxdhJointIdentityFamily.IsClass .uniform)))
      (PqxdhRegistrationJointIdentityUniform.total caps qInit (transported bounds budget)) :=
  sourceClient_uniform setup codec checks ensureInit qInit initBound caps kemBound none ordinal
    (compileFull setup codec route bounds mode adversary) runtime (transported bounds budget)
    (compile_full_certified setup codec route bounds mode adversary budget respects)

/-- All ordinary joint-use reductions of the concrete selected client have the original per-client bills, including the reserved identity seeds and the challenger's own seed. -/
theorem bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (kemBound : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (ordinal : Nat) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (target : Fin (budget.create + 1)) :
    PqxdhDeploymentPublicationSecurityReduction.Bills setup.joint budget.create
      (client setup codec checks route ensureInit bounds mode adversary budget.create ordinal runtime)
      fallback ordinaryFallback (3 * budget.bundle) (budget.finish + budget.accept)
      (PqxdhRegistrationJointIdentityUniform.total caps qInit (transported bounds budget)) target :=
  PqxdhDeploymentPublicationSecurityClient.terminal_bills setup.joint codec budget.create transcript
    (source setup codec checks route ensureInit bounds mode adversary ordinal runtime) fallback ordinaryFallback
    _ _ _ (service setup codec checks route ensureInit bounds mode adversary budget respects ordinal runtime true)
    (service setup codec checks route ensureInit bounds mode adversary budget respects ordinal runtime false)
    (uniform setup codec checks route ensureInit qInit initBound caps kemBound bounds mode adversary budget respects
      ordinal runtime) target

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.creates

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.service

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.unread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.unread

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityBills.bills
