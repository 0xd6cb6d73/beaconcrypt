import BeaconcryptCore.Computational.PqxdhInitialAuditedResources
import BeaconcryptCore.Computational.PqxdhInitialHistoryBudget
import BeaconcryptCore.Computational.PqxdhInitialParentStoppedBudgets

/-!
The ordinary stopped observer receives an actual supported descriptor and the complete audited pre-draw source state. Its private table, shared primitive state, identity state and root cache are the reached fields themselves. The candidate seed contains the literal saved disclosure history and every chronological earlier candidate. The original source budget derives the whole stopped certificate; neither an arbitrary reached-state resource bound nor a whole-observer premise is required.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient RawCtxSelectedParentEntry
open PqxdhInitialParentObserverBudgets (Costs ExternalUniform)
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Input (extra : OracleSpec ι) (M P I D K Result Origin A N C : Type) (S B : Nat) :=
  PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B × PqxdhInitialNativeAudit.State A N C

def Supported
    (run : ProbComp (PqxdhInitialNativeAuditCarried.Carried extra M P I D K Result Origin A N C S B)) :=
  { input : Input extra M P I D K Result Origin A N C S B //
    RawCtxForwardScan.Cut.pending input.1 input.2 ∈ support run }

def ambient (input : Input extra M P I D K Result Origin A N C S B) :
    PqxdhInitialParentObserver.State A N C :=
  ((input.2.1.1.1.1, input.2.1.2.1), input.2.1.2.2)

section Observer
variable (source : FixedHkdfSha512NoSaltSource)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (run : ProbComp (PqxdhInitialNativeAuditCarried.Carried extra M P I D K Result Origin A N C S B))
  (disclosed : List RatchetChain) (remaining : Nat)
  (event : Supported run × Entry → PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B → Prop)

noncomputable def continuation : PqxdhInitialParentStoppedHop.Continuation (Supported run)
    extra M P I D K X Response Shared A N C Result Origin S B where
  cut input := input.val.1
  depth _ := some remaining
  prior input := RawCtxSelectedParentTable.view (PqxdhJointKdf.productionStream source.crypto) input.val.2.1.1.1.2.1
  initial input := PqxdhInitialStoppedDisclosure.initial disclosed input.1.val.1
    (ambient input.1.val) input.1.val.2.2
  pre _ := pre
  application _ := application
  initializer _ := initializer
  selector _ := selector
  aux _ := aux
  event := event

/-- The observer uses the exact reached table and ambient fields and initializes its disclosure state from the actual saved history and full chronological audit. -/
theorem continuation_state (input : Supported run) (entry : Entry) :
    let next := continuation source pre application initializer selector aux run disclosed remaining event
    next.cut input = input.val.1 ∧
      next.prior input = RawCtxSelectedParentTable.view (PqxdhJointKdf.productionStream source.crypto) input.val.2.1.1.1.2.1 ∧
      next.initial (input, entry) = PqxdhInitialStoppedDisclosure.initial disclosed input.val.1
        (ambient input.val) input.val.2.2 := by
  exact ⟨rfl, rfl, rfl⟩

end Observer

section Source
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
  (depth stage qPost : Nat) (state : PqxdhInitialNativeAudit.State A N C)
  (sourceBound : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
  (disclosed : List RatchetChain) (remaining : Nat)
  (costs : Costs) (external : ExternalUniform costs pre application initializer selector aux)

local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer pre application initializer selector aux
  mark sender route decode execution depth stage state

def priorBudget : Nat :=
  PqxdhInitialHistoryBudget.knownLength disclosed execution.before.roles.2 + qPost + state.2.length + 3 * (7 + qPost * 67)

def certificate (event : Supported sourceRun × Entry → PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B → Prop) : PqxdhInitialParentStoppedBudgets.Certificate
    (continuation source pre application initializer selector aux sourceRun disclosed remaining event) where
  qPost := qPost
  qPrior := priorBudget execution qPost state disclosed
  qCheck := remaining + 1
  costs := costs
  fits := by
    intro input
    exact PqxdhInitialNativeAuditCarried.carried_fits source writer pre application initializer selector aux mark sender route decode
      execution depth stage qPost sourceBound state input.val.2 input.val.1 input.property
  checkBound _ := le_refl _
  priorBound := by
    intro input
    exact PqxdhInitialHistoryBudget.carried_seed source writer pre application initializer selector aux mark sender route decode
      execution depth stage qPost sourceBound disclosed state input.1.val.2 input.1.val.1 input.1.property
  external _ := external


/-- The source-supported certificate has explicit whole-observer, candidate and checker bills, with the original saved history and initial audit charged in full. -/
theorem certificate_bills
    (event : Supported sourceRun × Entry → PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B → Prop) :
    let actual := certificate source writer pre application initializer selector aux mark sender route decode execution
      depth stage qPost state sourceBound disclosed remaining costs external event
    PqxdhInitialParentStoppedBudgets.callbackBudget actual = 2 * (255 + qPost * 67) + (remaining + 1) ∧
      PqxdhInitialParentStoppedBudgets.uniformBudget actual = (2 * (255 + qPost * 67) + (remaining + 1)) * costs.cap ∧
      PqxdhInitialParentStoppedBudgets.candidateBudget actual =
        priorBudget execution qPost state disclosed + 3 * (2 * (255 + qPost * 67) + (remaining + 1)) := by
  exact ⟨rfl, rfl, rfl⟩

include sourceBound external in
/-- Every actual supported stopped descriptor yields the complete ordinary observer's derived random-query and candidate bounds, including all attempted operations and the appended lineage checker. -/
theorem observer_resources
    (event : Supported sourceRun × Entry → PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B → Prop)
    (context : Supported sourceRun × Entry) (output : PqxdhFullSecretInputKdf.FullOutput) :
    let next := continuation source pre application initializer selector aux sourceRun disclosed remaining event
    let work := PqxdhInitialParentStoppedHop.observed source writer mark sender route decode next context output
    work.IsTotalQueryBound ((2 * (255 + qPost * 67) + (remaining + 1)) * costs.cap) ∧
      ∀ result, result ∈ support work → (PqxdhInitialParentStoppedHop.candidates result).length ≤
        priorBudget execution qPost state disclosed + 3 * (2 * (255 + qPost * 67) + (remaining + 1)) := by
  exact ⟨PqxdhInitialParentStoppedBudgets.source_uniform source writer mark sender route decode _
    (certificate source writer pre application initializer selector aux mark sender route decode execution
      depth stage qPost state sourceBound disclosed remaining costs external event) context output,
    PqxdhInitialParentStoppedBudgets.source_candidates source writer mark sender route decode _
      (certificate source writer pre application initializer selector aux mark sender route decode execution
        depth stage qPost state sourceBound disclosed remaining costs external event) context output⟩

end Source
end BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate


/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate.continuation_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate.continuation_state

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate.certificate

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate.certificate_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate.certificate_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate.observer_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSupportedCertificate.observer_resources
