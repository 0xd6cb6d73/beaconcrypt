-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds
import BeaconcryptCore.Computational.FinitePartitionQueryBounds
/-! The actual corrected OPEN accept pays32 source coins, four shared hashes and one indexed encapsulation allowance. The public reserve remains in the same P and carries its independent external bill. Counts are derived from the actual free controller, including every rejected prefix. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeAccept
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind effectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_mono weighted_run)
open RegistrationNativePlatformServerOpenSyntaxBounds (Kind queryKind protocolKind cap)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePublicationCosts (hashCost)
open RegistrationNativeCreateCosts (administrativeCost)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I}

private def kinds : Finset Kind := {.prepare, .coin, .hash, .admin, .encapsulation, .reserve, .other}
local instance : Fintype Kind := ⟨kinds, by intro kind; cases kind <;> simp [kinds]⟩
private def cost (qSign qKem : Nat) (kind : EffectKind) : Kind → Nat
  | .prepare | .reserve => 0
  | .coin => coinCost 1 kind
  | .hash => hashCost kind
  | .admin => administrativeCost kind
  | .encapsulation => coinCost qKem kind
  | .other => coinCost (108 + qSign + qKem) kind + hashCost kind

def acceptBill (qKem : Nat) (kind : EffectKind) := coinCost (32 + qKem) kind + hashCost kind * 4

private theorem protocol_cost (qSign qKem : Nat) (kind : EffectKind)
    (query : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain) :
    RegistrationNativeReferenceCosts.bill qSign qKem query kind ≤ cost qSign qKem kind (protocolKind query) := by
  rcases query with message | (message | (publication | effect)) | (ordinary | (privateQuery | key))
  · simp [RegistrationNativeReferenceCosts.bill, protocolKind, cost]
  · cases kind <;> simp [RegistrationNativeReferenceCosts.bill, protocolKind, cost, coinCost, hashCost]; omega
  · cases publication with
    | inl raw => cases kind <;> simp [RegistrationNativeReferenceCosts.bill, protocolKind, cost,
        RegistrationNativePublicationCosts.bill, coinCost, hashCost]
    | inr request => cases request <;> cases kind <;> simp [RegistrationNativeReferenceCosts.bill, protocolKind, cost,
        RegistrationNativePublicationCosts.bill, coinCost, hashCost]; omega
  · cases reached : effectKind effect <;> cases kind <;> simp [RegistrationNativeReferenceCosts.bill, protocolKind,
      cost, reached, coinCost, hashCost, administrativeCost]
  · cases kind <;> simp [RegistrationNativeReferenceCosts.bill, protocolKind, cost, coinCost, hashCost]
  · cases kind <;> simp [RegistrationNativeReferenceCosts.bill, protocolKind, cost, coinCost, hashCost]
  · cases kind <;> simp [RegistrationNativeReferenceCosts.bill, protocolKind, cost, coinCost]

private theorem partition_weighted {Kind I A : Type} {spec : OracleSpec I} [Fintype Kind] [DecidableEq Kind]
    (classify : I → Kind) (cost budget : Kind → Nat) (work : OracleComp spec A)
    (bounded : ∀ kind, work.IsQueryBoundP (fun query => classify query = kind) (budget kind)) :
    Weighted (fun query => cost (classify query)) work (FinitePartitionQueryBounds.bill cost budget) := by
  apply OracleComp.IsQueryBound.proj (FinitePartitionQueryBounds.bill cost)
    (h := FinitePartitionQueryBounds.structural classify work budget bounded)
  · intro query current positive
    have same := FinitePartitionQueryBounds.bill_step cost current (classify query) positive
    dsimp only
    omega
  · intro query current positive
    have same := FinitePartitionQueryBounds.bill_step cost current (classify query) positive
    dsimp only
    omega

private theorem cap_eq (qSign qKem : Nat) (kind : EffectKind) :
    FinitePartitionQueryBounds.bill (cost qSign qKem kind) cap = acceptBill qKem kind := by
  unfold FinitePartitionQueryBounds.bill
  rw [show (Finset.univ : Finset Kind) = kinds from rfl]
  cases kind <;> simp [kinds, cost, cap, acceptBill, coinCost, hashCost, administrativeCost]

/-- Literal corrected accept retains the exact native bill independently of arbitrary stateful reservation effects. -/
theorem accept_bound (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment)
    (previous : Platform) (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (RegistrationNativePlatformPublicNativeLocal.bill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((((RegistrationNativePlatformServerOpenControl.accept (RegistrationNativePlatformPublicFrontend.localHandler selected)
        (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet).run front).run env).run previous)
      (acceptBill qKem kind) := by
  let implementation := RegistrationNativePlatformPublicSourceAccept.syntaxBase (n := n) (KemSK := KemSK) selected reserve
  have actual := RegistrationNativePlatformServerOpenSyntax.accept_source implementation setup checks verify packet
  change RegistrationNativePlatformServerOpenSyntax.evaluate implementation _ =
    RegistrationNativePlatformServerOpenControl.accept (RegistrationNativePlatformPublicFrontend.localHandler selected)
      (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet at actual
  rw [← actual]
  unfold RegistrationNativePlatformServerOpenSyntax.evaluate
  rw [← cap_eq qSign qKem kind]
  apply weighted_run _ _ implementation _ _ previous
    (partition_weighted queryKind (cost qSign qKem kind) cap _
      (fun selected => RegistrationNativePlatformServerOpenSyntaxBounds.accept_bound setup checks verify selected packet front env))
  intro query current
  cases query with
  | inl query =>
    apply weighted_mono _ _ _ _ ?_ (protocol_cost qSign qKem kind query)
    simpa only [implementation, RegistrationNativePlatformPublicSourceAccept.syntaxBase, simulateQ_spec_query] using
      RegistrationNativePlatformPublicNativeLocal.local_program qSign qKem kind selected
        ((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _)
        (RegistrationNativeReferenceCosts.bill qSign qKem query kind)
        (RegistrationNativeWeightedContext.query_bound _ _) current
  | inr _ => exact RegistrationNativePlatformPublicNativeLocal.platform_zero qSign qKem kind reserve current
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeAccept.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeAccept.accept_bound
