-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicCaps
import BeaconcryptCore.Computational.RegistrationNativeDecisionRetainedStartup

/-! The complete generated reference profile retains its original build-plus-finish material bill before preparation. The observation is any literal original-ledger decision in either original mode. This endpoint does not assume equality to the SDK source profile or a repeated-role hidden-install relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeDecisionKeyBill
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeDecisionRetainedStartup (client)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- Real constructor/ML/init/hash draws add no material demand to the original raw adversary allowance. -/
theorem client_bound (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) :
    (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision publicValue).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand (budget.cap 4 + budget.cap 5) := by
  unfold client
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) ?_ ?_).mono (by omega)
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro coin
    simp [RegistrationNativePublicRetained.coins, RegistrationNativeRetainedService.IsDemand, isQueryBoundP_query_iff]
  · intro initialized _reached
    cases initialized.1 with
    | none => trivial
    | some started =>
        apply RegistrationNativePublicCaps.retained_bound
        rw [RegistrationNativeDecisionRetainedStartup.observed, isQueryBoundP_map_iff]
        exact RegistrationNativePublicCaps.run_bound setup checks wire source
          (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
          (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) budget
          (bounded _) started.frontend


end BeaconcryptCore.Computational.RegistrationNativeDecisionKeyBill
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionKeyBill.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionKeyBill.client_bound
