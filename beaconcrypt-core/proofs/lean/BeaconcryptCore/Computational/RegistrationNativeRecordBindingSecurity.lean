-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource
import BeaconcryptCore.Computational.RegistrationNativeRecordBindingEvent

/-! The actual complete native ideal-record execution has a source-billed cross-handle binding bound. Startup effects, failed writers, all original test/fresh draws and all later publications stay in the one same-cache program. The event concerns the compiled installed record-slot partnership; completed root/initializer agreement remains a separate obligation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordBindingSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State)
open RegistrationNativeSelectiveRecordBills (programBill)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
  (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : PqxdhDeploymentInterface.Budget)
  (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
  (allowance : Fin 14 → PqxdhRecordLiftInterface.EffectKind → Nat)
  (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)
  (constructorCoins mlCoins : Nat)
  (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKid none).run ()).IsTotalQueryBound constructorCoins)
  (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)

include ideal bounded framed constructorBound mlBound in
/-- Same-run native commitment conflict has the exact private-seal versus shared-hash collision term, with bills derived from the actual source program. -/
theorem conflict_bound :
    𝒟[(fun result => PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      RegistrationNativeSelectiveEntropyStartup.run (n := n) modes replace setup checks wire route source ensureInit identityIndex serverKid
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary CtxPrivate.initial] {true} ≤
      ((budget.sends * (budget.sends +
        (1 + (budget.hash + (PqxdhRecordLiftInterface.Caps.mk budget 0).envTotal allowance .hash) + budget.sends + budget.receives)) : Nat) : ℝ≥0∞) /
          (2 : ℝ≥0∞)^512 := by
  have records := RegistrationNativeSelectiveRecordBills.record_bounded (n := n) setup checks wire source ensureInit identityIndex serverKid
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary budget bounded
  have hashes := RegistrationNativeSelectiveRecordBills.program_categories (n := n) setup checks wire source ensureInit identityIndex serverKid
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary budget bounded allowance framed
    constructorCoins mlCoins constructorBound mlBound route .hash
  have bound := RegistrationNativeRecordBindingSource.conflict_bound modes replace setup (RegistrationNativeWire.ledgerCodec wire) route
    (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKid
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary) ideal budget records
      (programBill budget bounds allowance constructorCoins mlCoins .hash) hashes
  rw [RegistrationNativeSelectiveRecordBills.hash_bill] at bound
  simpa only [RegistrationNativeRecordOriginProgram.program, RegistrationNativeRecordPackage.client,
    RegistrationNativeSelectiveRecordStartup.program, RegistrationNativeSelectiveEntropyStartup.run, RegistrationNativeSelectiveEntropyStartup.project,
    PqxdhRecordLiftProtocol.schedule, CborRecordWorldClient.client, CborRawRecordOriginFlatten.interpret,
    simulateQ_map, StateT.run_map, Functor.map_map] using bound

include ideal bounded framed constructorBound mlBound in
/-- Exact cross-handle record binding, in both directions and with publication anywhere in the final original transcript, has the same collision term. -/
theorem cross_bound (readback : PqxdhServerAuthNegativeControl.FrameReadBack (RegistrationNativeWire.ledgerCodec wire)) :
    𝒟[(fun result => PqxdhRecordLiftIdeal.crossEvent (RegistrationNativeWire.ledgerCodec wire) route
      (RegistrationNativeRecordBindingEvent.view result)) <$>
      RegistrationNativeSelectiveEntropyStartup.run (n := n) modes replace setup checks wire route source ensureInit identityIndex serverKid
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary CtxPrivate.initial] {true} ≤
      ((budget.sends * (budget.sends +
        (1 + (budget.hash + (PqxdhRecordLiftInterface.Caps.mk budget 0).envTotal allowance .hash) + budget.sends + budget.receives)) : Nat) : ℝ≥0∞) /
          (2 : ℝ≥0∞)^512 := by
  apply le_trans _ (conflict_bound modes ideal replace setup checks wire route source ensureInit identityIndex serverKid
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary budget bounded allowance framed
    constructorCoins mlCoins constructorBound mlBound)
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro result supported crossed
  exact @decide_eq_true _ (Classical.propDecidable _) (RegistrationNativeRecordBindingEvent.cross_conflict modes ideal replace setup checks wire route readback
    source ensureInit identityIndex serverKid seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary result supported
    (@of_decide_eq_true _ (Classical.propDecidable _) crossed))

end BeaconcryptCore.Computational.RegistrationNativeRecordBindingSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingSecurity.conflict_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingSecurity.conflict_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingSecurity.cross_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingSecurity.cross_bound
