-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomBeaconTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishPreparation
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount
/-! The actual corrected incoming finish uses its original selected/ordinary indexed source and exact terminal preparation helper, followed by its new assigned-ID record program. An atom attempt therefore spends the same actual selected owner’s one-use phase credit; no owner/handle equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerCount
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordAtomOwnerSource (State drop routing)
open RegistrationNativeSecretWordAtomInstallTrace (atom count)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "lower" => RegistrationNativeSecretWordAtomOwnerSource.lower (n := n) setup wire route sign input inside provider outer

private theorem abort_free (role : Role) (owner current : SelectedOwner source) (before : Environment) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.abort (RegistrationNativeSecretWordInterface.effect (n := n) (KemSK := KemSK)) owner).run current).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) 0 := by
  simp [RegistrationNativePlatformBeaconMaterialFrontend.abort, StateT.run_lift, bind_pure_comp,
    RegistrationNativeSecretWordInterface.effect, LocalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
    RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]

/-- Actual corrected first-record completion can charge only its own newly demanded descriptor. -/
theorem complete (scalar : Option PqxdhJointGapDh.ScalarBytes) (owner current : SelectedOwner source)
    (ready : BeaconReady) (before : State n KemSK)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × State n KemSK)
    (supported : result ∈ support
      ((lower scalar ((RegistrationNativePlatformSecretWordFinish.complete setup.source wire.frameWrite owner ready).run current)).run before)) :
    count .beacon result.2.2.1 ≤ count .beacon before.2.1 + atom (some ready.reference) := by
  have actual := RegistrationNativeSecretWordAtomOwnerSource.trace_support setup wire route sign input inside provider outer
    scalar ((RegistrationNativePlatformSecretWordFinish.complete setup.source wire.frameWrite owner ready).run current) before result supported
  simpa only [RegistrationNativePlatformSecretWordAtomBeaconTrace.compile, ite_true, Nat.one_mul] using
    RegistrationNativePlatformSecretWordAtomBeaconTrace.complete_count .beacon setup scalar setup.source wire.frameWrite
      owner current ready before.1 before.2.1 ((result.1, result.2.1), result.2.2.1) actual

private theorem map_apply {Private Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT Private m Value) (before : Private) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

attribute [local irreducible] RegistrationNativeSecretWordAtomOwnerSource.lower
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordInterpreter.handler

/-- An atom in an actual corrected incoming source uses the selected retained handle and spends that owner's terminal credit. -/
theorem local_finish (front : RegistrationNativeSecretWordMessage.State source)
    (index : Nat) (owner : RegistrationNativePublicOwners.Owner source)
    (packet : Option registration.ResponsePacket) (before : State n KemSK)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × State n KemSK)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned front.beacons before.2.2.kem.1.keys)
    (found : front.beacons[index]? = some owner)
    (supported : result ∈ support
      ((lower owner.scalar ((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner.view)).run before)) :
    count .beacon result.2.2.1 ≤ count .beacon before.2.1 +
      RegistrationNativeSecretWordOwnerCredit.cost selected (.inr (.finish index packet)) front := by
  have sourceEq : RegistrationNativePlatformSecretWordFinish.finish (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup wire source packet =
      RegistrationNativePlatformSecretWordFinishPreparation.program setup wire source packet := by
    funext current env
    exact RegistrationNativePlatformSecretWordFinishPreparation.source setup wire source packet current env
  rw [sourceEq] at supported
  simp only [RegistrationNativePlatformSecretWordFinishPreparation.program, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases phase : owner.view.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [phase, RegistrationNativeSecretWordAtomOwnerSource.lower_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      dsimp only
      omega
  | initSent pending oneTime =>
      simp only [phase] at supported
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, RegistrationNativeSecretWordAtomOwnerSource.lower_pure, StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          dsimp only
          omega
      | ok aborted =>
          simp only [moved, StateT.run_bind] at supported
          rw [RegistrationNativeSecretWordAtomOwnerSource.lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨⟨⟨prepared, current⟩, middle⟩, preparationAt, continued⟩ := supported
          have prepCount := RegistrationNativeSecretWordAtomOwnerCount.free setup wire route sign input inside selected pairs publicKey challenge outer .beacon owner.scalar
            ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner.view) before
            ((prepared, current), middle)
            (RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free .beacon setup source packet owner.view before.1)
            preparationAt
          dsimp only at prepCount
          cases prepared with
          | fail error | div =>
              simp only [RegistrationNativePlatformSecretWordFinish.afterPrepared] at continued
              have last := RegistrationNativeSecretWordAtomOwnerCount.free setup wire route sign input inside selected pairs publicKey challenge outer .beacon owner.scalar
                _ middle result (by
                  simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                    (abort_free .beacon (KemSK := KemSK) owner.view current middle.1)) continued
              omega
          | ok prepared => cases prepared with
            | none =>
                simp only [RegistrationNativePlatformSecretWordFinish.afterPrepared] at continued
                have last := RegistrationNativeSecretWordAtomOwnerCount.free setup wire route sign input inside selected pairs publicKey challenge outer .beacon owner.scalar
                  _ middle result (by
                    simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                      (abort_free .beacon (KemSK := KemSK) owner.view current middle.1)) continued
                omega
            | some ready =>
                simp only [RegistrationNativePlatformSecretWordFinish.afterPrepared] at continued
                have last := complete setup wire route sign input inside selected pairs publicKey challenge outer owner.scalar
                  owner.view current ready middle result continued
                by_cases word : ready.reference.kem = Word.atom
                · have eligible := RegistrationNativeSecretWordAtomOwnerCount.preparation_owner setup wire route sign input inside selected pairs publicKey challenge outer
                    front index owner before current ready middle aligned found packet word preparationAt
                  have paid : RegistrationNativeSecretWordOwnerCredit.cost selected (.inr (.finish index packet)) front = 1 := by
                    simp only [RegistrationNativeSecretWordOwnerCredit.cost, ite_eq_left eligible.1, found, ite_eq_left eligible.2]
                  simp only [atom, word] at last
                  omega
                · have noCharge : atom (some ready.reference) = 0 := by
                    unfold atom
                    cases actual : ready.reference.kem with
                    | atom => exact (word actual).elim
                    | literal secret => simp only [actual]
                  rw [noCharge] at last
                  omega


end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerCount

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerCount.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerCount.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerCount.local_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerCount.local_finish
