-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedRecordContents
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionReceipt

/-! Actual successful finish retains the first-record cut's cache through its actual remaining installation and phase update, for both the original and assigned-ID platform continuation. Cache bounds are derived from the reached source suffix rather than assumed at an unrelated final state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCompletionRecordCache
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (BeaconShell)
open RegistrationNativeBeaconFrontend
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
private theorem terminal (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (outcome : RustM (Option Pqxdh.Bytes)) (before after : Local n KemSK source) (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created (work *> pure outcome)).run before)) :
    .ok (some application) = outcome := by
  rw [seqRight_eq_bind, lower_bind, lower_pure, StateT.run_bind] at supported
  simp only [StateT.run_pure, bind_pure_comp, support_map] at supported
  obtain ⟨result, _possible, same⟩ := supported
  exact (congrArg Prod.fst same).symm

attribute [local irreducible] agreement record abort effect RegistrationAgreementExecutor.beacon RegistrationBeaconRecordExecutor.begin

/-- Actual successful legacy continuation retains its reached record cache through the actual source suffix. -/
theorem legacy (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativeResponseFinish.afterAuthentication setup wire index owner oneTime authenticated)).run before)) :
    ∃ capability established agreed recorded,
      (.ok (.BeaconComplete capability), agreed) ∈ support
        ((lower setup checks representation created
          (simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon authenticated))).run before) ∧
      (.ok (.Ok established), recorded) ∈ support
        ((lower setup checks representation created
          (simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run agreed) ∧
      RegistrationNativeWorldCache.cache before.2.2 ≤ RegistrationNativeWorldCache.cache agreed.2.2 ∧
      RegistrationNativeWorldCache.cache recorded.2.2 ≤ RegistrationNativeWorldCache.cache after.2.2 ∧
      application = TranscriptAuthParts.absSlice established.application := by
  rw [RegistrationNativeResponseFinish.afterAuthentication, lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, agreed⟩, called, continued⟩ := supported
  cases reply with
  | fail error | div =>
      have impossible := terminal setup checks representation created (abort owner) _ agreed after application continued
      cases impossible
  | ok result => cases result with
    | BeaconComplete capability =>
        rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at continued
        obtain ⟨⟨reply, recorded⟩, opened, continued⟩ := continued
        cases reply with
        | fail error | div =>
            have impossible := terminal setup checks representation created (abort owner) _ recorded after application continued
            cases impossible
        | ok result => cases result with
          | Err aborted =>
              have impossible := terminal setup checks representation created (abort owner) _ recorded after application continued
              cases impossible
          | Ok established =>
              have beforeAgreement := RegistrationNativeWorldCache.localProgram setup checks representation created _ before
                ((.ok (.BeaconComplete capability) : RustM agreement.AgreementEffect), agreed) called
              have afterRecord := RegistrationNativeWorldCache.localProgram setup checks representation created _ recorded
                ((.ok (some application) : RustM (Option Pqxdh.Bytes)), after) continued
              rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at continued
              obtain ⟨⟨installed, final⟩, inserted, returned⟩ := continued
              cases installed with
              | false =>
                  have impossible := terminal setup checks representation created (abort owner) _ final after application returned
                  cases impossible
              | true =>
                  have same := terminal setup checks representation created
                    (updatePhase index (.established ⟨established.control, established.binding, established.application⟩)) _ final after application returned
                  exact ⟨capability, established, agreed, recorded, called, opened, beforeAgreement, afterRecord,
                    Option.some.inj (RustM.ok.inj same)⟩
    | _ =>
        have impossible := terminal setup checks representation created (abort owner) _ agreed after application continued
        cases impossible


/-- Actual successful platform continuation retains its reached record cache through the actual source suffix. -/
theorem platform (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativePlatformBeaconFinish.afterAuthentication setup wire index owner oneTime authenticated)).run before)) :
    ∃ capability established agreed recorded,
      (.ok (.BeaconComplete capability), agreed) ∈ support
        ((lower setup checks representation created
          (simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon authenticated))).run before) ∧
      (.ok (.Ok established), recorded) ∈ support
        ((lower setup checks representation created
          (simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run agreed) ∧
      RegistrationNativeWorldCache.cache before.2.2 ≤ RegistrationNativeWorldCache.cache agreed.2.2 ∧
      RegistrationNativeWorldCache.cache recorded.2.2 ≤ RegistrationNativeWorldCache.cache after.2.2 ∧
      application = TranscriptAuthParts.absSlice established.application := by
  rw [RegistrationNativePlatformBeaconFinish.afterAuthentication, RegistrationNativePlatformBeaconFinish.afterAuthenticationWith, lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, agreed⟩, called, continued⟩ := supported
  cases reply with
  | fail error | div =>
      have impossible := terminal setup checks representation created (abort owner) _ agreed after application continued
      cases impossible
  | ok result => cases result with
    | BeaconComplete capability =>
        rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at continued
        obtain ⟨⟨reply, recorded⟩, opened, continued⟩ := continued
        cases reply with
        | fail error | div =>
            have impossible := terminal setup checks representation created (abort owner) _ recorded after application continued
            cases impossible
        | ok result => cases result with
          | Err aborted =>
              have impossible := terminal setup checks representation created (abort owner) _ recorded after application continued
              cases impossible
          | Ok established =>
              have beforeAgreement := RegistrationNativeWorldCache.localProgram setup checks representation created _ before
                ((.ok (.BeaconComplete capability) : RustM agreement.AgreementEffect), agreed) called
              have afterRecord := RegistrationNativeWorldCache.localProgram setup checks representation created _ recorded
                ((.ok (some application) : RustM (Option Pqxdh.Bytes)), after) continued
              simp only [RegistrationNativePlatformBeaconFinish.install_exact] at continued
              rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at continued
              obtain ⟨⟨installed, final⟩, inserted, returned⟩ := continued
              cases installed with
              | false =>
                  have impossible := terminal setup checks representation created (abort owner) _ final after application returned
                  cases impossible
              | true =>
                  have same := terminal setup checks representation created
                    (updatePhase index (.established ⟨established.control, established.binding, established.application⟩)) _ final after application returned
                  exact ⟨capability, established, agreed, recorded, called, opened, beforeAgreement, afterRecord,
                    Option.some.inj (RustM.ok.inj same)⟩
    | _ =>
        have impossible := terminal setup checks representation created (abort owner) _ agreed after application continued
        cases impossible




end BeaconcryptCore.Computational.RegistrationNativeCompletionRecordCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionRecordCache.legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionRecordCache.legacy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionRecordCache.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionRecordCache.platform
