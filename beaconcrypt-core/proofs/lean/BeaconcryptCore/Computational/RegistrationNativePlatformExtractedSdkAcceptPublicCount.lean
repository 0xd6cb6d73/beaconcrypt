-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The virtual native handle is the source adapter's count of successful accepted SDK tokens. It is not a parsed accept ordinal and is not read from a private receipt. The actual native retention projection returns exactly the pre-call session-list length on every Some reply. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount
open BeaconcryptCore.Refinement
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform] [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R : Type} {source : RegistrationNativeMldsa.Source}
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)

def observe (count : Nat) (word : AdapterPublicServerAgreementReceipt.Word R) : RustM (Option Nat) :=
  .ok (match word.1 with | .None=>none | .Some _=>some count)

omit platform in
theorem restored_sessions (before : RegistrationNativeExperiment.State n KemSK source)
    (raw : AdapterPublicServerAgreementReceipt.Receipt R ×RegistrationNativeExperiment.State n KemSK source)
    (effect : RustM agreement.AgreementEffect) (after : RegistrationNativeExperiment.State n KemSK source)
    (restored : AdapterPublicAgreementNativeWorldInterpreter.restore view before raw=.ok (effect,after)) :
    after.server.sessions=before.server.sessions := by
  rcases raw with ⟨receipt,current⟩
  cases receipt with
  | fail error | div=>cases restored
  | ok value=>
      simp only [AdapterPublicAgreementNativeWorldInterpreter.restore,AdapterPublicAgreementServerNativeWorld.restore,
        AdapterPublicAgreementServerWorld.restoreSource,AdapterPublicAgreementServerWorld.restoreRole,
        Functor.map,bind_tc_ok] at restored
      cases restored
      rfl

theorem retention (completed : agreement.ServerAgreement)
    (word : RustM (AdapterPublicServerAgreementReceipt.Word R)) (state : RegistrationNativeExperiment.State n KemSK source)
    (index : Nat) (after : RegistrationNativeExperiment.State n KemSK source)
    (projected : AdapterPublicServerRetainNative.project completed (word,state)=(.ok (some index),after)) :
    index=state.server.sessions.length := by
  cases word with
  | fail error | div=>cases projected
  | ok word=>
      rcases word with ⟨optional,self,rng⟩
      cases optional with
      | none=>cases projected
      | some token=>exact (Option.some.inj (RustM.ok.inj (congrArg Prod.fst projected))).symm

theorem agreement (before : RegistrationNativeExperiment.State n KemSK source)
    (raw : (AdapterPublicServerAgreementReceipt.Receipt R ×RustM (AdapterPublicServerAgreementReceipt.Word R)) ×RegistrationNativeExperiment.State n KemSK source)
    (index : Nat) (after : RegistrationNativeExperiment.State n KemSK source)
    (projected : AdapterPublicServerAgreementRetention.project view before raw=.ok (.ok (some index),after)) :
    index=before.server.sessions.length := by
  unfold AdapterPublicServerAgreementRetention.project at projected
  cases restored:AdapterPublicAgreementNativeWorldInterpreter.restore view before (raw.1.1,raw.2) with
  | fail error | div=>simp only [restored] at projected; cases projected
  | ok value=>
      rcases value with ⟨effect,current⟩
      have sessions:=restored_sessions view before (raw.1.1,raw.2) effect current restored
      simp only [restored,bind_tc_ok] at projected
      change RustM.ok (AdapterPublicServerAgreementRetention.projectEffect effect (raw.1.2,current))=.ok (.ok (some index),after) at projected
      have projected:=RustM.ok.inj projected
      cases effect with
      | fail error | div=>
          cases word:raw.1.2 <;> simp only [AdapterPublicServerAgreementRetention.projectEffect,word] at projected <;> cases projected
      | ok effect=>cases effect with
        | ServerComplete completed=>
            have same:=retention completed raw.1.2 current index after projected
            exact same.trans (congrArg List.length sessions)
        | _=>
            cases word:raw.1.2 <;> simp only [AdapterPublicServerAgreementRetention.projectEffect,word] at projected <;> cases projected

theorem reservation (before : RegistrationNativeExperiment.State n KemSK source)
    (raw : (AdapterPublicServerReservationReceipt.Receipt R ×RustM (AdapterPublicServerAgreementReceipt.Word R)) ×RegistrationNativeExperiment.State n KemSK source)
    (index : Nat) (after : RegistrationNativeExperiment.State n KemSK source)
    (projected : AdapterPublicServerReservationNative.project view before raw=.ok (.ok (some index),after)) :
    index=before.server.sessions.length := by
  cases receiptEq:raw.1.1 with
  | none=>
      cases word:raw.1.2 <;> simp only [AdapterPublicServerReservationNative.project,receiptEq,word] at projected <;> cases projected
  | some receipt=>
      simp only [AdapterPublicServerReservationNative.project,receiptEq] at projected
      exact agreement view before ((receipt,raw.1.2),raw.2) index after projected
theorem represented (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (raw : (AdapterPublicServerReservationReceipt.Receipt R ×RustM (AdapterPublicServerAgreementReceipt.Word R)) ×RegistrationNativeExperiment.State n KemSK source)
    (word : AdapterPublicServerAgreementReceipt.Word R) (handle : Option Nat)
    (after : RegistrationNativeExperiment.State n KemSK source)
    (projected : AdapterPublicServerReservationNative.project view before raw=.ok (.ok handle,after))
    (returned : AdapterPublicServerAgreementPost.Returned view views created credential word (.ok handle,after)) :
    observe before.server.sessions.length word=.ok handle := by
  rcases word with ⟨optional,self,rng⟩
  cases optional with
  | none=>
      cases handle with
      | none=>rfl
      | some index=>exact returned.2.elim
  | some token=>
      cases handle with
      | none=>exact returned.2.elim
      | some index=>
          have same:=reservation view before raw index after projected
          cases same
          rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.restored_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.restored_sessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.retention' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.retention

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.reservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.reservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount.represented
