-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawEnvironmentRun

/-! The guarded/public native interpreter uses the same actual CBOR record handler as the checked raw middle execution. Registration codecs remain independent of established record bytes. Resetting the unused legacy analysis ghosts retains every protocol field, produced frame, cache and private backend. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawNativeMiddle
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentBackend (RegImpl XState handlerWith onBase)
open PqxdhDeploymentIdealCut (unghost)
variable {ι KemSK Reader Response Bk : Type} {baseSpec : OracleSpec ι} {n : Nat}

/-- For established records, the actual command-dependent registration normalization changes no record primitive. -/
theorem record_base (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : Spec.Domain)
    (record : CborSplitCompiler.recordCommand query = true) (state : PqxdhDeploymentNative.State KemSK) :
    (CborProductionBoundary.baseHandler setup wire parse checks seed query).run state =
      (PqxdhDeploymentNative.handler setup (CborTaggedSimulation.boundaryWire wire parse) checks
        (CborRawCompile.route parse) seed query).run state := by
  rcases query with coin | command
  · simp [CborSplitCompiler.recordCommand] at record
  · cases command
    case serverSend => rfl
    case serverRaw => rfl
    case beaconSend => rfl
    case beaconRaw => rfl
    all_goals simp [CborSplitCompiler.recordCommand] at record

/-- The extended interpreter delegates record operations to the exact native base and does not inspect registration. -/
theorem backend_records (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (reg : RegImpl KemSK Bk n) (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true) :
    handlerWith setup codec route reg query = onBase (PqxdhDeploymentNative.handler setup codec checks route seed query) := by
  rcases query with coin | command
  · simp [CborSplitCompiler.recordCommand] at record
  · cases command
    case serverSend => rfl
    case serverRaw => rfl
    case beaconSend => rfl
    case beaconRaw => rfl
    all_goals simp [CborSplitCompiler.recordCommand] at record

/-- The codec outside registration is irrelevant to every non-record command. -/
theorem backend_nonrecord {OtherReader OtherResponse : Type} (setup : Setup baseSpec KemSK)
    (left : Codec Reader Response) (right : Codec OtherReader OtherResponse)
    (route : RawCtxServerRouting.SenderDecoder) (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (registration : CborSplitCompiler.recordCommand query = false) :
    handlerWith setup left route reg query = handlerWith setup right route reg query := by
  rcases query with coin | command
  · rfl
  · cases command
    case serverSend => simp [CborSplitCompiler.recordCommand] at registration
    case serverRaw => simp [CborSplitCompiler.recordCommand] at registration
    case beaconSend => simp [CborSplitCompiler.recordCommand] at registration
    case beaconRaw => simp [CborSplitCompiler.recordCommand] at registration
    all_goals rfl

private theorem record_refusal (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true)
    (state : PqxdhDeploymentNative.State KemSK) :
    CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state) =
      if CborProductionBoundary.allowed query state then none else some (CborProductionBoundary.reject query state).1 := by
  rcases query with coin | command
  · simp [CborSplitCompiler.recordCommand] at record
  · cases command
    case serverSend keyId plaintext => exact CborRecordNativeAdmission.server_admission state keyId plaintext
    case beaconSend owner plaintext => exact CborRecordNativeAdmission.beacon_admission state owner plaintext
    case serverRaw => rfl
    case beaconRaw => rfl
    all_goals simp [CborSplitCompiler.recordCommand] at record

private theorem reject_state (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true)
    (state : PqxdhDeploymentNative.State KemSK) : (CborProductionBoundary.reject query state).2 = state := by
  rcases query with coin | command
  · simp [CborSplitCompiler.recordCommand] at record
  · cases command
    case serverSend => rfl
    case serverRaw => rfl
    case beaconSend => rfl
    case beaconRaw => rfl
    all_goals simp [CborSplitCompiler.recordCommand] at record

/-- Native early admission is exactly the actual raw CBOR record operation, with complete protocol/private state retained. -/
theorem record_native (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (reg : RegImpl KemSK Bk n)
    (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true) (state : XState KemSK Bk n) :
    (fun value => (value.1, unghost value.2)) <$>
        (CborRawGuardedJoin.nativeHandler setup (CborTaggedSimulation.boundaryWire wire parse)
          (CborRawCompile.route parse) reg query).run state =
      (fun value => (value.1, (⟨value.2, state.backend, state.seeds,
          PqxdhDeploymentLater.Snap.empty, []⟩ : XState KemSK Bk n))) <$>
        (CborProductionBoundary.handler setup wire parse checks seed query).run state.base := by
  simp only [CborRawGuardedJoin.nativeHandler, StateT.run, record_refusal query record state.base,
    CborProductionBoundary.handler, CborCommandFilter.handler]
  cases allowed : CborProductionBoundary.allowed query state.base with
  | false =>
      simp only [Bool.false_eq_true, ite_false, map_pure, reject_state query record]
      rfl
  | true =>
      simp only [ite_true]
      rw [backend_records setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse) checks seed
        reg query record]
      have base : CborProductionBoundary.baseHandler setup wire parse checks seed query state.base =
          PqxdhDeploymentNative.handler setup (CborTaggedSimulation.boundaryWire wire parse) checks
            (CborRawCompile.route parse) seed query state.base :=
        record_base setup wire parse checks seed query record state.base
      rw [base]
      simp only [onBase, LazyOracleDiscard.StateLens.lift, PqxdhDeploymentBackend.baseLens, StateT.run, Functor.map_map]
      rfl

end BeaconcryptCore.Computational.CborRawNativeMiddle

/-- info: 'BeaconcryptCore.Computational.CborRawNativeMiddle.record_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeMiddle.record_base
/-- info: 'BeaconcryptCore.Computational.CborRawNativeMiddle.backend_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeMiddle.backend_records
/-- info: 'BeaconcryptCore.Computational.CborRawNativeMiddle.backend_nonrecord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeMiddle.backend_nonrecord
/-- info: 'BeaconcryptCore.Computational.CborRawNativeMiddle.record_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeMiddle.record_native
