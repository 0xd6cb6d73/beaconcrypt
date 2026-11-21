-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProgram

/-! The same original source prefix supplies actual generated-row ownership to the normalized public bundle cutoff. Normalization erases only prior signature slots and raw ML receipts; private source rows, full hash state and signing history remain in the interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedInput
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxMain (Full interpret)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "current(" placeholder ")" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder

local notation "jointView(" placeholder ")" => RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder

/-- The actual normalized callback depends on no erased old signature or ML-receipt field in its input. -/
theorem query (placeholder : Ed25519Signature) (request : TypedSpec.Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    current(placeholder) request (jointView(placeholder) before)=current(placeholder) request before := by
  exact (RegistrationNativePlatformIdentityCtxTypedJointView.handler_stable setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer placeholder request before).symm

private theorem visit_step (selected position accept : Nat) (placeholder : Ed25519Signature)
    (defaults : (request : TypedSpec.Domain) → TypedSpec.Range request) (request : TypedSpec.Domain)
    (next : TypedSpec.Range request → OracleComp TypedSpec A)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState (RegistrationNativeIdentityMain.State n KemSK source × Platform)) :
    RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current(placeholder) defaults (TypedSpec.query request >>=next) before=(do
      let result←(RegistrationNativeIdentityCensorBeforeAccept.step selected position accept placeholder current(placeholder) defaults request).run before
      match RegistrationNativeIdentityCensorPublicClient.observe accept request before result.1 result.2 with
      | none=>RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current(placeholder) defaults (next result.1) result.2
      | some reason=>pure (RegistrationNativeIdentityCensorPacketClient.finish result.2.1.2.target reason)) := rfl

/-- The complete executable before-accept visitor is identical at arbitrary original and jointly viewed native inputs. Mode, ordinal, private source queries and the original packet remain unchanged. -/
theorem visit (selected position accept : Nat) (placeholder : Ed25519Signature)
    (defaults : (request : TypedSpec.Domain) → TypedSpec.Range request) (work : OracleComp TypedSpec A)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (mode : RegistrationNativeIdentityCensorCompiler.Mode) (cursor : Nat) :
    RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current(placeholder) defaults work ((jointView(placeholder) before,mode),cursor)=
      RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current(placeholder) defaults work ((before,mode),cursor) := by
  induction work using OracleComp.inductionOn with
  | pure value=>rfl
  | query_bind request next ih=>
    rw [visit_step,visit_step]
    cases request with
    | inl coin=>simp only [RegistrationNativeIdentityCensorBeforeAccept.step,RegistrationNativeIdentityCensorPublicClient.step,
        RegistrationNativeIdentityCensorPublicClient.callback,StateT.run,query,RegistrationNativeIdentityCensorPublicClient.observe]
    | inr command=>
      cases command
      case accept packet=>
        by_cases chosen : cursor=accept
        · simp only [RegistrationNativeIdentityCensorBeforeAccept.step,StateT.run,chosen,ite_true,pure_bind,
            RegistrationNativeIdentityCensorPublicClient.observe]
        · simp only [RegistrationNativeIdentityCensorBeforeAccept.step,StateT.run,chosen,ite_false,
            RegistrationNativeIdentityCensorPublicClient.step,RegistrationNativeIdentityCensorPublicClient.callback,query,RegistrationNativeIdentityCensorPublicClient.observe]
      all_goals simp only [RegistrationNativeIdentityCensorBeforeAccept.step,RegistrationNativeIdentityCensorPublicClient.step,
        RegistrationNativeIdentityCensorPublicClient.callback,StateT.run,query,RegistrationNativeIdentityCensorPublicClient.observe]
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedInput
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedInput.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedInput.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedInput.visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedInput.visit
