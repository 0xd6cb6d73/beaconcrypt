-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps

/-! Concrete Server publication lowering runs on the current Env and cannot introduce another material descriptor. The actual admitted, complete and one-use build programs therefore satisfy preparation safety using their exact retained reference and the internally maintained live-session invariant. Both current signing receipts and every failure continuation remain in the AST. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady ServerState)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec LocalSpec effect demand liftLocal)
open RegistrationNativeSecretWordInterpreter (State Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
open RegistrationNativeSecretWordLiveFlags (Valid)
open RegistrationNativeSecretWordLiveCaps (Bad BadLocal BadPublic)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordServerCompiler (service)
variable {n : Nat} {ι KemSK Value Encoded : Type} {base : OracleSpec ι}

private theorem bad_demand (flags : Message → Bool) (query : (LocalSpec n KemSK).Domain)
    (bad : BadLocal (KemSK := KemSK) flags query) : RegistrationNativeSecretWordFrontendCapsLocal.IsDemand (KemSK := KemSK) query := by
  rcases query with message | (message | common) | kem
  · exact bad.elim
  · trivial
  · exact bad.elim
  · exact bad.elim

private theorem environment_free (flags : Message → Bool) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (BadLocal (KemSK := KemSK) flags) 0 :=
  IsQueryBoundP.of_imp (bad_demand flags) (RegistrationNativeSecretWordFrontendCapsLocal.effect_free work)

private theorem common_free (flags : Message → Bool) (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (env : Environment) :
    ((RegistrationNativeCommonCompiler.common (effect (KemSK := KemSK)) hkdf wire.frameWrite sign query).run env).IsQueryBoundP
      (BadLocal (KemSK := KemSK) flags) 0 := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeCommonCompiler.common, RegistrationNativeCommonCompiler.publication,
        StateT.run, isQueryBoundP_map_iff]
      exact environment_free flags _
  | inr query =>
      simp [RegistrationNativeCommonCompiler.common, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, effect, BadLocal, isQueryBoundP_query_iff]

private theorem service_bound (flags : Message → Bool) (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Value)
    (bounded : work.IsQueryBoundP (BadPublic flags) 0) (env : Environment) :
    ((simulateQ (service (KemSK := KemSK) hkdf wire sign) work).run env).IsQueryBoundP (BadLocal (KemSK := KemSK) flags) 0 := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    cases query with
    | inl message =>
        simp [service, demand, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
          BadLocal, isQueryBoundP_query_iff]
    | inr query => exact counted.elim
  · intro query free current
    cases query with
    | inl message =>
        have prepared : flags message = true := Bool.eq_true_of_not_eq_false free
        simp [service, demand, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
          BadLocal, prepared, isQueryBoundP_query_iff]
    | inr query => exact common_free flags hkdf wire sign query current

/-- Actual admitted Server material and current-Env publication are preparation-safe under their successful returned-name flag receipt. -/
theorem admitted (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selected : Bool) (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (reference : Message)
    (env : Environment) (before : State n KemSK) (valid : Valid input before) (prepared : before.flags reference = true) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (simulateQ (liftLocal selected) ((simulateQ (service setup.source wire sign)
        (RegistrationNativeSecretWordServerMaterial.admitted encode control initial reference)).run env)) before := by
  apply RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid
  apply RegistrationNativeSecretWordLiveCaps.local_bound before.flags selected
  exact service_bound before.flags setup.source wire sign _
    (RegistrationNativeSecretWordLiveMaterialCaps.admitted_free before.flags encode control initial reference prepared) env

/-- Every actual transient Server completion keeps its exact reference through all admission, publication and installation branches. -/
theorem complete (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selected reservePeer : Bool) (ready : ServerReady) (application : Slice U8) (server : ServerState)
    (env : Environment) (before : State n KemSK) (valid : Valid input before) (prepared : before.flags ready.reference = true) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (simulateQ (liftLocal selected) ((simulateQ (service setup.source wire sign)
        ((RegistrationNativeSecretWordServerMaterial.complete wire reservePeer ready application).run server)).run env)) before := by
  apply RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid
  apply RegistrationNativeSecretWordLiveCaps.local_bound before.flags selected
  exact service_bound before.flags setup.source wire sign _
    (RegistrationNativeSecretWordLiveMaterialCaps.complete_free before.flags wire reservePeer ready application server prepared) env

/-- The literal symbolic Server build uses only live stored references, including one-use take, cancellation and every later failure. -/
theorem build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selected : Bool) (handle : Nat) (application : Option (Slice U8)) (server : ServerState)
    (env : Environment) (before : State n KemSK) (valid : Valid input before)
    (live : RegistrationNativeSecretWordLiveSessions.Live server before.flags) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (simulateQ (liftLocal selected)
        (((RegistrationNativeSecretWordServerCompiler.build setup.source wire checks sign handle application).run server).run env)) before := by
  apply RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid
  apply RegistrationNativeSecretWordLiveCaps.local_bound before.flags selected
  exact service_bound before.flags setup.source wire sign _
    (RegistrationNativeSecretWordLiveMaterialCaps.build_free before.flags wire checks.reservePeer handle application server live) env

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerCaps.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerCaps.admitted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerCaps.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerCaps.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerCaps.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerCaps.build
