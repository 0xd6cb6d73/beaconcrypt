-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication
import BeaconcryptCore.Refinement.AdapterPublicServerRetain
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The actual accept callback preserves every existing one-use session. A successful optional reply appends exactly one consumed token and returns the old successful-session count; every rejection leaves the session list unchanged. Parsed accept coordinates remain separate. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions
attribute [local irreducible] RegistrationAuthenticationExecutor.begin
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {n : Nat} {I KemSK Reader Response P : Type} {base : OracleSpec I}

def Shape (before : List (Option peer.ConsumedRegistration)) (reply : RustM (Option Nat))
    (after : List (Option peer.ConsumedRegistration)) : Prop :=
  match reply with
  | .ok (some index)=>index=before.length ∧∃consumed,after=before++[some consumed]
  | _=>after=before

private theorem pure_shape (value : RustM (Option Nat)) (noHandle : ∀index,value≠.ok (some index))
    (before : RegistrationServerFrontendCompiler.State n) (previous : P)
    (result : (RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)×P)
    (supported : result∈support (((pure value :StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) _).run before).run previous)) :
    Shape before.sessions result.1.1 result.1.2.sessions := by
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  subst result
  cases value with
  | fail error | div=>rfl
  | ok optional=>cases optional with
    | none=>rfl
    | some index=>exact (noHandle index rfl).elim

theorem retain (coins : QueryImpl unifSpec (StateT P ProbComp))
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (accepted : agreement.ServerAgreement)
    (before : RegistrationServerFrontendCompiler.State n) (previous : P)
    (result : (RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)×P)
    (supported : result∈support (((RegistrationNativePlatformServerSdk.liftNative coins
      (RegistrationServerNativeSource.retain created accepted)).run before).run previous)) :
    Shape before.sessions result.1.1 result.1.2.sessions := by
  change result∈support ((simulateQ coins ((RegistrationServerNativeSource.retain created accepted).run before)).run previous) at supported
  rw [AdapterPublicServerRetain.native,simulateQ_pure] at supported
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  subst result
  unfold AdapterPublicServerRetain.handle AdapterPublicServerRetain.after
  split
  · rfl
  · exact ⟨rfl,⟨accepted⟩,rfl⟩

private theorem agreement_sessions (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerFrontendCompiler.State n) (previous : P)
    (result : (RustM agreement.AgreementEffect×RegistrationServerFrontendCompiler.State n)×P)
    (supported : result∈support (((RegistrationNativePlatformServerSdk.liftNative coins
      (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)).run before).run previous)) :
    result.1.2.sessions=before.sessions := by
  have called:=RegistrationNativePlatformHashReceipt.native_support coins
    ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before) result.1 previous result.2 supported
  simp only [RegistrationServerNativeSource.agree,StateT.run,support_map] at called
  obtain ⟨inner,_called,equal⟩:=called
  exact (congrArg (fun pair=>pair.2.sessions) equal).symm

theorem after_authentication (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (reserve : StateT P ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerFrontendCompiler.State n) (previous : P)
    (result : (RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)×P)
    (supported : result∈support (((RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve)
      representation created packet authenticated).run before).run previous)) :
    Shape before.sessions result.1.1 result.1.2.sessions := by
  rw [RegistrationNativePlatformServerSdk.afterAuthentication_run] at supported
  split at supported
  · exact pure_shape (.ok none) (by intro index impossible;cases impossible) before previous result supported
  · simp only [StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨allocated,called,continued⟩:=supported
    simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at called
    obtain ⟨admitted,_reserved,rfl⟩:=called
    cases flag:admitted.1 with
    | false=>
      simp only [flag,Bool.false_eq_true,ite_false] at continued
      exact pure_shape (.ok none) (by intro index impossible;cases impossible) before admitted.2 result continued
    | true=>
      simp only [flag,ite_true,StateT.run_bind,mem_support_bind_iff] at continued
      obtain ⟨completed,agreed,later⟩:=continued
      have same:=agreement_sessions coins setup checks representation created packet authenticated before admitted.2 completed agreed
      rw [←same]
      cases effectEq:completed.1.1 with
      | fail error=>
        simp only [effectEq] at later
        exact pure_shape (.fail error) (by intro index impossible;cases impossible) completed.1.2 completed.2 result later
      | div=>
        simp only [effectEq] at later
        exact pure_shape .div (by intro index impossible;cases impossible) completed.1.2 completed.2 result later
      | ok phase=>cases phase with
        | ServerComplete accepted=>
          simp only [effectEq] at later
          exact retain coins created accepted completed.1.2 completed.2 result later
        | _=>
          simp only [effectEq] at later
          exact pure_shape (.ok none) (by intro index impossible;cases impossible) completed.1.2 completed.2 result later

private theorem authenticate_sessions (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before : RegistrationServerFrontendCompiler.State n) (previous : P)
    (result : (RustM (List RegistrationAuthenticationFlow.Event×registration.InitAuthentication)×RegistrationServerFrontendCompiler.State n)×P)
    (supported : result∈support (((RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run before).run previous)) :
    result.1.2.sessions=before.sessions := by
  rw [RegistrationNativePlatformSourceAccept.authenticate_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,_called,equal⟩:=supported
  cases equal
  rfl

theorem after_pin (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT P ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (pinResult : RustM (core.option.Option session.ServerAuthenticationPin))
    (before : RegistrationServerFrontendCompiler.State n) (previous : P)
    (result : (RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)×P)
    (supported : result∈support (((RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve)
      route verify representation created packet pinResult).run before).run previous)) :
    Shape before.sessions result.1.1 result.1.2.sessions := by
  cases pinResult with
  | fail error=>exact pure_shape (.fail error) (by intro index impossible;cases impossible) before previous result supported
  | div=>exact pure_shape .div (by intro index impossible;cases impossible) before previous result supported
  | ok optional=>cases optional with
    | none=>exact pure_shape (.ok none) (by intro index impossible;cases impossible) before previous result supported
    | some pin=>
      simp only [RegistrationNativePlatformSourceAccept.afterPin,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨checked,called,later⟩:=supported
      have same:=authenticate_sessions coins setup codec route verify pin packet before previous checked called
      rw [←same]
      cases checkEq:checked.1.1 with
      | fail error=>
        simp only [checkEq] at later
        exact pure_shape (.fail error) (by intro index impossible;cases impossible) checked.1.2 checked.2 result later
      | div=>
        simp only [checkEq] at later
        exact pure_shape .div (by intro index impossible;cases impossible) checked.1.2 checked.2 result later
      | ok checkedValue=>
        rcases checkedValue with ⟨events,phase⟩
        cases phase with
        | Accepted authenticated=>
          simp only [checkEq] at later
          exact after_authentication coins setup checks reserve representation created packet authenticated checked.1.2 checked.2 result later
        | _=>
          simp only [checkEq] at later
          exact pure_shape (.ok none) (by intro index impossible;cases impossible) checked.1.2 checked.2 result later

private theorem pin_sessions (coins : QueryImpl unifSpec (StateT P ProbComp))
    (before : RegistrationServerFrontendCompiler.State n) (previous : P)
    (result : (RustM (core.option.Option session.ServerAuthenticationPin)×RegistrationServerFrontendCompiler.State n)×P)
    (supported : result∈support (((RegistrationNativePlatformSourceBuild.pin coins).run before).run previous)) :
    result.1.2.sessions=before.sessions := by
  change result∈support (((fun inner=>(inner.1,{before with world:={before.world with world:=(inner.2,before.world.world.2)}})) <$>
    simulateQ coins ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run before.world.world.1)).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,_called,equal⟩:=supported
  cases equal
  rfl

theorem accept (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT P ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (before : RegistrationServerFrontendCompiler.State n) (previous : P)
    (result : (RustM (Option Nat)×RegistrationServerFrontendCompiler.State n)×P)
    (supported : result∈support (((RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve
      route verify representation created packet).run before).run previous)) :
    Shape before.sessions result.1.1 result.1.2.sessions := by
  simp only [RegistrationNativePlatformSourceAccept.accept,RegistrationNativePlatformSourceAccept.acceptWith,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨pinned,called,later⟩:=supported
  have same:=pin_sessions coins before previous pinned called
  rw [←same]
  exact after_pin coins setup codec checks reserve route verify representation created packet pinned.1.1 pinned.1.2 pinned.2 result later

variable {source : RegistrationNativeMldsa.Source}
theorem native [ed : AdapterInitEdPrimitive.Operations]
    (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT P ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (input : Slice U8) (before : RegistrationNativeExperiment.State n KemSK source) (previous : P)
    (result : (RustM (Option Nat)×RegistrationNativeExperiment.State n KemSK source)×P)
    (supported : result∈support (((RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks reserve route verify representation created input).run before).run previous)) :
    Shape before.server.sessions result.1.1 result.1.2.server.sessions := by
  cases decoded:RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>
    simp only [RegistrationNativePlatformExtractedSdkServer.Accept.native,decoded,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    subst result
    rfl
  | some packet=>
    simp only [RegistrationNativePlatformExtractedSdkServer.Accept.native,decoded,StateT.run_bind,StateT.run_modify,pure_bind] at supported
    rw [RegistrationNativePlatformExtractedAuthentication.accept_source coins setup codec route verify checks representation created functional reserve packet] at supported
    rw [AdapterPublicServerSourceLens.server_run,StateT.run_map,support_map] at supported
    obtain ⟨inner,called,equal⟩:=supported
    cases equal
    exact accept coins setup codec checks reserve route verify representation created packet before.server previous inner called

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.retain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.after_authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.after_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions.native
