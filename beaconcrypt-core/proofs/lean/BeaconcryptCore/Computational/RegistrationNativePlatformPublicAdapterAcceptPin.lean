-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions
import BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
/-! The actual returned acceptance slot contains the agreement from that callback's actual authentication. Its selected Server binding and ML public key are retained without requiring equality of the separately recomputed fingerprint. These are exactly the pin coordinates read by the unsigned authentication transcript. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec Checks)
attribute [local irreducible] RegistrationAuthenticationExecutor.begin
variable {n :Nat} {I KemSK Reader Response P R :Type} {base :OracleSpec I}
variable (coins :QueryImpl unifSpec (StateT P ProbComp))
variable (setup :Setup base KemSK) (codec :Codec Reader Response) (checks :Checks)
variable (reserve :StateT P ProbComp Bool) (route :RawCtxServerRouting.SenderDecoder) (verify :MldsaTranscriptAuth.Verify)
variable (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

/-- An exact successful returned slot belongs to this retention, even if an equal-valued token was already present. -/
theorem retain (accepted :agreement.ServerAgreement) (before after :RegistrationServerFrontendCompiler.State n)
    (previous next :P) (index :Nat) (token :peer.ConsumedRegistration)
    (supported :((.ok (some index),after),next)∈support (((RegistrationNativePlatformServerSdk.liftNative coins
      (RegistrationServerNativeSource.retain created accepted)).run before).run previous))
    (row :after.sessions[index]?=some (some token)) :token.agreement=accepted :=by
  have original:=RegistrationNativePlatformHashReceipt.native_support coins
    ((RegistrationServerNativeSource.retain created accepted).run before) (.ok (some index),after) previous next supported
  rw [AdapterPublicServerRetain.native] at original
  simp only [support_pure,Set.mem_singleton_iff,Prod.mk.injEq,RustM.ok.injEq] at original
  obtain ⟨handle,same⟩:=original
  subst after
  unfold AdapterPublicServerRetain.handle at handle
  split at handle
  · cases handle
  · have chosen :index=before.sessions.length:=Option.some.inj handle
    subst index
    simp only [AdapterPublicServerRetain.after] at row
    split at row
    · contradiction
    · simp only [List.getElem?_append_right (show before.sessions.length≤before.sessions.length from le_refl _),Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at row
      exact congrArg peer.ConsumedRegistration.agreement row.symm

/-- The actual agreement and successful replay insertion retain the authenticated binding in the returned slot. -/
theorem after_authentication (packet :registration.InitPacket) (authenticated :registration.AuthenticatedInit)
    (before after :RegistrationServerFrontendCompiler.State n) (previous next :P) (index :Nat) (token :peer.ConsumedRegistration)
    (supported :((.ok (some index),after),next)∈support (((RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks
      (StateT.lift reserve) representation created packet authenticated).run before).run previous))
    (row :after.sessions[index]?=some (some token)) :token.agreement.binding=authenticated.binding :=by
  rw [RegistrationNativePlatformServerSdk.afterAuthentication_run] at supported
  split at supported
  · simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq,RustM.ok.injEq,reduceCtorEq,false_and] at supported
  · simp only [StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨allocated,called,continued⟩:=supported
    simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at called
    obtain ⟨admitted,_reserved,rfl⟩:=called
    cases flag:admitted.1 with
    | false=>simp only [flag,Bool.false_eq_true,ite_false,StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq,RustM.ok.injEq,reduceCtorEq,false_and] at continued
    | true=>
      simp only [flag,ite_true,StateT.run_bind,mem_support_bind_iff] at continued
      obtain ⟨completed,agreed,later⟩:=continued
      cases effectEq:completed.1.1 with
      | fail error | div=>
        simp only [effectEq,StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq,reduceCtorEq,false_and] at later
      | ok phase=>cases phase with
        | ServerComplete accepted=>
          simp only [effectEq] at later
          have tokenEq:=retain coins created accepted completed.1.2 after completed.2 next index token later row
          have called:=RegistrationNativePlatformHashReceipt.native_support coins
            ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)
            completed.1 admitted.2 completed.2 agreed
          change (completed.1.1,completed.1.2)∈_ at called
          rw [effectEq] at called
          obtain ⟨receipt⟩:=RegistrationNativeTokenRootReceipt.agree setup checks representation created packet authenticated accepted before completed.1.2 called
          rw [tokenEq,receipt.completedEq]
        | _=>simp only [effectEq,StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq,RustM.ok.injEq,reduceCtorEq,false_and] at later

theorem authenticate (pin :session.ServerAuthenticationPin) (packet :registration.InitPacket)
    (before after :RegistrationServerFrontendCompiler.State n) (previous next :P)
    (events :List RegistrationAuthenticationFlow.Event) (authenticated :registration.AuthenticatedInit)
    (supported :((.ok (events,.Accepted authenticated),after),next)∈support
      (((RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run before).run previous)) :
    authenticated.binding.server_pin.binding=pin.binding ∧authenticated.binding.server_pin.public_key=pin.public_key :=by
  rw [RegistrationNativePlatformSourceAccept.authenticate_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  have original:=RegistrationNativePlatformHashReceipt.native_support coins
    ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before.world.world.1) inner.1 previous inner.2 called
  have replyEq :inner.1.1=.ok (events,.Accepted authenticated):=congrArg (fun value=>value.1.1) same
  change (inner.1.1,inner.1.2)∈_ at original
  rw [replyEq] at original
  have actual:=RegistrationWorldAuthentication.begin_native_support setup codec route verify pin packet before.world.world.1 inner.1.2 events authenticated original
  exact RegistrationAuthenticationNative.begin_selected_pin setup.source.crypto verify codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
    pin packet (RegistrationWorldAuthentication.project before.world.world.1) (RegistrationWorldAuthentication.project inner.1.2) events authenticated actual

theorem pin (before after :RegistrationServerFrontendCompiler.State n) (previous next :P) (selected :session.ServerAuthenticationPin)
    (supported :((.ok (.Some selected),after),next)∈support
      (((RegistrationNativePlatformSourceBuild.pin coins).run before).run previous)) :
    selected.binding=before.pin.binding ∧selected.public_key=before.pin.public_key :=by
  change ((.ok (.Some selected),after),next)∈support
    (((fun inner=>(inner.1,{before with world:={before.world with world:=(inner.2,before.world.world.2)}})) <$>
      simulateQ coins ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run before.world.world.1)).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  have original:=RegistrationNativePlatformHashReceipt.native_support coins
    ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run before.world.world.1) inner.1 previous inner.2 called
  have replyEq :inner.1.1=.ok (.Some selected):=congrArg (fun value=>value.1.1) same
  change (inner.1.1,inner.1.2)∈_ at original
  rw [replyEq,RegistrationNativeServerPinRecompute.native_run] at original
  simp only [support_pure,Set.mem_singleton_iff,Prod.mk.injEq,RustM.ok.injEq,core.option.Option.Some] at original
  have selectedEq:=Option.some.inj original.1
  cases selectedEq
  exact ⟨rfl,rfl⟩

theorem after_pin (selected :session.ServerAuthenticationPin) (packet :registration.InitPacket)
    (before after :RegistrationServerFrontendCompiler.State n) (previous next :P) (index :Nat) (token :peer.ConsumedRegistration)
    (supported :((.ok (some index),after),next)∈support (((RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks
      (StateT.lift reserve) route verify representation created packet (.ok (.Some selected))).run before).run previous))
    (row :after.sessions[index]?=some (some token)) :
    token.agreement.binding.server_pin.binding=selected.binding ∧token.agreement.binding.server_pin.public_key=selected.public_key :=by
  simp only [RegistrationNativePlatformSourceAccept.afterPin,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨checked,called,later⟩:=supported
  cases checkEq:checked.1.1 with
  | fail error | div=>simp only [checkEq,StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq,reduceCtorEq,false_and] at later
  | ok checkedValue=>
    rcases checkedValue with ⟨events,phase⟩
    cases phase with
    | Accepted authenticated=>
      simp only [checkEq] at later
      have bindingEq:=after_authentication coins setup checks reserve representation created packet authenticated checked.1.2 after checked.2 next index token later row
      have checkedSupport:=called
      change ((checked.1.1,checked.1.2),checked.2)∈_ at checkedSupport
      rw [checkEq] at checkedSupport
      have selectedEq:=authenticate coins setup codec route verify selected packet before checked.1.2 previous checked.2 events authenticated checkedSupport
      rw [bindingEq]
      exact selectedEq
    | _=>simp only [checkEq,StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq,RustM.ok.injEq,reduceCtorEq,false_and] at later

/-- Successful source acceptance supplies the exact two pin operands in its newly returned slot. -/
theorem accept (packet :registration.InitPacket) (before after :RegistrationServerFrontendCompiler.State n)
    (previous next :P) (index :Nat) (token :peer.ConsumedRegistration)
    (supported :((.ok (some index),after),next)∈support (((RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve
      route verify representation created packet).run before).run previous))
    (row :after.sessions[index]?=some (some token)) :
    token.agreement.binding.server_pin.binding=before.pin.binding ∧token.agreement.binding.server_pin.public_key=before.pin.public_key :=by
  simp only [RegistrationNativePlatformSourceAccept.accept,RegistrationNativePlatformSourceAccept.acceptWith,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨pinned,called,later⟩:=supported
  cases pinEq:pinned.1.1 with
  | fail error | div=>simp only [RegistrationNativePlatformSourceAccept.afterPin,pinEq,StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq,reduceCtorEq,false_and] at later
  | ok optional=>cases optional with
    | none=>simp only [RegistrationNativePlatformSourceAccept.afterPin,pinEq,StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq,RustM.ok.injEq,reduceCtorEq,false_and] at later
    | some selected=>
      simp only [pinEq] at later
      have coordinates:=after_pin coins setup codec checks reserve route verify representation created selected packet pinned.1.2 after pinned.2 next index token later row
      have pinSupport:=called
      change ((pinned.1.1,pinned.1.2),pinned.2)∈_ at pinSupport
      rw [pinEq] at pinSupport
      have selectedEq:=pin coins before pinned.1.2 previous pinned.2 selected pinSupport
      exact ⟨coordinates.1.trans selectedEq.1,coordinates.2.trans selectedEq.2⟩

variable {source :RegistrationNativeMldsa.Source}
theorem native [ed :AdapterInitEdPrimitive.Operations]
    (functional :RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (input :Slice U8) (before after :RegistrationNativeExperiment.State n KemSK source) (previous next :P) (index :Nat) (token :peer.ConsumedRegistration)
    (supported :((.ok (some index),after),next)∈support (((RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks reserve
      route verify representation created input).run before).run previous))
    (row :after.server.sessions[index]?=some (some token)) :
    token.agreement.binding.server_pin.binding=before.server.pin.binding ∧token.agreement.binding.server_pin.public_key=before.server.pin.public_key :=by
  cases decoded:RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>simp only [RegistrationNativePlatformExtractedSdkServer.Accept.native,decoded,StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq,RustM.ok.injEq,reduceCtorEq,false_and] at supported
  | some packet=>
    simp only [RegistrationNativePlatformExtractedSdkServer.Accept.native,decoded,StateT.run_bind,StateT.run_modify,pure_bind] at supported
    rw [RegistrationNativePlatformExtractedAuthentication.accept_source coins setup codec route verify checks representation created functional reserve packet,
      AdapterPublicServerSourceLens.server_run,StateT.run_map,support_map] at supported
    obtain ⟨inner,called,same⟩:=supported
    have replyEq :inner.1.1=.ok (some index):=congrArg (fun value=>value.1.1) same
    have serverEq :inner.1.2=after.server:=congrArg (fun value=>value.1.2.server) same
    have platformEq :inner.2=next:=congrArg Prod.snd same
    change ((inner.1.1,inner.1.2),inner.2)∈_ at called
    rw [replyEq,serverEq,platformEq] at called
    exact accept coins setup codec checks reserve route verify representation created packet before.server after.server previous next index token called row

variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]

/-- The same returned source token inherits those two pin coordinates through its literal material row. -/
theorem returned_source (view :AdapterPublicWrapperState.MaterialView source KemSK) (views :AdapterPublicWrapperStorage.Views)
    (credential :RegistrationNativeMldsa.Credential source)
    (functional :RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (input :Slice U8) (before after :RegistrationNativeExperiment.State n KemSK source) (previous next :P) (index :Nat)
    (held :RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential (after,next))
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (found :held.objects.tokens index=some token)
    (supported :((.ok (some index),after),next)∈support (((RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks reserve
      route verify representation created input).run before).run previous)) :
    token.registration.agreement.binding.server_pin.binding=before.server.pin.binding ∧
      token.registration.agreement.binding.server_pin.public_key=before.server.pin.public_key :=by
  have table:=held.tokens index
  cases selected:after.server.sessions[index]? with
  | none=>simp only [selected] at table;rw [found] at table;cases table
  | some optional=>cases optional with
    | none=>simp only [selected] at table;rw [found] at table;cases table
    | some consumed=>
      simp only [selected] at table
      obtain ⟨original,same,related⟩:=table
      have tokenEq :original=token:=Option.some.inj (same.symm.trans found)
      subst original
      rw [related.1]
      exact native coins setup codec checks reserve route verify representation created functional input before after previous next index consumed supported selected

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.after_authentication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.authenticate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.after_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.returned_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptPin.returned_source
