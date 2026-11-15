-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax
/-! The complete corrected accept is transported through its existing exact free controller syntax. Every primitive request uses the real indexed source dictionary and the public reserve uses the same persistent external state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceAccept
attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceEffects (Extra Private)
open RegistrationNativePublicSourceCallbacks (services remember)
open RegistrationNativePlatformPublicSourceLocal (external interpret)
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι}

noncomputable def actualCallbacks (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra (StateT Platform ProbComp) :=
  RegistrationNativePlatformServerOpenSource.callbacks setup seed scalar remember (services setup wire route sign seed scalar)
    (fun query => RegistrationNativePlatformInterpret.state external ((services setup wire route sign seed scalar).demand query))
    (fun query => RegistrationNativePlatformInterpret.state external ((services setup wire route sign seed scalar).publication query))

noncomputable def actual (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :=
  RegistrationNativePlatformServerOpenKernel.handler (external (Platform := Platform)) setup
    (actualCallbacks (n := n) setup wire route sign seed scalar)

private theorem callbacks_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativePlatformServerOpenKernel.liftCallbacks external
      (RegistrationServerOpenReferenceSourceStage.callbacks setup seed scalar remember (services setup wire route sign seed scalar)) =
      actualCallbacks (Platform := Platform) (n := n) setup wire route sign seed scalar := by
  have preparation : (fun query => RegistrationNativePlatformInterpret.state (external (Platform := Platform))
      (RegistrationServerOpenReferenceSourceStage.prepare (n := n) setup seed scalar remember query)) =
      RegistrationNativePlatformServerOpenSource.prepare setup seed scalar remember :=
    funext fun query => (RegistrationNativePlatformServerOpenSource.prepare_lift external setup seed scalar remember query).symm
  dsimp only [RegistrationNativePlatformServerOpenKernel.liftCallbacks,
    RegistrationServerOpenReferenceSourceStage.callbacks, actualCallbacks, RegistrationNativePlatformServerOpenSource.callbacks]
  rw [preparation]

private theorem query_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (query : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain) :
    interpret (Platform := Platform) setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.localHandler selected query) =
      actual setup wire route sign seed scalar query := by
  rw [RegistrationNativePlatformPublicSourceLocal.handler_source]
  have lifted := RegistrationNativePlatformServerOpenKernel.handler_lift (external (Platform := Platform)) setup
    (RegistrationServerOpenReferenceSourceStage.callbacks setup seed scalar remember (services setup wire route sign seed scalar)) query
  rw [callbacks_source] at lifted
  exact lifted.symm

private theorem interpret_program {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (implementation : QueryImpl spec (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform))
    (work : OracleComp spec Value) :
    interpret setup wire route sign seed scalar (simulateQ implementation work) =
      simulateQ (fun query => interpret setup wire route sign seed scalar (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact RegistrationNativePlatformPublicSourceLocal.interpret_pure setup wire route sign seed scalar value
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPublicSourceLocal.interpret_bind, ih]

noncomputable def syntaxBase (selected : Bool) (reserve : StateT Platform ProbComp Bool) :
    QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform)
  | .inl query => RegistrationNativePlatformPublicFrontend.localHandler selected query
  | .inr () => RegistrationNativePlatformPublicFrontend.platform reserve

noncomputable def syntaxActual (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (reserve : StateT Platform ProbComp Bool) :
    QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (StateT (Private n KemSK) (StateT Platform ProbComp))
  | .inl query => actual setup wire route sign seed scalar query
  | .inr () => StateT.lift reserve

private theorem syntax_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) :
    (fun query => interpret setup wire route sign seed scalar (syntaxBase (n := n) (KemSK := KemSK) selected reserve query)) =
      syntaxActual setup wire route sign seed scalar reserve := by
  funext query
  cases query with
  | inl query => exact query_source setup wire route sign seed scalar selected query
  | inr query => cases query; exact RegistrationNativePlatformPublicSourceLocal.interpret_platform setup wire route sign seed scalar reserve

/-- The full corrected accept body has the actual source interpretation, with no controller correspondence supplied as a premise. -/
theorem accept (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (front : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) :
    interpret (n := n) setup wire route sign seed scalar
      (((RegistrationNativePlatformServerOpenControl.accept
        (RegistrationNativePlatformPublicFrontend.localHandler selected)
        (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet).run front).run env) =
    (((RegistrationNativePlatformServerOpenControl.accept
      (actual (n := n) setup wire route sign seed scalar) (StateT.lift reserve) setup checks verify packet).run front).run env) := by
  have first := congrArg (fun work => ((work.run front).run env))
    (RegistrationNativePlatformServerOpenSyntax.accept_source
      (syntaxBase (n := n) (KemSK := KemSK) selected reserve) setup checks verify packet)
  have last := congrArg (fun work => ((work.run front).run env))
    (RegistrationNativePlatformServerOpenSyntax.accept_source
      (syntaxActual (n := n) setup wire route sign seed scalar reserve) setup checks verify packet)
  change simulateQ (syntaxBase selected reserve)
    (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run front).run env) =
    (((RegistrationNativePlatformServerOpenControl.accept
      (RegistrationNativePlatformPublicFrontend.localHandler selected)
      (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet).run front).run env) at first
  change simulateQ (syntaxActual setup wire route sign seed scalar reserve)
    (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run front).run env) =
    (((RegistrationNativePlatformServerOpenControl.accept (actual (n := n) setup wire route sign seed scalar)
      (StateT.lift reserve) setup checks verify packet).run front).run env) at last
  rw [← first, interpret_program, syntax_source]
  exact last


private theorem close_run {A : Type}
    (work : RegistrationNativePlatformServerReferenceAccept.PublicM (StateT (Private n KemSK) (StateT Platform ProbComp)) A)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment)
    (before : Private n KemSK) (previous : Platform) :
    (((RegistrationNativePlatformServerOpenControl.close work).run (front, (env, before))).run previous) =
      (fun result => ((result.1.1.1.1, (result.1.1.1.2, (result.1.1.2, result.1.2))), result.2)) <$>
        ((((work.run front).run env).run before).run previous) := by
  change ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun result => (result.1.1, (result.1.2, result.2))) <$>
      (((work.run front).run env).run before))).run previous = _
  rw [StateT.run_map, StateT.run_map, Functor.map_map]

/-- A returned token in the new adaptive source interpreter is backed by the literal root in that same run's private memo. -/
theorem receipt (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (front after : RegistrationServerMaterialFrontend.State)
    (env nextEnv : RegistrationServerReferenceCompiler.Environment) (before next : Private n KemSK)
    (previous nextPlatform : Platform) (handle : Nat)
    (supported : ((((.ok (some handle), after), nextEnv), next), nextPlatform) ∈ support
      (((interpret setup wire route sign seed scalar
        (((RegistrationNativePlatformServerOpenControl.accept
          (RegistrationNativePlatformPublicFrontend.localHandler selected)
          (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet).run front).run env)).run before).run previous)) :
    ∃ ready root, after.sessions[handle]? = some (some ready) ∧ next.extra.1 ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [accept] at supported
  have reached : ((.ok (some handle), (after, (nextEnv, next))), nextPlatform) ∈ support
      (((RegistrationNativePlatformServerOpenControl.close
        (RegistrationNativePlatformServerOpenControl.accept (actual setup wire route sign seed scalar) (StateT.lift reserve)
          setup checks verify packet)).run (front, (env, before))).run previous) := by
    rw [close_run, support_map]
    exact ⟨((((.ok (some handle), after), nextEnv), next), nextPlatform), supported, rfl⟩
  exact RegistrationNativePlatformServerAcceptMemo.accept external setup checks verify seed scalar
    (services setup wire route sign seed scalar)
    (fun query => RegistrationNativePlatformInterpret.state external ((services setup wire route sign seed scalar).demand query))
    (fun query => RegistrationNativePlatformInterpret.state external ((services setup wire route sign seed scalar).publication query))
    reserve packet handle (front, (env, before)) (after, (nextEnv, next)) previous nextPlatform reached

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceAccept.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceAccept.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceAccept.receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceAccept.receipt
