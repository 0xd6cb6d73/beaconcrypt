-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildState
import BeaconcryptCore.Computational.RegistrationNativePublicSourceInvariant
import BeaconcryptCore.Computational.RegistrationNativeMainView

/-! Actual typed Server commands of the mixed source client coincide with the native SDK dispatcher. Complete state restoration and the concrete native non-read theorem close the analysis-view input gap; source live roots are the initialized adaptive invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceServerQueries
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore project nativeView Live MemoCorrect)
open RegistrationNativePublicSourceExecution (execute)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationAuthenticationCompiler.program RegistrationServerSdkSource.accept

/-- The actual parsed accept entry, including mandatory verification and every failed reached state, is the full native dispatcher under the named source view. -/
theorem accept_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (packet : registration.InitPacket) (before : State n KemSK source) :
    Prod.map id (fun after => project (RegistrationNativePublicSourceState.roots setup created.seed scalar) scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept publicPrekey (.inr (.accept packet)))).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created source credential (.inr (.accept packet))).run
          (restore (RegistrationNativePublicSourceState.roots setup created.seed scalar) scalar before.1 before.2) := by
  let changed : State n KemSK source := ({ before.1 with parsedAccepts := before.1.parsedAccepts + 1 }, before.2)
  have actual := congrArg (fun distribution => Prod.map id nativeView <$> distribution)
    (RegistrationNativePublicSourceAcceptState.accept_native setup (RegistrationNativeWire.ledgerCodec wire) wire checks route
      (RegistrationNativeMldsa.owned source credential) source.verify representation correct created scalar
      (decide (before.1.parsedAccepts = selectedAccept)) packet changed)
  have folded : (RegistrationNativeExperiment.server
      (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify representation created packet)).run
      (RegistrationNativePublicSourceAcceptState.project setup created.seed scalar changed) =
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential (.inr (.accept packet))).run
        (RegistrationNativePublicSourceAcceptState.project setup created.seed scalar before) := by
    simp only [RegistrationNativeExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind]
    rfl
  rw [folded] at actual
  have equalView : nativeView (RegistrationNativePublicSourceAcceptState.project setup created.seed scalar before) =
      nativeView (restore (RegistrationNativePublicSourceState.roots setup created.seed scalar) scalar before.1 before.2) :=
    RegistrationNativePublicSourceAcceptState.view_project setup created.seed scalar before
  have stable := RegistrationNativeMainView.handler_input (n := n) setup checks wire route representation created credential (.inr (.accept packet))
  calc
    _ = Prod.map id nativeView <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created source credential (.inr (.accept packet))).run
          (RegistrationNativePublicSourceAcceptState.project setup created.seed scalar before) := by
      rw [RegistrationNativePublicSourceInvariant.accept_run]
      have normalized := actual
      simp only [Functor.map_map, Prod.map_def, id_eq,
        RegistrationNativePublicSourceAcceptState.view_project, changed] at normalized
      convert normalized using 1 <;> rfl
    _ = _ := by
      rw [stable, equalView]
      exact (stable _).symm

/-- An actual live build executes the native SDK entry with the same original one-use, signature, codec and publication failures. -/
theorem build_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK source) (live : Live before.1 before.2)
    (correct : MemoCorrect setup created.seed scalar before.2.roots) :
    Prod.map id (fun after => project (RegistrationNativePublicSourceState.roots setup created.seed scalar) scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept publicPrekey (.inr (.build handle application)))).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created source credential (.inr (.build handle application))).run
          (restore (RegistrationNativePublicSourceState.roots setup created.seed scalar) scalar before.1 before.2) := by
  exact RegistrationNativePublicSourceBuildState.build_literal setup wire checks route
    (RegistrationNativeMldsa.owned source credential) created.seed scalar handle application before live correct

end BeaconcryptCore.Computational.RegistrationNativePublicSourceServerQueries
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceServerQueries.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceServerQueries.accept_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceServerQueries.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceServerQueries.build_source
