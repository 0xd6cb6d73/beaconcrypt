-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendProgram
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety

/-! Concrete typed command safety follows from actual zero-demand bills, the live one-use Server session table, and the transient Beacon preparation receipt. Adaptive composition uses only supported reached continuations of the same checked interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
open RegistrationNativeSecretWordLiveFrontendState (Good)
open RegistrationNativeSecretWordInterface (Spec)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)

/-- A pure result observation adds no material request and retains actual reached preparation safety. -/
theorem mapped (work : OracleComp (Spec n KemSK) Value) (observe : Value → Next)
    (before : State n KemSK) (valid : RegistrationNativeSecretWordLiveFlags.Valid input before)
    (safe : AllPrepared input (handlerChecked setup wire route sign input inside provider) work before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider) (observe <$> work) before := by
  rw [← bind_pure_comp]
  apply RegistrationNativeSecretWordLivePrefix.bind input (handlerChecked setup wire route sign input inside provider) work _ before safe
  intro result supported
  have reached := RegistrationNativeSecretWordLiveFlags.program_receipts setup wire route sign input inside provider work before valid result supported
  exact RegistrationNativeSecretWordLiveCaps.no_demand setup wire route sign input inside provider (pure (observe result.1)) result.2 reached.1 (by trivial)

private theorem quiet (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (current : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (free : ¬ RegistrationNativeSecretWordFrontendCaps.IsMaterial current)
    (before : RegistrationNativeSecretWordMessage.State source) (context : State n KemSK)
    (good : Good input before context) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey current).run before) context := by
  apply RegistrationNativeSecretWordLiveCaps.no_demand setup wire route sign input inside provider _ context good.1
  have bounded := RegistrationNativeSecretWordFrontendCaps.handler_bound (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey current before
  simpa only [ite_eq_right free] using bounded

/-- The actual one-use Server build is preparation-safe from its internally maintained live capability table. -/
theorem build (checks : Checks) (source : RegistrationNativeMldsa.Source) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeSecretWordMessage.State source) (context : State n KemSK)
    (good : Good input before context) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      ((RegistrationNativeSecretWordFrontend.serverOpen false
        (RegistrationNativeSecretWordServerCompiler.build (n := n) setup.source wire checks sign handle application)).run before) context := by
  apply mapped setup wire route sign input inside provider _ _ context good.1
  exact RegistrationNativeSecretWordLiveServerCaps.build setup checks wire route sign input inside provider false handle application before.server before.environment context good.1 good.2

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

/-- Every actual typed command is preparation-safe from the initialized internal invariant; no command supplies an arbitrary material reference. -/
theorem query (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (current : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeSecretWordMessage.State source) (context : State n KemSK)
    (good : Good input before context) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey current).run before) context := by
  cases current with
  | inl coin =>
      apply quiet setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey _ ?_ before context good
      simp only [RegistrationNativeSecretWordFrontendCaps.IsMaterial, not_false_eq_true]
  | inr command => cases command with
    | build handle application => exact build setup wire route sign input inside provider checks source handle application before context good
    | finish index packet =>
        apply mapped setup wire route sign input inside provider _ _ context good.1
        exact RegistrationNativeSecretWordLiveBeaconSafety.owners setup wire route sign input inside provider source index packet before.beacons before.environment context good.1
    | _ =>
        apply quiet setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey _ ?_ before context good
        simp only [RegistrationNativeSecretWordFrontendCaps.IsMaterial, not_false_eq_true]

/-- Preparation safety holds throughout every actual adaptive typed execution from its concrete live-session invariant. -/
theorem program (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeSecretWordMessage.State source) (context : State n KemSK)
    (good : Good input before context) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      ((simulateQ (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before) context := by
  induction work using OracleComp.inductionOn generalizing before context with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact RegistrationNativeSecretWordLiveCaps.no_demand setup wire route sign input inside provider _ context good.1 (by trivial)
  | query_bind current next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply RegistrationNativeSecretWordLivePrefix.bind input (handlerChecked setup wire route sign input inside provider) _ _ context
        (query setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey current before context good)
      intro reached called
      have nextGood := RegistrationNativeSecretWordLiveFrontendPost.query setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey current before context good reached called
      exact ih reached.1.1 reached.1.2 reached.2 nextGood

/-- Actual cold initialization and the literal original full native ledger derive every reached material demand's preparation receipt internally. -/
theorem run (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeSecretWordMessage.State source) (empty : before.server.sessions = [])
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before)
      (RegistrationNativeSecretWordInterpreter.initial ordinary kem) :=
  program setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) before _
    (RegistrationNativeSecretWordLiveFrontendProgram.initial source input before empty ordinary kem)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.mapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.mapped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety.run
