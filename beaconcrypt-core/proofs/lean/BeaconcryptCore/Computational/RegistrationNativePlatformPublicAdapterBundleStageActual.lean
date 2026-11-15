-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut
/-! The logged Bundle source publication executes request-only signing using the actual preceding source hash. Its source dictionary and private chronological log are executed once; erasing the private hash cut gives the same jointly logged publication tree. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageActual
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (recorded)
local notation "Cut"=>RegistrationNativePlatformCutJournal.State
variable {S E Log :Type} {m :Type→Type} [Monad m] [LawfulMonad m]
abbrev Spec (E :Type):=RegistrationNativePlatformWriter.Spec E

noncomputable def publication (implementation :QueryImpl (Spec E) (StateT S m))
    (observe :(query :(Spec E).Domain)→(Spec E).Range query→List Log)
    (control :pqxdh.BeaconFresh) (inputs :pqxdh.BeaconStartInputs) (scalar :pqxdh.BeaconCoins)
    (pin :session.ServerAuthenticationPin)
    (before :S×List Log) :m (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))×(S×List Log)) :=
  Prod.map id Prod.fst <$>
    (RegistrationNativePlatformBeaconPublication.begin
      (RegistrationNativePlatformCutJournal.extended
        (RegistrationNativePlatformCutJournal.source
          (fun query=>recorded implementation observe (.inl (.inl query))) (fun _=>pure .None))
        (fun query=>RegistrationNativePlatformCutJournal.liftNative (recorded implementation observe (.inl (.inr query)))))
      (fun signed=>simulateQ (fun query=>RegistrationNativePlatformCutJournal.liftNative (recorded implementation observe (.inr query)))
        (AdapterRegistrationWriterRequestExtraction.encodeInit (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.initPacket signed)).run)
      control inputs scalar pin).run (before,none)

theorem source (implementation :QueryImpl (Spec E) (StateT S m))
    (observe :(query :(Spec E).Domain)→(Spec E).Range query→List Log)
    (control :pqxdh.BeaconFresh) (inputs :pqxdh.BeaconStartInputs) (scalar :pqxdh.BeaconCoins)
    (pin :session.ServerAuthenticationPin) (before :S×List Log) :
    publication implementation observe control inputs scalar pin before=
      (simulateQ (recorded implementation observe) (RegistrationNativePlatformWriter.begin E control inputs scalar pin)).run before :=by
  have actual:=congrArg (fun work=>Prod.map id Prod.fst <$>work.run (before,none))
    (RegistrationNativePlatformPublicAdapterBundleStageCut.actual (recorded implementation observe) (fun _=>pure .None)
      control inputs scalar pin)
  have associated:=congrArg (fun tree=>Prod.map id Prod.fst <$>tree)
    (RegistrationNativePlatformPublicAdapterBundleStageCut.associate_program implementation observe
      (RegistrationNativePlatformWriter.begin E control inputs scalar pin) ((before.1,none),before.2))
  have erased:=RegistrationNativePlatformPublicAdapterBundleStageCut.logged_source implementation observe
    (RegistrationNativePlatformWriter.begin E control inputs scalar pin) ((before.1,none),before.2)
  simp only [Functor.map_map,Prod.map,RegistrationNativePlatformPublicAdapterCutLogAssociation.associate,id_eq] at associated erased
  exact actual.symm.trans (associated.symm.trans erased)
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageActual
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageActual.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageActual.source
