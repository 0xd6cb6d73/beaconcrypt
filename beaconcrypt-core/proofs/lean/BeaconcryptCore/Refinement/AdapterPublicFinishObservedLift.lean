-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody
import BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable {m :Type→Type} [Monad m] [LawfulMonad m] {Log A B :Type}

def lift (work :RustT m A) :RustT (StateT (List Log) m) A:=⟨StateT.lift work.run⟩

theorem pure (value :A) :lift (Log:=Log) (Pure.pure value:RustT m A)=Pure.pure value:=by
  apply RustT.ext
  exact (monadLift_pure (m:=m) (n:=StateT (List Log) m) (RustM.ok value))

theorem bind (work :RustT m A) (next :A→RustT m B) :
    lift (Log:=Log) (work >>=next)=(lift work >>=fun value=>lift (next value)):=by
  apply RustT.ext
  change StateT.lift (work.run >>=fun result=>match result with
    | .ok value=>(next value).run
    | .fail error=>Pure.pure (.fail error)
    | .div=>Pure.pure .div)=_
  rw [show (StateT.lift (work.run >>=fun result=>match result with
    | .ok value=>(next value).run
    | .fail error=>Pure.pure (.fail error)
    | .div=>Pure.pure .div):StateT (List Log) m _)=
      (StateT.lift work.run >>=fun result=>StateT.lift (match result with
        | .ok value=>(next value).run
        | .fail error=>Pure.pure (.fail error)
        | .div=>Pure.pure .div)) from monadLift_bind (m:=m) (n:=StateT (List Log) m) work.run (fun result=>match result with
        | .ok value=>(next value).run
        | .fail error=>Pure.pure (.fail error)
        | .div=>Pure.pure .div)]
  apply bind_congr
  intro result
  cases result with
  | ok value=>rfl
  | fail error=>exact monadLift_pure (m:=m) (n:=StateT (List Log) m) (RustM.fail error:RustM B)
  | div=>exact monadLift_pure (m:=m) (n:=StateT (List Log) m) (RustM.div:RustM B)

theorem rust (result :RustM A) :
    lift (Log:=Log) (AdapterRecordRequestMonad.liftRust result:RustT m A)=AdapterRecordRequestMonad.liftRust result:=by
  apply RustT.ext
  exact (monadLift_pure (m:=m) (n:=StateT (List Log) m) result)

theorem map (f:A→B) (work:RustT m A) :lift (Log:=Log) (f <$>work)=f <$>lift work:=by
  simp only [←bind_pure_comp,bind,pure]

@[instance_reducible] def transformation :AdapterPublicAgreementMonadMap.Transformation m (StateT (List Log) m) where
  transform:=lift
  lawful:=Cslib.IsMonadHom.mk' pure bind
  lift:=rust

variable [material :PublicWrapperPlatform.Material] [ed :AdapterInitEdPrimitive.Operations]
variable [original :CryptoOperations (RustT m)]
@[instance_reducible] def cryptography :CryptoOperations (RustT (StateT (List Log) m)):=
  letI :AdapterPublicAgreementMonadMap.Transformation m (StateT (List Log) m):=transformation
  AdapterPublicAgreementMonadCrypto.operations original

variable {I KemSK :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}

variable [PublicWrapperPlatform.CryptoOperations]

theorem agreement (setup :PqxdhServerAuthExperiment.Setup base KemSK) (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (model :AdapterPublicAgreementCommonModel.Model (m:=m) setup view)
    (keys :AdapterPublicAgreementFields.Keys) (authenticated :registration.AuthenticatedResponse) :
    letI :CryptoOperations (RustT (StateT (List Log) m)):=cryptography
    ((do let phase←AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
         beaconcrypt_public_request.pqxdh.execute_beacon_agreement phase keys):RustT (StateT (List Log) m) agreement.AgreementEffect).run=
      StateT.lift (simulateQ (AdapterPublicAgreementCapture.implementation model keys) (RegistrationAgreementExecutor.beacon authenticated)) :=by
  let :AdapterPublicAgreementMonadMap.Transformation m (StateT (List Log) m):=transformation
  let :CryptoOperations (RustT (StateT (List Log) m)):=cryptography
  have mapped:=AdapterPublicAgreementMonadInterpreter.entry (left:=m) (right:=StateT (List Log) m)
    beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError keys (agreement.begin_beacon_agreement authenticated) ()
  have cast (a:agreement.AgreementEffect) :
      beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m:=RustT (StateT (List Log) m)) a keys=
        Prod.fst <$>beaconcrypt_public_request.pqxdh.execute_agreement beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError a keys ():=rfl
  have sourceCast (a:agreement.AgreementEffect) :
      beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m:=RustT m) a keys=
        Prod.fst <$>beaconcrypt_public_request.pqxdh.execute_agreement beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError a keys ():=rfl
  let baseRun :RustT m agreement.AgreementEffect:=do
    let phase←AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
    beaconcrypt_public_request.pqxdh.execute_beacon_agreement phase keys
  let loggedRun :RustT (StateT (List Log) m) agreement.AgreementEffect:=do
    let phase←AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
    beaconcrypt_public_request.pqxdh.execute_beacon_agreement phase keys
  let sourceFull :RustT m (agreement.AgreementEffect×Unit):=do
    let phase←AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
    beaconcrypt_public_request.pqxdh.execute_agreement beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError phase keys ()
  let loggedFull :RustT (StateT (List Log) m) (agreement.AgreementEffect×Unit):=do
    let phase←AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
    beaconcrypt_public_request.pqxdh.execute_agreement beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError phase keys ()
  have fullEq:loggedFull=lift sourceFull:=mapped
  have baseView:baseRun=Prod.fst <$>sourceFull:=by
    simp only [baseRun,sourceFull,sourceCast,map_bind]
  have loggedView:loggedRun=Prod.fst <$>loggedFull:=by
    simp only [loggedRun,loggedFull,cast,map_bind]
  have bodyEq:loggedRun=lift baseRun:=
    loggedView.trans ((congrArg (fun work=>Prod.fst <$>work) fullEq).trans
      ((map Prod.fst sourceFull).symm.trans (congrArg (lift (Log:=Log)) baseView.symm)))
  change loggedRun.run=_
  rw [bodyEq]
  change StateT.lift _=_
  rw [RegistrationNativePlatformSdkFinishSourceProgram.agreement setup view model keys authenticated]

end BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.rust' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.rust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.agreement

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishObservedLift.map
