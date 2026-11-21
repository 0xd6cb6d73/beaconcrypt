-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconFinish
/-! The actual scalar owner finish retains its complete chronological trace and private state at the same successful preparation, before any later optional completion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordFrontendTrace (Event)
open RegistrationNativeSecretWordGenericLower (Auxiliary lower lower_run)
open RegistrationNativePlatformRecordPartnerFinishScalar (scalarLocal)
open RegistrationNativePlatformSecretWordInstallBeaconComplete (compile)
open RegistrationNativePlatformSecretWordFinish (finish afterPrepared phase)
variable {n : Nat} {I KemSK Private Value : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem scalar_compose (setup : Setup base KemSK)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    scalarLocal setup implementation scalar=implementation ∘ₛ RegistrationNativeSecretWordAtomOwnerSource.routing setup scalar := by
  cases scalar with
  | none=>rfl
  | some scalar=>
      funext query
      simp only [scalarLocal,RegistrationNativeSecretWordAtomOwnerSource.routing,QueryImpl.compose,QueryImpl.simulateQ_compose]

/-- The literal optional-scalar local interpreter factors through the same original full Word query tree, without changing its current environment or private state. -/
theorem execute (setup : Setup base KemSK)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : StateT Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (before : Auxiliary Private) :
    (lower (scalarLocal setup implementation scalar) work).run before=
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ implementation (compile setup scalar (work.run before.1))).run before.2 := by
  rw [lower_run,scalar_compose,QueryImpl.simulateQ_compose]
  rfl

/-- A current source result retains its exact actual trace of the same optional-scalar finish tree. -/
theorem trace_support (setup : Setup base KemSK)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : StateT Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (before : Auxiliary (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (result : Value × Auxiliary (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (supported : result∈support ((lower (scalarLocal setup (RegistrationNativePlatformLorStatefulSupport.trace implementation) scalar) work).run before)) :
    ((result.1,result.2.1),result.2.2.1)∈support
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler (compile setup scalar (work.run before.1))).run before.2.1) := by
  rw [execute,support_map] at supported
  obtain ⟨inner,called,same⟩ := supported
  cases same
  exact RegistrationNativePlatformLorStatefulSupport.trace_support implementation _ before.2 inner called

private noncomputable def close {Value : Type} (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformSecretWordFinish.M n KemSK RegistrationServerRoleBackend.State source Value)
    (owner : SelectedOwner source) (env : Environment) :=
  compile setup scalar ((work.run owner).run env)

private theorem finish_close (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (env : Environment) :
    close (n := n) setup ownScalar (finish setup wire source packet) owner env =
      match owner.phase with
      | .initSent pending _ => match pending.aborted_state with
        | .fail error => pure ((.fail error, owner), env)
        | .div => pure ((.div, owner), env)
        | .ok _ => do
            let reached ← close setup ownScalar (RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet) owner env
            close setup ownScalar (afterPrepared setup.source wire.frameWrite owner reached.1.1) reached.1.2 reached.2
      | _ => pure ((.ok none, owner), env) := by
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [close, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile, finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, StateT.run_pure, simulateQ_pure]
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [close, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile, finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_pure, simulateQ_pure]
      | ok aborted =>
          simp only [close, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile, finish, RegistrationNativeSecretWordBeaconCompiler.finishPreparation,
            StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_modify, StateT.run_set,
            StateT.run_lift, bind_pure_comp, bind_map_left, simulateQ_bind, bind_assoc]
          apply bind_congr
          intro accepted
          cases accepted with
          | fail error | div => simp only [StateT.run_pure, simulateQ_pure, pure_bind, afterPrepared]
          | ok response => cases response with
            | Err _ => simp only [StateT.run_pure, simulateQ_pure, pure_bind, afterPrepared]
            | Ok authenticated =>
                simp only [phase, StateT.run_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, bind_map_left, simulateQ_bind, simulateQ_map]


private theorem no_added {A : Type} (before after added : List A)
    (suffix : after=before++added) (same : after=before) : added=[] := by
  exact List.append_cancel_left (suffix.symm.trans (same.trans (List.append_nil before).symm))

variable (setup : Setup base KemSK)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
local notation "actual" => RegistrationNativePlatformLorStatefulSupport.trace implementation
open RegistrationNativeSecretWordInstallOrdinals (messages)

include contract in
/-- A newly successful atom installation in the literal source finish belongs to the selected private owner, even if its public enclosing reply later fails. -/
theorem local_finish (wire : RegistrationNativeWire.Wire) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner source) (packet : Option registration.ResponsePacket)
    (before : Auxiliary (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × Auxiliary (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (supported : result∈support ((lower (scalarLocal setup actual scalar)
      ((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner)).run before))
    (added : List Message) (suffix : messages .beacon result.2.2.1.events=messages .beacon before.2.1.events++added)
    (message : Message) (member : message∈added) (atom : message.kem=Word.atom) : owner.kemHandle=selected := by
  rw [execute,support_map] at supported
  obtain ⟨⟨⟨⟨reply,afterOwner⟩,afterEnv⟩,afterPrivate⟩,called,same⟩ := supported
  cases same
  change messages .beacon afterPrivate.1.events=messages .beacon before.2.1.events++added at suffix
  change (((reply,afterOwner),afterEnv),afterPrivate)∈support
    ((simulateQ actual (close setup scalar (finish setup wire source packet) owner before.1)).run before.2) at called
  rw [finish_close] at called
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [ownerPhase,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at called
      cases called
      have empty := no_added _ _ added suffix rfl
      rw [empty] at member
      cases member
  | initSent pending oneTime=>
      simp only [ownerPhase] at called
      cases moved : pending.aborted_state with
      | fail error | div=>
          simp only [moved,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at called
          cases called
          have empty := no_added _ _ added suffix rfl
          rw [empty] at member
          cases member
      | ok aborted=>
          simp only [moved,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at called
          obtain ⟨prepared,possible,continued⟩ := called
          have preparedFree := RegistrationNativePlatformLorStatefulSupport.trace_support implementation _ before.2 prepared possible
          have noInstall := RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free (n := n) .beacon setup source packet owner before.1
          have bound := RegistrationNativeSecretWordAtomOwnerSource.routing_bound setup .beacon scalar _ 0 noInstall
          have prefixEq := RegistrationNativeSecretWordInstallTrace.free .beacon _ bound before.2.1 (prepared.1,prepared.2.1) preparedFree
          have continuedFree := RegistrationNativePlatformLorStatefulSupport.trace_support implementation _ prepared.2
            (((reply,afterOwner),afterEnv),afterPrivate) continued
          cases outcome : prepared.1.1.1 with
          | fail error=>
              have ended := RegistrationNativePlatformSecretWordInstallBeaconComplete.abort setup scalar owner prepared.1.1.2 prepared.1.2
                (.fail error) prepared.2.1 (((reply,afterOwner),afterEnv),afterPrivate.1)
                (by simpa only [outcome,afterPrepared,close] using continuedFree)
              have sameMessages : messages .beacon afterPrivate.1.events=messages .beacon before.2.1.events := by
                have traceEq : afterPrivate.1=prepared.2.1 := ended.2
                exact (congrArg (fun trace=>messages .beacon trace.events) traceEq).trans prefixEq
              have empty := no_added _ _ added suffix sameMessages
              rw [empty] at member
              cases member
          | div=>
              have ended := RegistrationNativePlatformSecretWordInstallBeaconComplete.abort setup scalar owner prepared.1.1.2 prepared.1.2
                .div prepared.2.1 (((reply,afterOwner),afterEnv),afterPrivate.1)
                (by simpa only [outcome,afterPrepared,close] using continuedFree)
              have sameMessages : messages .beacon afterPrivate.1.events=messages .beacon before.2.1.events := by
                have traceEq : afterPrivate.1=prepared.2.1 := ended.2
                exact (congrArg (fun trace=>messages .beacon trace.events) traceEq).trans prefixEq
              have empty := no_added _ _ added suffix sameMessages
              rw [empty] at member
              cases member
          | ok optional=>cases optional with
            | none=>
                have ended := RegistrationNativePlatformSecretWordInstallBeaconComplete.abort setup scalar owner prepared.1.1.2 prepared.1.2
                  (.ok none) prepared.2.1 (((reply,afterOwner),afterEnv),afterPrivate.1)
                  (by simpa only [outcome,afterPrepared,close] using continuedFree)
                have sameMessages : messages .beacon afterPrivate.1.events=messages .beacon before.2.1.events := by
                  have traceEq : afterPrivate.1=prepared.2.1 := ended.2
                  exact (congrArg (fun trace=>messages .beacon trace.events) traceEq).trans prefixEq
                have empty := no_added _ _ added suffix sameMessages
                rw [empty] at member
                cases member
            | some ready=>
                have completed := RegistrationNativePlatformSecretWordInstallBeaconComplete.complete_all .beacon setup scalar setup.source wire.frameWrite
                  owner prepared.1.1.2 ready prepared.1.2 prepared.2.1 (((reply,afterOwner),afterEnv),afterPrivate.1)
                  (by simpa only [outcome,afterPrepared,close] using continuedFree)
                rw [prefixEq] at completed
                have addedEq := List.append_cancel_left (suffix.symm.trans completed)
                have sameMessage : message=ready.reference := by
                  rw [addedEq] at member
                  split at member
                  · exact List.mem_singleton.mp member
                  · cases member
                have readyAtom : ready.reference.kem=Word.atom := by rw [←sameMessage]; exact atom
                have preparedAt : ((.ok (some ready),prepared.1.1.2),(prepared.1.2,prepared.2))∈support
                    ((lower (scalarLocal setup actual scalar)
                      ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner)).run before) := by
                  rw [execute,support_map]
                  exact ⟨prepared,possible,Prod.ext (Prod.ext outcome rfl) rfl⟩
                exact RegistrationNativePlatformRecordPartnerFinishScalar.prepared_handle setup actual selected pairs publicKey challenge
                  (fun state=>kem state.2) input (RegistrationNativePlatformLorSourceKemTrace.contract implementation kem input _ contract)
                  scalar packet owner prepared.1.1.2 ready before (prepared.1.2,prepared.2) readyAtom preparedAt

variable {Platform : Type}
local notation "Front" => RegistrationNativePlatformSecretWordOrdinary.State source Platform
local notation "Current" => Front × (RegistrationNativeSecretWordFrontendTrace.State × Private)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before=Prod.map change id <$> work before := StateT.run_map change work before

private theorem present (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : Current) (owner : RegistrationNativePublicOwners.Owner source) (found : before.1.1.beacons[index]?=some owner) :
    (fun reached=>(reached.1.1,(reached.1.2,reached.2))) <$>
      (simulateQ actual ((RegistrationNativePlatformSecretWordFrontend.finish setup wire source index packet).run before.1)).run before.2=
    (fun reached=>(reached.1.1,(({before.1.1 with beacons:=before.1.1.beacons.set index {owner with view:=reached.1.2},environment:=reached.2.1},before.1.2),reached.2.2))) <$>
      (lower (scalarLocal setup actual owner.scalar)
        ((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner.view)).run (before.1.1.environment,before.2) := by
  rw [execute]
  simp only [RegistrationNativePlatformSecretWordFrontend.finish,StateT.run,found,simulateQ_map,map_apply,Functor.map_map]
  cases owner.scalar <;>
    simp only [compile,RegistrationNativeSecretWordAtomOwnerSource.routing,QueryImpl.simulateQ_compose]
  all_goals rfl

include contract in
/-- A newly successful atom install from the literal current frontend finish belongs to the original selected owner index, derived from its current row alignment. -/
theorem frontend (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : Current) (result : RustM (Option Pqxdh.Bytes) × Current)
    (supported : result∈support ((fun reached=>(reached.1.1,(reached.1.2,reached.2))) <$>
      (simulateQ actual ((RegistrationNativePlatformSecretWordFrontend.finish setup wire source index packet).run before.1)).run before.2))
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned before.1.1.beacons (kem before.2.2).1.keys)
    (added : List Message) (suffix : messages .beacon result.2.2.1.events=messages .beacon before.2.1.events++added)
    (message : Message) (member : message∈added) (atom : message.kem=Word.atom) : index=selected := by
  cases found : before.1.1.beacons[index]? with
  | none=>
      simp only [RegistrationNativePlatformSecretWordFrontend.finish,StateT.run,found,simulateQ_pure] at supported
      cases supported
      have empty := no_added _ _ added suffix rfl
      rw [empty] at member
      cases member
  | some owner=>
      rw [present setup implementation wire index packet before owner found,support_map] at supported
      obtain ⟨reached,called,same⟩ := supported
      have privateEq : reached.2.2=result.2.2 := congrArg (fun output=>output.2.2) same
      have localSuffix : messages .beacon reached.2.2.1.events=messages .beacon before.2.1.events++added := by rw [privateEq]; exact suffix
      have handle := local_finish setup implementation selected pairs publicKey challenge kem input contract wire owner.scalar owner.view packet
        (before.1.1.environment,before.2) reached called added localSuffix message member atom
      exact RegistrationNativePlatformRecordPartnerOwner.owner_index selected before.1.1.beacons (kem before.2.2).1.keys index owner aligned found handle

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish.execute

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish.trace_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish.trace_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish.local_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish.local_finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinish.frontend
