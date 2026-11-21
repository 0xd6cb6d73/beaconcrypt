-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl
/-! A genuinely retained Server Ready carries the exact descriptor requested at its own earlier preparation in the same actual source trace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedServer
open RegistrationNativeSecretWordInterface (Spec LocalSpec prepare liftLocal)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared prepare_recorded)
variable {n : Nat} {KemSK Private Reader E : Type}
variable (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp)) (input : Message → Option Key)
variable (echo : ∀ message before result,result∈support ((implementation (.inl (.inl message))).run before) →
  result.1=(input message).map (fun _=>message))
local notation "actual" => RegistrationNativePlatformLorStatefulSupport.trace implementation
local notation "Trace" => RegistrationNativeSecretWordFrontendTrace.State

include echo in
/-- The actual successful Server root reply names its own just-recorded prepare request, using only the individual source echo contract. -/
theorem root_prepared (routed : Bool) (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input Reader E PqxdhJointIdentity.PeerEncoding)
    (before after : Trace × Private) (ready : ServerReady)
    (supported : (.ok (some ready),after)∈support ((simulateQ actual (simulateQ (liftLocal routed)
      (simulateQ (prepare (n := n) (KemSK := KemSK)) (RegistrationNativeSecretWordServerRoot.client binding collected)))).run before)) :
    Prepared ready.reference after.1 := by
  classical
  simp only [RegistrationNativeSecretWordServerRoot.client] at supported
  split at supported
  · simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
  · simp only [bind_pure_comp,simulateQ_map,simulateQ_spec_query,prepare,liftLocal,StateT.run_map,support_map] at supported
    obtain ⟨queried,called,equal⟩ := supported
    have prepared := prepare_recorded implementation (RegistrationNativeSecretWordServerRoot.message collected) before queried called
    have original := RegistrationNativePlatformLorSourceKemTrace.query_support implementation (.inl (.inl (RegistrationNativeSecretWordServerRoot.message collected))) before queried called
    have value := congrArg Prod.fst equal
    dsimp only at value
    rw [echo (RegistrationNativeSecretWordServerRoot.message collected) before.2 (queried.1,queried.2.2) original] at value
    cases realized : input (RegistrationNativeSecretWordServerRoot.message collected) with
    | none=>simp [realized] at value
    | some key=>
      simp only [realized,Option.map_some,RustM.ok.injEq,Option.some.injEq] at value
      have reference : ready.reference=RegistrationNativeSecretWordServerRoot.message collected :=
        (congrArg ServerReady.reference value).symm
      have afterEq := congrArg Prod.snd equal
      dsimp only at afterEq
      rw [reference,←afterEq]
      exact prepared
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before=(fun value=>(value,before)) <$>work := bind_pure_comp _ _
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$>work) before=Prod.map change id <$>work before := StateT.run_map _ _ _

private theorem lower_root_source (routed : Bool) (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input Reader E PqxdhJointIdentity.PeerEncoding)
    (before : RegistrationServerReferenceCompiler.Environment × (Trace × Private)) :
    (RegistrationNativePlatformLorSourceRetainedCore.lower (actual ∘ₛ liftLocal routed)
      (StateT.lift (simulateQ (prepare (n := n) (KemSK := KemSK)) (RegistrationNativeSecretWordServerRoot.client binding collected)))).run before=
      (fun result=>(result.1,(before.1,result.2))) <$>
        (simulateQ actual (simulateQ (liftLocal routed)
          (simulateQ (prepare (n := n) (KemSK := KemSK)) (RegistrationNativeSecretWordServerRoot.client binding collected)))).run before.2 := by
  simp only [RegistrationNativePlatformLorSourceRetainedCore.lower,StateT.run,lift_apply,simulateQ_map,map_apply,
    Functor.map_map,QueryImpl.simulateQ_compose]
  rfl

include echo in
/-- The same root preparation remains attached after its actual local environment interpretation. -/
theorem lower_root_prepared (routed : Bool) (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input Reader E PqxdhJointIdentity.PeerEncoding)
    (before after : RegistrationServerReferenceCompiler.Environment × (Trace × Private)) (ready : ServerReady)
    (supported : (.ok (some ready),after)∈support ((RegistrationNativePlatformLorSourceRetainedCore.lower (actual ∘ₛ liftLocal routed)
      (StateT.lift (simulateQ (prepare (n := n) (KemSK := KemSK)) (RegistrationNativeSecretWordServerRoot.client binding collected)))).run before)) :
    Prepared ready.reference after.2.1 := by
  rw [lower_root_source,support_map] at supported
  obtain ⟨result,called,equal⟩ := supported
  change (result.1,(before.1,result.2))=(.ok (some ready),after) at equal
  have replyEq : result.1=.ok (some ready) := congrArg Prod.fst equal
  have stateEq : result.2=after.2 := congrArg (fun value=>value.2.2) equal
  have identity : result=(.ok (some ready),after.2) := Prod.ext replyEq stateEq
  rw [identity] at called
  exact root_prepared implementation input echo routed binding collected before.2 after.2 ready called

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedServer.root_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedServer.root_prepared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedServer.lower_root_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedServer.lower_root_prepared
