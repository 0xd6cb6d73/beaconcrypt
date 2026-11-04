-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedGeneric
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedGenericAgreement
open RegistrationNativeSecretWordInterface (Spec LocalSpec prepare liftLocal)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared prepare_recorded)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformLorSourceRetainedCore (lower Auxiliary)
variable {n : Nat} {I KemSK Private Reader E A B : Type} {base : OracleSpec I}
variable (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp)) (input : Message → Option Key)
variable (seen : Private → RegistrationNativeSecretWordFrontendTrace.State)
variable (recorded : ∀ message before result,result∈support ((implementation (.inl (.inl message))).run before) → Prepared message (seen result.2))
variable (echo : ∀ message before result,result∈support ((implementation (.inl (.inl message))).run before) →
  result.1=(input message).map (fun _=>message))
local notation "actual" => implementation
local notation "Trace" => RegistrationNativeSecretWordFrontendTrace.State

private theorem lower_run (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) A) (before : Auxiliary Private) :
    (lower implementation work).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$> (simulateQ implementation (work.run before.1)).run before.2 := rfl

private theorem lower_pure (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp)) (value : A) :
    lower implementation (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower,StateT.run,StateT.monad_pure_def,StateT.pure,simulateQ_pure,map_pure]

private theorem lower_bind (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) A)
    (next : A → StateT Environment (OracleComp (LocalSpec n KemSK)) B) :
    lower implementation (work >>= next) = (lower implementation work >>= fun value => lower implementation (next value)) := by
  apply StateT.ext
  intro before
  simp only [lower_run,StateT.run_bind,simulateQ_bind,map_bind,bind_map_left]

private theorem lower_map (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (observe : A → B) (work : StateT Environment (OracleComp (LocalSpec n KemSK)) A) :
    lower implementation (observe <$> work) = observe <$> lower implementation work := by
  apply StateT.ext
  intro before
  simp only [lower_run,StateT.run_map,simulateQ_map,Functor.map_map]

private theorem agreement_program (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (server : RegistrationNativeSecretWordMessage.ServerState) :
    (RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run server =
    (show StateT Environment (OracleComp (LocalSpec n KemSK)) (RustM (Option ServerReady) × RegistrationNativeSecretWordMessage.ServerState) from do
      let result ← RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated
      match result with
      | none => pure (.ok none,server)
      | some collected =>
          (fun reply => (reply,server)) <$> StateT.lift
            (simulateQ RegistrationNativeSecretWordInterface.prepare
              (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected))) := by
  apply StateT.ext
  intro env
  simp only [RegistrationNativeSecretWordServerCompiler.agreement,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left]
  apply bind_congr
  intro result
  cases result.1 <;> rfl

include recorded echo in
/-- Successful actual Server agreement retains the exact preparation performed by its own root client. -/
theorem agreement_prepared (setup : Setup base KemSK) (checks : Checks) (routed : Bool)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (server afterServer : RegistrationNativeSecretWordMessage.ServerState)
    (before after : Auxiliary (Private)) (ready : ServerReady)
    (supported : ((.ok (some ready),afterServer),after)∈support
      ((lower (actual ∘ₛ liftLocal routed) ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run server)).run before)) :
    Prepared ready.reference (seen after.2) := by
  rw [agreement_program,lower_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨⟨collected,middle⟩,called,supported⟩ := supported
  cases collected with
  | none =>
    simp only [lower_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
  | some collected =>
    rw [lower_map,StateT.run_map,support_map] at supported
    obtain ⟨result,possible,equal⟩ := supported
    have pairEqual : result = (.ok (some ready),after) := Prod.ext
      (congrArg (fun result => result.1.1) equal) (congrArg (fun result => result.2) equal)
    rw [pairEqual] at possible
    exact RegistrationNativePlatformLorSourcePreparedGeneric.lower_root_prepared implementation input seen recorded echo routed
      authenticated.binding collected middle after ready possible
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedGenericAgreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedGenericAgreement.agreement_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedGenericAgreement.agreement_prepared
