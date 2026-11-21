-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementRoot
import BeaconcryptCore.Computational.RegistrationRelatedRoot

/-! The exact final native agreement phase is the related-root consumer at its reached authenticated input. Instrumenting root calls records the existing family table and HMAC history, while projection retains the complete original shared primitive state. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 2048

namespace BeaconcryptCore.Computational.RegistrationAgreementFinish

open RegistrationAgreementExecutor
open PqxdhServerRootPreparation (Inputs)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhSecretInputKdf (HmacSha512)
open PqxdhServerRelatedRootConsumer (State)

def finishSource (control : pqxdh.ServerState) (binding : session.RegistrationBinding)
    (input : Inputs registration.InitPacket Unit Word32) : OracleComp Spec (RustM agreement.AgreementEffect) :=
  continueWith (PqxdhServerRelatedRootInput.accept control binding.server_pin.binding input) fun result =>
    match result with
    | .Err _ => pure (.ok (.Rejected .None))
    | .Ok (_, pending) => drive 1 (.RootKdf ⟨.Server pending binding⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The actual fourth-DH admission uses the original authenticated credential and full populated binding. -/
theorem finish_source (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit)
    (input : Inputs registration.InitPacket Unit Word32)
    (credential : PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys = authenticated.registration) :
    RegistrationAgreementRoot.finish control authenticated input = finishSource control authenticated.binding input := by
  obtain ⟨accepted, acceptedRun⟩ := BeaconcryptCore.PanicFreedom.server_accept_ok control authenticated.registration
    .Fresh authenticated.binding.server_pin.binding
    ⟨input.ephemeral.publicKey, input.ciphertext⟩
    ⟨input.first, input.second, input.third, input.fourth, input.kem⟩
  cases accepted with
  | Err error =>
      simp only [RegistrationAgreementRoot.finish, RegistrationAgreementRoot.state,
        agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok,
        session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding,
        finishSource, PqxdhServerRelatedRootInput.accept, PqxdhServerRelatedRootInput.secrets,
        credential, acceptedRun, continueWith, drive, step, pure_bind]
  | Ok pair =>
      rcases pair with ⟨next, pending⟩
      simp only [RegistrationAgreementRoot.finish, RegistrationAgreementRoot.state,
        agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok,
        session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding,
        finishSource, PqxdhServerRelatedRootInput.accept, PqxdhServerRelatedRootInput.secrets,
        credential, acceptedRun, continueWith]
      dsimp!

/-- The optional native root reply and all its original continuation checks are preserved. -/
theorem root_step (pending : agreement.RootKdfPending) (request : agreement.RootKdfRequest)
    (requested : pending.request = .ok request) :
    drive 1 (.RootKdf pending) = (do
      let reply ← (Spec.query (.root request) : OracleComp Spec _)
      pure (pending.resume reply)) := by
  simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
  congr 1
  funext reply
  cases pending.resume reply <;> rfl

def rootReceipt {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Inputs registration.InitPacket Unit Word32) (request : agreement.RootKdfRequest) :
    StateT (State Auxiliary) ProbComp (core.option.Option Word32) := fun before =>
  pure (.Some (RegistrationAgreementShared.rootResponse source.crypto request),
    (PqxdhJointDhExtractRoot.rootState hmac (PqxdhServerRelatedRootConsumer.nativeMessage input)
      (absBytes request.input) before.1, before.2))

/-- Extra root-table bookkeeping cannot modify any native primitive effect or CTX cache. -/
def instrument {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (input : Inputs registration.InitPacket Unit Word32) :
    QueryImpl Spec (StateT (State (RawCtxSharedPrimitive.SharedState Auxiliary)) ProbComp)
  | .root request => rootReceipt source hmac input request
  | request => fun before =>
      (fun result => (result.1, (before.1, result.2))) <$>
        (RegistrationAgreementShared.implementation source primitive request).run before.2

attribute [local irreducible] RegistrationAgreementShared.rootResponse PqxdhJointDhExtractRoot.rootState

private theorem project_reinsert {Value Family Auxiliary : Type} (family : Family)
    (work : ProbComp (Value × Auxiliary)) :
    Prod.map id Prod.snd <$> ((fun result => (result.1, (family, result.2))) <$> work) = work := by
  rw [Functor.map_map]
  change id <$> work = work
  exact id_map work

theorem instrument_query {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (input : Inputs registration.InitPacket Unit Word32) (request : Request)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$>
        (instrument source hmac primitive input request).run before =
      (RegistrationAgreementShared.implementation source primitive request).run before.2 := by
  cases request with
  | root request =>
      rw [RegistrationAgreementShared.root_exact]
      rfl
  | convertPublic key =>
      exact project_reinsert before.1
        ((RegistrationAgreementShared.implementation source primitive (.convertPublic key)).run before.2)
  | convertSecret role =>
      exact project_reinsert before.1
        ((RegistrationAgreementShared.implementation source primitive (.convertSecret role)).run before.2)
  | generate role =>
      exact project_reinsert before.1
        ((RegistrationAgreementShared.implementation source primitive (.generate role)).run before.2)
  | encapsulate key =>
      exact project_reinsert before.1
        ((RegistrationAgreementShared.implementation source primitive (.encapsulate key)).run before.2)
  | decapsulate ciphertext =>
      exact project_reinsert before.1
        ((RegistrationAgreementShared.implementation source primitive (.decapsulate ciphertext)).run before.2)
  | dh request =>
      exact project_reinsert before.1
        ((RegistrationAgreementShared.implementation source primitive (.dh request)).run before.2)

theorem instrument_program {Auxiliary Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (input : Inputs registration.InitPacket Unit Word32) (work : OracleComp Spec Result)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$>
        (simulateQ (instrument source hmac primitive input) work).run before =
      (simulateQ (RegistrationAgreementShared.implementation source primitive) work).run before.2 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (instrument_query source hmac primitive input) work before

def quiet {Auxiliary : Type} : QueryImpl PqxdhServerRelatedRootConsumer.AuxSpec (StateT Auxiliary ProbComp) :=
  fun _ => pure ()

private theorem quiet_lift {Auxiliary : Type} (query : PqxdhServerRelatedRootConsumer.Auxiliary) :
    PqxdhServerRelatedRootConsumer.auxImpl (quiet : QueryImpl _ (StateT Auxiliary ProbComp)) query = pure () := rfl

theorem response_root (source : FixedHkdfSha512NoSaltSource) (original : pqxdh.PendingServerRegistration) :
    RegistrationAgreementShared.rootResponse source.crypto ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ =
      PqxdhRootTableInitialization.rootArray
        (PqxdhJointDhExtractRoot.nativeRoot source (absBytes original.root_key_input.bytes)) := by
  apply Subtype.ext
  simp only [RegistrationAgreementShared.rootResponse, PqxdhRootTableInitialization.rootArray,
    PqxdhJointDhExtractRoot.nativeRoot, Pqxdh.rootSecret, absBytes_PQXDH_INFO]
  rfl

theorem root_native {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (input : Inputs registration.InitPacket Unit Word32) (binding : session.RegistrationBinding)
    (original : pqxdh.PendingServerRegistration)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    (simulateQ (instrument source hmac primitive input)
      (drive 1 (.RootKdf ⟨.Server original binding⟩))).run before =
      pure (.ok (.ServerComplete ⟨PqxdhServerClearedRoot.cleared original, binding,
        ⟨PqxdhRootTableInitialization.rootArray
          (PqxdhJointDhExtractRoot.nativeRoot source (absBytes original.root_key_input.bytes))⟩⟩),
        (PqxdhJointDhExtractRoot.rootState hmac (PqxdhServerRelatedRootConsumer.nativeMessage input)
          (absBytes original.root_key_input.bytes) before.1, before.2)) := by
  have requested : (⟨.Server original binding⟩ : agreement.RootKdfPending).request =
      .ok ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
    simp only [agreement.RootKdfPending.request, pqxdh.PendingServerRegistration.impl.root_key_input,
      pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
  rw [root_step _ _ requested]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  change (pure
    ((⟨.Server original binding⟩ : agreement.RootKdfPending).resume
      (.Some (RegistrationAgreementShared.rootResponse source.crypto
        ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩)),
      (PqxdhJointDhExtractRoot.rootState hmac (PqxdhServerRelatedRootConsumer.nativeMessage input)
        (absBytes original.root_key_input.bytes) before.1, before.2)) :
      ProbComp (RustM agreement.AgreementEffect × State (RawCtxSharedPrimitive.SharedState Auxiliary))) = _
  rw [BeaconcryptCore.Refinement.KeyAgreement.root_success_refines, response_root]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The final native callback, root-input clearing and complete completion capability agree with the source consumer, including rejection and its exact family log. -/
theorem finish_native {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (control : pqxdh.ServerState) (binding : session.RegistrationBinding)
    (input : Inputs registration.InitPacket Unit Word32) :
    simulateQ (instrument source hmac primitive input) (finishSource control binding input) =
      RegistrationRelatedRoot.source source hmac quiet control binding input := by
  obtain ⟨accepted, acceptedRun⟩ := BeaconcryptCore.PanicFreedom.server_accept_ok control
    (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys)
    .Fresh binding.server_pin.binding ⟨input.ephemeral.publicKey, input.ciphertext⟩
    (PqxdhServerRelatedRootInput.secrets input)
  have sourceAccept : PqxdhServerRelatedRootInput.accept control binding.server_pin.binding input = .ok accepted :=
    acceptedRun
  funext before
  change (simulateQ (instrument source hmac primitive input) (finishSource control binding input)).run before =
    (RegistrationRelatedRoot.source source hmac quiet control binding input).run before
  cases accepted with
  | Err error =>
      simp only [finishSource, sourceAccept, continueWith, simulateQ_pure, StateT.run_pure,
        RegistrationRelatedRoot.source, PqxdhServerRelatedRootConsumer.source,
        quiet_lift, map_pure, pure_bind, RegistrationRelatedRoot.completed]
  | Ok pair =>
      rcases pair with ⟨next, original⟩
      simp only [finishSource, sourceAccept, continueWith]
      rw [root_native]
      simp only [StateT.run_map, StateT.run_bind, StateT.run_pure, pure_bind,
        RegistrationRelatedRoot.source, PqxdhServerRelatedRootConsumer.source,
        sourceAccept, quiet_lift, RegistrationRelatedRoot.completed]
      rfl

end BeaconcryptCore.Computational.RegistrationAgreementFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementFinish.finish_source

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementFinish.root_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementFinish.root_step

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementFinish.instrument_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementFinish.instrument_query

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementFinish.instrument_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementFinish.instrument_program

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementFinish.response_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementFinish.response_root

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementFinish.root_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementFinish.root_native

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementFinish.finish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementFinish.finish_native
