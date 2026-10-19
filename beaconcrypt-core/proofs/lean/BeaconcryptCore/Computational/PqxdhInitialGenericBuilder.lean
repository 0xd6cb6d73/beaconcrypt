import BeaconcryptCore.Computational.PqxdhInitialGenericPublication

/-!
The current Server registration gates and complete first-send builder carry an abstract private ratchet kernel. The actual native projection retains allocation, identity, reservation, consumed binding, application bytes, serialization and every peer field. This is the source continuation of a supplied initializer response; it neither samples before an admission gate nor exposes the selected chain to an ordinary observer.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialGenericBuilder
open PqxdhServerRegistrationPublication (AuxSpec Response TailSpec registrationWitness)
open PqxdhInitialGenericPublication
variable {Kernel Metadata PeerMetadata Consumed Result : Type}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def continueRust {α β : Type} (result : RustM α) (next : α → m (RustM β)) : m (RustM β) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

noncomputable def candidate (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    m (RustM (Option Response × State Kernel Metadata PeerMetadata Consumed)) := do
  let valid ← aux (.checkIdentity candidate.beacon_identity_public_key)
  if !valid then pure (ok (none, state)) else do
    let reserved ← aux .reservePeer
    if !reserved then pure (ok (none, state)) else
      continueRust initial fun kernel => do
        let plaintext := data.getD registrationWitness
        if plaintext.isEmpty then pure (ok (none, state))
        else if 8 + plaintext.length ≤ Usize.max then do
          let allocated ← aux (.reservePlaintext (8 + plaintext.length))
          if !allocated then pure (ok (none, state)) else
            continueRust (candidate.key_id_binding) fun binding =>
              ok <$> PqxdhInitialGenericPublication.afterInitialization calls aux candidate
                (absBytes binding.bytes ++ plaintext) kernel metadata state
        else pure (ok (none, state))

set_option backward.isDefEq.respectTransparency false in
/-- The original candidate admission and first-send program preserve the entire native state under the kernel map. The only local premise is the displayed full send equation, discharged by the retained-table specialization. -/
theorem candidate_native (interpret : Kernel → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls Kernel m) (backend : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (aux : QueryImpl AuxSpec m)
    (sendRealized : ∀ entry context,
      simulateQ ((backend ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (initial : RustM Kernel) (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    simulateQ (nativeImpl backend aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhInitialBuilderCut.candidate (interpret <$> initial) pending data metadata (native interpret state))) =
      Functor.map (Prod.map id (native interpret)) <$> candidate calls aux initial pending data metadata state := by
  simp only [PqxdhInitialBuilderCut.candidate, candidate, simulateQ_bind, simulateQ_spec_query,
    PqxdhServerRegistrationPublication.nativeAdapter, nativeImpl, map_bind]
  apply bind_congr
  intro valid
  cases valid
  · simp only [Bool.not_false, ite_true, simulateQ_pure, map_pure]
    rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
      PqxdhServerRegistrationPublication.nativeAdapter, nativeImpl, map_bind]
    apply bind_congr
    intro reserved
    cases reserved
    · simp only [Bool.not_false, ite_true, simulateQ_pure, map_pure]
      rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases initial with
      | fail error =>
          simp only [show (interpret <$> (fail error : RustM Kernel)) = fail error from rfl,
            PqxdhServerRegistrationPublication.continueRust, continueRust, simulateQ_pure, map_pure]
          rfl
      | div =>
          simp only [show (interpret <$> (div : RustM Kernel)) = div from rfl,
            PqxdhServerRegistrationPublication.continueRust, continueRust, simulateQ_pure, map_pure]
          rfl
      | ok kernel =>
          simp only [RawCtxMaterialInterpretation.rust_map_ok, PqxdhServerRegistrationPublication.continueRust, continueRust]
          by_cases empty : (data.getD registrationWitness).isEmpty = true
          · simp only [empty, ite_true, simulateQ_pure, map_pure, RawCtxMaterialInterpretation.rust_map_ok,
              Prod.map_apply, id_eq]
          · simp only [empty, Bool.false_eq_true, ite_false]
            by_cases fits : 8 + (data.getD registrationWitness).length ≤ Usize.max
            · simp only [fits, ite_true, simulateQ_bind, simulateQ_spec_query,
                PqxdhServerRegistrationPublication.nativeAdapter, nativeImpl, map_bind]
              apply bind_congr
              intro allocated
              cases allocated
              · simp only [Bool.not_false, ite_true, simulateQ_pure, map_pure, RawCtxMaterialInterpretation.rust_map_ok,
                  Prod.map_apply, id_eq]
              · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases binding : pending.key_id_binding with
                | fail error => simp only [simulateQ_pure, map_pure]; rfl
                | div => simp only [simulateQ_pure, map_pure]; rfl
                | ok binding =>
                    simp only [simulateQ_map, after_native interpret calls backend aux sendRealized, Functor.map_map]
                    rfl
            · simp only [fits, ite_false, simulateQ_pure, map_pure, RawCtxMaterialInterpretation.rust_map_ok,
                Prod.map_apply, id_eq]

noncomputable def usedBuild
    (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (initial : RustM Kernel)
    (pending : PqxdhRegistrationInputs.UsedInput)
    (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    m (RustM (Option Response × State Kernel Metadata PeerMetadata Consumed)) :=
  continueRust (pqxdh.server_next_key_id state.control) fun next =>
    match next with
    | .Err _ => pure (ok (none, state))
    | .Ok next =>
        let availability := if (state.server.peers next).isSome then
          pqxdh.KeyIdAvailability.Occupied else .Available
        continueRust (PqxdhRegistrationInputs.prepare state.control pending
          ⟨state.server.identity, state.identityKeyId⟩ availability) fun prepared =>
          match prepared with
          | .Err _ => pure (ok (none, state))
          | .Ok candidate => PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state


/-- Native current allocation and occupied-peer checks use the same generic fields before the unchanged candidate tail. -/
theorem used_native (interpret : Kernel → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls Kernel m) (backend : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (aux : QueryImpl AuxSpec m)
    (sendRealized : ∀ entry context,
      simulateQ ((backend ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (initial : RustM Kernel) (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    simulateQ (nativeImpl backend aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhInitialBuilderCut.usedBuild (interpret <$> initial) pending data metadata (native interpret state))) =
      Functor.map (Prod.map id (native interpret)) <$> usedBuild calls aux initial pending data metadata state := by
  unfold PqxdhInitialBuilderCut.usedBuild usedBuild
  change simulateQ (nativeImpl backend aux) (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
    (PqxdhServerRegistrationPublication.continueRust (pqxdh.server_next_key_id state.control) _)) = _
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => simp only [PqxdhServerRegistrationPublication.continueRust, continueRust, simulateQ_pure, map_pure]; rfl
  | div => simp only [PqxdhServerRegistrationPublication.continueRust, continueRust, simulateQ_pure, map_pure]; rfl
  | ok result =>
      cases result with
      | Err error => simp only [PqxdhServerRegistrationPublication.continueRust, continueRust, simulateQ_pure, map_pure]; rfl
      | Ok key =>
          simp only [PqxdhServerRegistrationPublication.continueRust, continueRust]
          have preparation :
              PqxdhRegistrationInputs.prepare (native interpret state).control pending
                ⟨(native interpret state).server.identity, (native interpret state).identityKeyId⟩
                (if ((native interpret state).server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) =
              PqxdhRegistrationInputs.prepare state.control pending ⟨state.server.identity, state.identityKeyId⟩
                (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) := by
            simp only [native, RawCtxGenericRoleStorage.nativeServer, Option.isSome_map]
          rw [preparation]
          cases prepared : PqxdhRegistrationInputs.prepare state.control pending ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => simp only [simulateQ_pure, map_pure]; rfl
          | div => simp only [simulateQ_pure, map_pure]; rfl
          | ok value => cases value with
            | Err error => simp only [simulateQ_pure, map_pure]; rfl
            | Ok value => exact candidate_native interpret calls backend aux sendRealized initial value data metadata state

noncomputable def readyBuild (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m) (initial : RustM Kernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :=
  usedBuild calls aux initial (PqxdhAcceptedRegistration.usedReady source.crypto binding ready) ready.application metadata state

/-- Every actual Ready field, current allocation and binding check precedes the same complete generic first-send tail under the native kernel map. -/
theorem ready_native (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (interpret : Kernel → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls Kernel m) (backend : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (aux : QueryImpl AuxSpec m)
    (sendRealized : ∀ entry context,
      simulateQ ((backend ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (initial : RustM Kernel) (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    simulateQ (nativeImpl backend aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhInitialBuilderCut.readyBuild source (interpret <$> initial) binding ready metadata (native interpret state))) =
      Functor.map (Prod.map id (native interpret)) <$> readyBuild source calls aux initial binding ready metadata state :=
  used_native interpret calls backend aux sendRealized initial _ ready.application metadata state

omit [LawfulMonad m] in
/-- Once the typed initializer is supplied, this executable generic builder retains no Ready root dependency. -/
theorem ready_root_unused (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m) (initial : RustM Kernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    readyBuild source calls aux initial binding {ready with root := root} metadata state =
      readyBuild source calls aux initial binding ready metadata state := rfl

/-- The retained-table source interpretation discharges the whole Ready builder, including all original gates and first ciphertext, without any caller-supplied callback-compatibility premise. -/
theorem selected_ready {A : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (entry : RawCtxSelectedParentEntry.Entry) (target : PqxdhSecretInputKdf.RootOutput)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (initial : RustM RawCtxSelectedChain.Kernel) (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : PeerMetadata) (state : State RawCtxSelectedChain.Kernel Metadata PeerMetadata Consumed) :
    simulateQ (nativeImpl (RawCtxSelectedParentNativeBackend.backend source writer prior entry target) aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhInitialBuilderCut.readyBuild source
          (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initial) binding ready metadata
          (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state))) =
      Functor.map (Prod.map id (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))) <$>
        readyBuild source (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)) aux initial binding ready metadata state :=
  ready_native source _ _ _ aux (selected_send source writer prior entry target) initial binding ready metadata state

end BeaconcryptCore.Computational.PqxdhInitialGenericBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.candidate_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.candidate_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.used_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.used_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.ready_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.ready_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.ready_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.ready_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.selected_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBuilder.selected_ready
