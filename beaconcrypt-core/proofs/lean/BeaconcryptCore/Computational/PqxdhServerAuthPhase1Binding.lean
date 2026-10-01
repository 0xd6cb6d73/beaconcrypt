import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Projection

/-! The same actual pending and builder receipt retains the pinned Server binding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding
open PqxdhServerAuthExperiment PqxdhServerAuthPhase1Projection PqxdhServerAuthEntryFactor
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Successful original commit preparation requires both fields of the supplied pending binding to equal the current Server binding. -/
theorem prepare_binding (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (current : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (prepared : pqxdh.server_prepare_commit state pending current availability = ok (.Ok candidate)) :
    pending.server_binding = current := by
  have identifier : pending.server_binding.identity_key_id = current.identity_key_id := by
    by_contra different
    have rejected := BeaconcryptCore.Refinement.PqxdhSurface.server_binding_mismatch_is_rejected
      state pending current availability (Or.inl different)
    rw [prepared] at rejected
    cases RustM.ok.inj rejected
  have publicKey : pending.server_binding.identity_public_key = current.identity_public_key := by
    by_contra different
    have rejected := BeaconcryptCore.Refinement.PqxdhSurface.server_binding_mismatch_is_rejected
      state pending current availability (Or.inr different)
    rw [prepared] at rejected
    cases RustM.ok.inj rejected
  cases left : pending.server_binding
  cases right : current
  simpa only [left, right, pqxdh.ServerBinding.mk.injEq] using And.intro publicKey identifier

/-- The same successful selected builder receipt carries the actual pinned Server identity and identifier into both its source state and sealed context. No equality of roots or candidate encodings is used. -/
theorem record_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PqxdhJointGapDh.PublicChallenge)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (verified : PqxdhServerRootPreparation.Verified Reader)
    (projected : Projected setup publicValue token verified)
    (payload : Option Pqxdh.Bytes) (state : ServerState)
    (response : PqxdhServerRegistrationPublication.Response) (entry : CtxRomAuth.CtxSuccessfulSeal)
    (receipt : PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload state response entry) :
    state.server.identity = PqxdhRootTableInitialization.rootArray publicValue.identity.ed25519 ∧
    state.identityKeyId = setup.serverKeyId ∧
    entry.input.context.ad.sid = setup.serverKeyId.val ∧
    entry.input.context.ad.bytes = Pqxdh.assocData publicValue.identity.ed25519.toList verified.identity.toList := by
  obtain ⟨key, candidate, bound, sealed, encrypted, nonce, width, next, prepared, bindingEq,
    contextSame, written, responseId, hidden, input, frame⟩ := receipt
  have current : (⟨state.server.identity, state.identityKeyId⟩ : pqxdh.ServerBinding) = binding setup publicValue :=
    (prepare_binding state.control token.pending _ _ candidate prepared).symm.trans projected.1
  have publicKey : state.server.identity = PqxdhRootTableInitialization.rootArray publicValue.identity.ed25519 :=
    congrArg pqxdh.ServerBinding.identity_public_key current
  have identifier : state.identityKeyId = setup.serverKeyId :=
    congrArg pqxdh.ServerBinding.identity_key_id current
  have fields := PqxdhServerAuthNegativeControl.prepare_commit_fields state.control token.pending _ _ candidate prepared
  refine ⟨publicKey, identifier, ?_, ?_⟩
  · rw [input]
    change sealed.context.senderId.val = setup.serverKeyId.val
    rw [contextSame]
    exact congrArg (fun id : U64 => id.val) (fields.2.2.1.trans identifier)
  · rw [input]
    change sealed.context.associatedData = _
    rw [contextSame]
    change absBytes candidate.associated_data = _
    rw [PqxdhServerAuthPublicationIdentity.prepared_bytes state.control token.pending _ _ candidate prepared,
      publicKey, projected.2.1, PqxdhRootTableInitialization.rootArray_bytes,
      PqxdhRootTableInitialization.rootArray_bytes]

end BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding.prepare_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding.prepare_binding

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding.record_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding.record_fields
