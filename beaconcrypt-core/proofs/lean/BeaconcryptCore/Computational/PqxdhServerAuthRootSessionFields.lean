import BeaconcryptCore.Computational.PqxdhServerAuthRootExecution
import BeaconcryptCore.Computational.PqxdhRegistrationResponse

/-! Actual native session fields at the source-root initialization occurrences. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Native successful publication supplies the exact pending/current binding check; the proof uses the actual complete builder support and allows all earlier callback effects. -/
theorem native_binding (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (before after : ServerState) (cache next : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : (ok (some response, after), next) ∈ support
      ((simulateQ (tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.build setup.source pending root payload () before)).run cache)) :
    pending.server_binding = ⟨before.server.identity, before.identityKeyId⟩ := by
  rcases PqxdhRegistrationResponse.build_publication (tailImpl setup codec checks) setup.source pending root
      payload () before cache (ok (some response, after), next) supported with failed |
      ⟨_, candidate, _, _, _, prepared, _⟩
  · cases RustM.ok.inj failed
  · exact PqxdhServerAuthPhase1Binding.prepare_binding before.control pending _ _ candidate prepared

/-- The exact native successful build has one source seal context, the actual ordered identity AD, and an initializer run using the supplied source root. No writer totality or decode/read-back premise is needed. -/
theorem native_context (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (before after : ServerState) (cache : CtxRomAuth.CtxRO.QueryCache)
    (logged : List RawCtxSourceSend.SealContext) (next : CtxRomAuth.CtxRO.QueryCache)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : (ok (some response, after), (logged, next)) ∈ support
      ((simulateQ (tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.build setup.source pending root payload () before)).run ([], cache))) :
    ∃ candidate kernel,
      candidate.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      candidate.server_identity_public_key = before.server.identity ∧
      candidate.server_identity_key_id = before.identityKeyId ∧
      PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel ∧
      absBytes candidate.associated_data =
        Pqxdh.assocData (absBytes before.server.identity) (absBytes pending.beacon_identity_public_key) ∧
      logged = [PqxdhServerRegistrationPublication.firstContext candidate
        (Pqxdh.LE64 candidate.key_id.val ++ payload.getD PqxdhServerRegistrationPublication.registrationWitness)] := by
  obtain ⟨candidate, kernel, _, _, beacon, server, identifier, _, _, ad, initialized, _, _, _, _, log⟩ :=
    PqxdhServerAuthNegativeControl.build_published setup codec checks pending root payload before cache
      (ok (some response, after), (logged, next)) supported response rfl
  exact ⟨candidate, kernel, beacon, server, identifier, initialized,
    PqxdhServerAuthPublicationIdentity.source_bytes _ _ _ ad, log⟩

/-- An active Beacon on the original source path retains the exact successful output of the actual target Phase1 generation. Writer failure is excluded by the reached phase, not by writer totality. -/
theorem path_generation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (sampled : context ∈ support (contextSample setup codec))
    (initial : PqxdhJointDhExtractFamily.State)
    (current : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) calls current)
    (active : InitSent current.1) :
    ∃ bytes,
      codec.write1 (PqxdhServerAuthNegativeControl.beaconCandidate setup (context.publicValue setup)
        context.beaconSeed context.oneTime context.keys.1) = some bytes ∧
      context.published = (some bytes, PqxdhServerAuthNegativeControl.publishedBeacon setup
        (context.publicValue setup) context.beaconSeed context.oneTime context.keys.2) ∧
      current.1.beacon = context.published.2 := by
  have retained := PqxdhServerAuthRootProvenance.path_active setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar (contextState setup context, initial) current calls path active
  have generated := (PqxdhServerAuthPhase1Generation.context_generated setup codec context sampled).2.2.2.2.2
  rw [PqxdhServerAuthNegativeControl.phase1Run_eq] at generated
  simp only [support_pure, Set.mem_singleton_iff] at generated
  cases written : codec.write1 (PqxdhServerAuthNegativeControl.beaconCandidate setup
    (context.publicValue setup) context.beaconSeed context.oneTime context.keys.1)
  · simp [InitSent, retained, contextState, initialGameState, generated, written, freshBeacon] at active
  · exact ⟨_, rfl, by simpa only [written] using generated, retained⟩

/-- The original successful builder's exact native context remains in the same session's complete final ghost log. Its token and root are the actual consumed values. -/
theorem path_build_context (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (beaconSeed seed : IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (first final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar first calls final)
    (index : Nat) (data : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : GameState KemSK) (roots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (built : (⟨.inr (.build index data), some response, before, after, roots⟩ : Call KemSK) ∈ calls) :
    ∃ token candidate kernel,
      before.pending index = some token ∧
      token.pending.server_binding = ⟨before.server.server.identity, before.server.identityKeyId⟩ ∧
      candidate.beacon_identity_public_key = token.pending.beacon_identity_public_key ∧
      candidate.server_identity_public_key = before.server.server.identity ∧
      candidate.server_identity_key_id = before.server.identityKeyId ∧
      PqxdhRootTableInitialization.initialKernelRun setup.source false token.root = ok kernel ∧
      absBytes candidate.associated_data = Pqxdh.assocData (absBytes before.server.server.identity)
        (absBytes token.pending.beacon_identity_public_key) ∧
      (index, PqxdhServerRegistrationPublication.firstContext candidate
        (Pqxdh.LE64 candidate.key_id.val ++ data.getD PqxdhServerRegistrationPublication.registrationWitness))
          ∈ final.1.ghost.seals := by
  obtain ⟨earlier, later, prior, next, split, preceding, reached, suffix⟩ :=
    path_occurrence setup codec checks publicValue beaconSeed seed scalar first final calls path _ built
  have source := callback_source setup codec checks publicValue beaconSeed seed scalar _ prior next reached
  obtain ⟨token, published, installed, logged, cache, found, _, _, _, _, native, _, sealed⟩ :=
    PqxdhServerAuthRootInitialization.build_receipt setup codec checks seed scalar index data
      (before, prior) response (after, next) source
  obtain ⟨candidate, kernel, beacon, server, identifier, initialized, ad, log⟩ :=
    native_context setup codec checks token.pending token.root data before.server _ before.ctx logged cache response native
  refine ⟨token, candidate, kernel, found,
    native_binding setup codec checks token.pending token.root data before.server _ _ _ response native,
    beacon, server, identifier, initialized, ad, ?_⟩
  apply (PqxdhServerAuthRootProvenance.path_grows setup codec checks publicValue beaconSeed seed scalar
    (after, next) final later suffix).seals.subset
  rw [sealed, log]
  exact List.mem_append_right _ (by simp)

end BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.native_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.native_binding

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.native_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.native_context

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.path_generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.path_generation

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.path_build_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields.path_build_context
