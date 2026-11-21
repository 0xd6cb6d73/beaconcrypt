-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformInterpret

/-! The source signer receives only a complete signing request. A private chronological hash cut supplies its unsigned payload and digest; it never inverts the shared hash cache. The actual source hash continuation establishes the cut before the actual Server outgoing signing stage. True primitive draws and complete native World state are retained, including failed signing and later publication. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command DispatchResult replyBytes)
open RegistrationSigningShared (SignReply)
variable {n : Nat} {Encoded Value : Type}
variable {m : Type → Type} [Monad m]

structure Cut where
  request : registration.HashRequest
  digest : CtxRomAuth.CtxDigest

def Cut.payload (cut : Cut) (role : authentication.AuthRole) : MldsaTranscriptAuth.Payload :=
  ⟨TranscriptAuthInputsRefinement.absRole role, hashBytes cut.request⟩

abbrev State (n : Nat) := RegistrationWorldSigning.State n × Option Cut

def liftNative (coins : QueryImpl unifSpec m) (work : StateT (RegistrationWorldSigning.State n) ProbComp Value) :
    StateT (State n) m Value := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> simulateQ coins (work.run before.1)

noncomputable def hash (coins : QueryImpl unifSpec m)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply) (request : registration.HashRequest) :
    StateT (State n) m CtxRomAuth.CtxDigest := do
  let digest ← liftNative coins (RegistrationWorldSigning.outgoing sign (.hash request))
  modify fun before => (before.1, some ⟨request, digest⟩)
  pure digest

noncomputable def sign (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply) (request : registration.MldsaSigningRequest) :
    StateT (State n) m SignReply := fun before =>
  match before.2 with
  | none =>
      (fun result => (result.1, ((result.2, before.1.2), none))) <$>
        simulateQ coins ((PqxdhRecordLiftWorld.sampled (primitive request)).run before.1.1)
  | some cut =>
      (liftNative coins (RegistrationWorldSigning.outgoing primitive
        (.sign request (cut.payload request.role) cut.digest))).run before

noncomputable def forward (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (State n) m)
  | .hash request => hash coins primitive request
  | .sign request payload digest => liftNative coins (RegistrationWorldSigning.outgoing primitive (.sign request payload digest))

noncomputable def source (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (State n) m)
  | .hash request => hash coins primitive request
  | .sign request _ _ => sign coins primitive request

variable [LawfulMonad m]

theorem hash_run (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply) (request : registration.HashRequest)
    (before : State n) :
    (hash coins primitive request).run before =
      (fun result => (result.1, (result.2, some (⟨request, result.1⟩ : Cut)))) <$>
        simulateQ coins ((RegistrationWorldSigning.outgoing primitive (.hash request)).run before.1) := by
  simp only [hash, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
  change ((fun result => (result.1, (result.2, before.2))) <$>
    simulateQ coins ((RegistrationWorldSigning.outgoing primitive (.hash request)).run before.1) >>=
    fun result => pure (result.1, (result.2.1, some (⟨request, result.1⟩ : Cut)))) = _
  simp only [bind_pure_comp, Functor.map_map]

omit [LawfulMonad m] in
theorem sign_cut (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply) (request : registration.MldsaSigningRequest)
    (cut : Cut) (before : RegistrationWorldSigning.State n) :
    (sign coins primitive request).run (before, some cut) =
      (fun result => (result.1, (result.2, some cut))) <$>
        simulateQ coins ((RegistrationWorldSigning.outgoing primitive
          (.sign request (cut.payload request.role) cut.digest)).run before) := rfl

private theorem forward_query (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : State n) :
    Prod.map id Prod.fst <$> (forward coins primitive query).run before =
      simulateQ coins ((RegistrationWorldSigning.outgoing primitive query).run before.1) := by
  cases query with
  | hash request => rw [forward, hash_run]; simp only [Functor.map_map, Prod.map, id_eq]; exact id_map _
  | sign request payload digest =>
      change Prod.map id Prod.fst <$> ((fun result => (result.1, (result.2, before.2))) <$>
        simulateQ coins ((RegistrationWorldSigning.outgoing primitive (.sign request payload digest)).run before.1)) = _
      simp only [Functor.map_map, Prod.map, id_eq]
      exact id_map _

theorem forward_program (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Value) (before : State n) :
    Prod.map id Prod.fst <$> (simulateQ (forward coins primitive) work).run before =
      simulateQ coins ((simulateQ (RegistrationWorldSigning.outgoing primitive) work).run before.1) := by
  have same := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (forward coins primitive)
    (fun query => RegistrationNativePlatformInterpret.state coins (RegistrationWorldSigning.outgoing primitive query))
    Prod.fst (forward_query coins primitive) work before
  rw [← RegistrationNativePlatformInterpret.state_simulate] at same
  exact same

private theorem submit_source (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply)
    (command : Command) (digest : CtxRomAuth.CtxDigest) (stage : RegistrationSigningShared.Stage)
    (encoded : core.option.Option Encoded) (request : registration.HashRequest)
    (transcript : hashBytes request = command.payload.transcript)
    (aligned : match stage with
      | .server pending => ∀ selected, pending.request = .ok selected →
          TranscriptAuthInputsRefinement.absRole selected.role = command.payload.role
      | _ => True)
    (before : RegistrationWorldSigning.State n) :
    (simulateQ (source coins primitive) (RegistrationSigningShared.submit command digest stage encoded)).run
        (before, some (⟨request, digest⟩ : Cut)) =
      (simulateQ (forward coins primitive) (RegistrationSigningShared.submit command digest stage encoded)).run
        (before, some (⟨request, digest⟩ : Cut)) := by
  cases stage with
  | server pending =>
      simp only [RegistrationSigningShared.submit]
      cases called : pending.request with
      | fail error | div => simp only [RegistrationSigningShared.continueWith, simulateQ_pure]
      | ok selected =>
          have payload : (Cut.mk request digest).payload selected.role = command.payload := by
            change MldsaTranscriptAuth.Payload.mk _ _ = _
            rw [aligned selected called, transcript]
          have same : (sign coins primitive selected).run (before, some (⟨request, digest⟩ : Cut)) =
              (liftNative coins (RegistrationWorldSigning.outgoing primitive
                (.sign selected command.payload digest))).run (before, some (⟨request, digest⟩ : Cut)) := by
            change (liftNative coins (RegistrationWorldSigning.outgoing primitive
              (.sign selected ((Cut.mk request digest).payload selected.role) digest))).run _ = _
            rw [payload]
          simp only [RegistrationSigningShared.continueWith, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, source, forward, simulateQ_pure]
          rw [same]
  | serverStopped previous => rfl

/-- Actual source hash/sign continuations derive the journal alignment, including every later signature/publication outcome. -/
theorem dispatch_source (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply)
    (command : Command) (encoded : core.option.Option Encoded) (before : State n) :
    (simulateQ (source coins primitive) (RegistrationSigningShared.dispatch command encoded)).run before =
      (simulateQ (forward coins primitive) (RegistrationSigningShared.dispatch command encoded)).run before := by
  obtain ⟨request, requested, transcript⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact command
  simp only [RegistrationSigningShared.dispatch, requested, RegistrationSigningShared.continueWith,
    simulateQ_bind, simulateQ_spec_query, source, forward, StateT.run_bind, hash_run, bind_map_left]
  apply bind_congr
  intro result
  cases command with
  | server hashing =>
      obtain ⟨pending, selected, resumed, selectedRun, _key, role, _context, _input⟩ :=
        RegistrationSigningShared.resume_server_request hashing result.1
      rw [resumed]
      apply submit_source coins primitive (.server hashing) result.1 (.server pending) encoded request transcript
      intro query queryRun
      have same : query = selected := RustM.ok.inj (queryRun.symm.trans selectedRun)
      subst query
      simp only [role, TranscriptAuthInputsRefinement.absRole,
        BeaconcryptCore.Refinement.RegistrationSigningTrace.Command.payload]

/-- Erasing only the private journal gives the entire native World and chronological ML attempts of the source continuation. -/
theorem dispatch_world (coins : QueryImpl unifSpec m)
    (primitive : registration.MldsaSigningRequest → ProbComp SignReply)
    (command : Command) (encoded : core.option.Option Encoded) (before : State n) :
    Prod.map id Prod.fst <$> (simulateQ (source coins primitive)
        (RegistrationSigningShared.dispatch command encoded)).run before =
      simulateQ coins ((simulateQ (RegistrationWorldSigning.outgoing primitive)
        (RegistrationSigningShared.dispatch command encoded)).run before.1) := by
  rw [dispatch_source]
  exact forward_program coins primitive _ before

end BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.hash_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.hash_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.sign_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.sign_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.forward_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.forward_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.dispatch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.dispatch_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.dispatch_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal.dispatch_world
