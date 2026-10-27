import BeaconcryptCore.Computational.PqxdhInitialBuilderContext

/-!
The Server candidate records its actual initializer return only after its original identity and peer-reservation gates reach that return. The receipt remains private even if a subsequent plaintext check, seal, writer or publication fails. Recording an attempt is separate from installing an owner or producing a cryptographic seal.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness)
open PqxdhInitialGenericPublication
open PqxdhInitialGenericBuilder (continueRust)
variable {Kernel M P Consumed : Type}

structure Receipt (Kernel : Type) where
  candidate : pqxdh.ServerRegistrationCandidate
  initial : Kernel

abbrev Result (Kernel M P Consumed : Type) :=
  RustM (Option Response × State Kernel M P Consumed) × Option (Receipt Kernel)

section Effects
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def afterInitial (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (kernel : Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : State Kernel M P Consumed) :
    m (RustM (Option Response × State Kernel M P Consumed)) :=
  let plaintext := data.getD registrationWitness
  if plaintext.isEmpty then pure (.ok (none, state))
  else if 8 + plaintext.length ≤ Usize.max then do
    let allocated ← aux (.reservePlaintext (8 + plaintext.length))
    if !allocated then pure (.ok (none, state)) else
      continueRust candidate.key_id_binding fun binding =>
        RustM.ok <$> PqxdhInitialGenericPublication.afterInitialization calls aux candidate
          (absBytes binding.bytes ++ plaintext) kernel metadata state
  else pure (.ok (none, state))

noncomputable def candidate (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (initial : RustM Kernel) (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : State Kernel M P Consumed) : m (Result Kernel M P Consumed) := do
  let valid ← aux (.checkIdentity pending.beacon_identity_public_key)
  if !valid then pure (.ok (none, state), none) else do
    let reserved ← aux .reservePeer
    if !reserved then pure (.ok (none, state), none) else
      match initial with
      | .fail error => pure (.fail error, none)
      | .div => pure (.div, none)
      | .ok kernel =>
          (fun result => (result, some ⟨pending, kernel⟩)) <$>
            afterInitial calls aux kernel pending data metadata state

noncomputable def used (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (initial : RustM Kernel) (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : State Kernel M P Consumed) : m (Result Kernel M P Consumed) :=
  match pqxdh.server_next_key_id state.control with
  | .fail error => pure (.fail error, none)
  | .div => pure (.div, none)
  | .ok (.Err _) => pure (.ok (none, state), none)
  | .ok (.Ok next) =>
      let availability := if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available
      match PqxdhRegistrationInputs.prepare state.control pending ⟨state.server.identity, state.identityKeyId⟩ availability with
      | .fail error => pure (.fail error, none)
      | .div => pure (.div, none)
      | .ok (.Err _) => pure (.ok (none, state), none)
      | .ok (.Ok pending) => candidate calls aux initial pending data metadata state

noncomputable def ready (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m) (initial : RustM Kernel)
    (binding : pqxdh.ServerBinding) (input : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : P) (state : State Kernel M P Consumed) : m (Result Kernel M P Consumed) :=
  used calls aux initial (PqxdhAcceptedRegistration.usedReady source.crypto binding input) input.application metadata state

/-- Receipt erasure preserves the actual identity/reservation gates, initializer return and complete later plaintext, first-send and writer continuation. -/
theorem candidate_erase (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (initial : RustM Kernel) (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : State Kernel M P Consumed) :
    Prod.fst <$> candidate calls aux initial pending data metadata state =
      PqxdhInitialGenericBuilder.candidate calls aux initial pending data metadata state := by
  simp only [candidate, PqxdhInitialGenericBuilder.candidate, map_bind]
  apply bind_congr
  intro valid
  cases valid
  · simp only [Bool.not_false, ite_true, map_pure]
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, map_bind]
    apply bind_congr
    intro reserved
    cases reserved
    · simp only [Bool.not_false, ite_true, map_pure]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases initial <;> simp only [continueRust, map_pure, Functor.map_map, afterInitial, id_map']

/-- Actual counter allocation, occupied-peer admission and consumed-input preparation retain their original failure paths before the same recorded candidate continuation. -/
theorem used_erase (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (initial : RustM Kernel) (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : State Kernel M P Consumed) :
    Prod.fst <$> used calls aux initial pending data metadata state =
      PqxdhInitialGenericBuilder.usedBuild calls aux initial pending data metadata state := by
  unfold used PqxdhInitialGenericBuilder.usedBuild
  cases allocated : pqxdh.server_next_key_id state.control with
  | fail error => simp only [continueRust, map_pure]
  | div => simp only [continueRust, map_pure]
  | ok next =>
      cases next with
      | Err error => simp only [continueRust, map_pure]
      | Ok next =>
          simp only [continueRust]
          cases preparation : PqxdhRegistrationInputs.prepare state.control pending
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => simp only [map_pure]
          | div => simp only [map_pure]
          | ok prepared =>
              cases prepared with
              | Err error => simp only [map_pure]
              | Ok pending => exact candidate_erase calls aux initial pending data metadata state

/-- The receipt uses the same consumed Ready input and actual source binding, preserving the complete original registration builder. -/
theorem ready_erase (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m) (initial : RustM Kernel)
    (binding : pqxdh.ServerBinding) (input : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : P) (state : State Kernel M P Consumed) :
    Prod.fst <$> ready source calls aux initial binding input metadata state =
      PqxdhInitialGenericBuilder.readyBuild source calls aux initial binding input metadata state :=
  used_erase calls aux initial _ _ metadata state

end Effects

section Interpretation
variable {κ : Type} {spec : OracleSpec κ} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The receipt's complete post-initialization tail commutes with the actual handler, preserving every failure, seal, erase and writer effect. -/
theorem after_interpretation (impl : QueryImpl spec m)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl AuxSpec (OracleComp spec)) (kernel : Kernel)
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : State Kernel M P (List Pqxdh.Bytes)) :
    simulateQ impl (afterInitial calls aux kernel pending data metadata state) =
      afterInitial (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls) (impl ∘ₛ aux)
        kernel pending data metadata state := by
  dsimp only [afterInitial]
  split
  · exact simulateQ_pure _ _
  · split
    · simp only [simulateQ_bind]
      apply bind_congr
      intro allocated
      cases allocated
      · simp only [Bool.not_false, ite_true, simulateQ_pure]
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        cases binding : pending.key_id_binding with
        | fail error => exact simulateQ_pure _ _
        | div => exact simulateQ_pure _ _
        | ok binding =>
            simp only [continueRust, simulateQ_map, PqxdhInitialPendingBuilder.after_interpretation]
    · exact simulateQ_pure _ _

/-- The actual candidate handler preserves its initializer receipt and every original gate when interpreted into the source state monad. -/
theorem candidate_interpretation (impl : QueryImpl spec m)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl AuxSpec (OracleComp spec)) (initial : RustM Kernel)
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : State Kernel M P (List Pqxdh.Bytes)) :
    simulateQ impl (candidate calls aux initial pending data metadata state) =
      candidate (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls) (impl ∘ₛ aux)
        initial pending data metadata state := by
  simp only [candidate, simulateQ_bind]
  apply bind_congr
  intro valid
  cases valid
  · simp only [Bool.not_false, ite_true, simulateQ_pure]
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind]
    apply bind_congr
    intro reserved
    cases reserved
    · simp only [Bool.not_false, ite_true, simulateQ_pure]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases initial <;> simp only [simulateQ_pure, simulateQ_map, after_interpretation]

/-- The original current peer allocation and complete Ready builder commute with the same interpreter, including all Rust error branches. -/
theorem ready_interpretation (impl : QueryImpl spec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec))
    (initial : RustM Kernel) (binding : pqxdh.ServerBinding) (input : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) :
    simulateQ impl (ready source calls aux initial binding input metadata state) =
      ready source (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls) (impl ∘ₛ aux)
        initial binding input metadata state := by
  unfold ready used
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => exact simulateQ_pure _ _
  | div => exact simulateQ_pure _ _
  | ok value =>
      cases value with
      | Err error => exact simulateQ_pure _ _
      | Ok key =>
          dsimp only
          cases preparation : PqxdhRegistrationInputs.prepare state.control
            (PqxdhAcceptedRegistration.usedReady source.crypto binding input)
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => exact simulateQ_pure _ _
          | div => exact simulateQ_pure _ _
          | ok result =>
              cases result with
              | Err error => exact simulateQ_pure _ _
              | Ok candidate => exact candidate_interpretation impl calls aux initial candidate input.application metadata state

end Interpretation

/-- Each attempted-initializer receipt comes after the actual successful identity and reservation replies and records the literal supplied initializer return before the complete later source continuation. -/
theorem candidate_origin {Auxiliary ξ : Type} {base : OracleSpec ξ}
    (calls : RawCtxChainOwner.Calls Kernel (StateT Auxiliary (OracleComp base)))
    (aux : QueryImpl AuxSpec (StateT Auxiliary (OracleComp base)))
    (initial : RustM Kernel) (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : State Kernel M P Consumed) (before : Auxiliary)
    (result : Result Kernel M P Consumed × Auxiliary)
    (supported : result ∈ support ((candidate calls aux initial pending data metadata state).run before))
    (receipt : Receipt Kernel) (recorded : result.1.2 = some receipt) :
    ∃ (atIdentity atReserved : Auxiliary),
      (true, atIdentity) ∈ support ((aux (.checkIdentity pending.beacon_identity_public_key)).run before) ∧
      (true, atReserved) ∈ support ((aux .reservePeer).run atIdentity) ∧
      receipt.candidate = pending ∧ initial = .ok receipt.initial ∧
      (result.1.1, result.2) ∈ support ((afterInitial calls aux receipt.initial pending data metadata state).run atReserved) := by
  unfold candidate at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨valid, checked, rest⟩ := supported
  cases validFound : valid.1
  case false =>
    simp only [validFound, Bool.not_false, ite_true, StateT.run_pure, mem_support_pure_iff] at rest
    subst result
    cases recorded
  case true =>
    simp only [validFound, Bool.not_true, Bool.false_eq_true, ite_false, StateT.run_bind, mem_support_bind_iff] at rest
    obtain ⟨reserved, reservedSupport, rest⟩ := rest
    cases reservedFound : reserved.1
    case false =>
      simp only [reservedFound, Bool.not_false, ite_true, StateT.run_pure, mem_support_pure_iff] at rest
      subst result
      cases recorded
    case true =>
      simp only [reservedFound, Bool.not_true, Bool.false_eq_true, ite_false] at rest
      cases initial
      case fail error =>
        simp only [StateT.run_pure, mem_support_pure_iff] at rest
        subst result
        cases recorded
      case div =>
        simp only [StateT.run_pure, mem_support_pure_iff] at rest
        subst result
        cases recorded
      case ok kernel =>
        simp only [StateT.run_map, support_map] at rest
        obtain ⟨completed, tailReached, rfl⟩ := rest
        cases Option.some.inj recorded
        exact ⟨valid.2, reserved.2, by simpa only [← validFound] using checked,
          by simpa only [← reservedFound] using reservedSupport, rfl, rfl, tailReached⟩

/-- A receipt in the complete consumed-input builder identifies its actual allocation and preparation, then the same supported candidate tail. The supplied initial value is its literal successful constructor return. -/
theorem used_origin {Auxiliary ξ : Type} {base : OracleSpec ξ}
    (calls : RawCtxChainOwner.Calls Kernel (StateT Auxiliary (OracleComp base)))
    (aux : QueryImpl AuxSpec (StateT Auxiliary (OracleComp base)))
    (initial : RustM Kernel) (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : State Kernel M P Consumed) (before : Auxiliary)
    (result : Result Kernel M P Consumed × Auxiliary)
    (supported : result ∈ support ((used calls aux initial pending data metadata state).run before))
    (receipt : Receipt Kernel) (recorded : result.1.2 = some receipt) :
    ∃ next,
      pqxdh.server_next_key_id state.control = .ok (.Ok next) ∧
      PqxdhRegistrationInputs.prepare state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) =
          .ok (.Ok receipt.candidate) ∧
      initial = .ok receipt.initial ∧
      result ∈ support ((candidate calls aux initial receipt.candidate data metadata state).run before) := by
  unfold used at supported
  split at supported
  all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; subst result; cases recorded }
  rename_i next allocated
  dsimp only at supported
  cases prepared : PqxdhRegistrationInputs.prepare state.control pending
    ⟨state.server.identity, state.identityKeyId⟩
    (if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
  | fail error => simp only [prepared, StateT.run_pure, mem_support_pure_iff] at supported; subst result; cases recorded
  | div => simp only [prepared, StateT.run_pure, mem_support_pure_iff] at supported; subst result; cases recorded
  | ok outcome =>
      cases outcome with
      | Err error => simp only [prepared, StateT.run_pure, mem_support_pure_iff] at supported; subst result; cases recorded
      | Ok found =>
          simp only [prepared] at supported
          obtain ⟨_, _, _, _, candidateFound, initialized, _⟩ :=
            candidate_origin calls aux initial found data metadata state before result supported receipt recorded
          exact ⟨next, allocated, candidateFound ▸ prepared, initialized, candidateFound ▸ supported⟩

open PqxdhInitialPendingPost
variable {ι Chain I D K X SourceResponse Shared : Type} {extra : OracleSpec ι} {S B : Nat}

noncomputable def build (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (input : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (Front Chain M P I D K S B) (OracleComp (Spec extra Chain I D K X SourceResponse Shared S B))
      (RustM (Option Response) × Option (Receipt (KernelOf Chain))) := fun before =>
  let current := PqxdhInitialPendingBuilder.consume index input before
  let selected := PqxdhInitialPendingBuilder.selected sender index current
  (fun result =>
    let installed := PqxdhInitialPendingBuilder.reinstall index current result.1
    ((installed.1, result.2), installed.2)) <$>
      ready source calls auxForward initial ⟨selected.server.identity, selected.identityKeyId⟩ input metadata selected

/-- Erasing only the attempted-initializer receipt preserves the actual consumed state, returned response and complete indexed peer/control reinstallation. -/
theorem build_erase (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (input : PqxdhPrivateAcceptedRoot.Ready) (before : Front Chain M P I D K S B) :
    Prod.map Prod.fst id <$>
      (build (extra := extra) (X := X) (SourceResponse := SourceResponse) (Shared := Shared)
        source initial sender index metadata input).run before =
      (PqxdhInitialPendingBuilder.build source initial sender index metadata input).run before := by
  simp only [build, PqxdhInitialPendingBuilder.build, StateT.run, Functor.map_map]
  rw [← ready_erase]
  simp only [Functor.map_map]
  rfl

/-- Any actual interpretation of the complete indexed Builder retains the literal successful initializer in its private receipt. The source handler and all intermediate effects remain unrestricted. -/
theorem build_initialized {Auxiliary ξ : Type} {base : OracleSpec.{0, 0} ξ}
    (impl : QueryImpl (Spec extra Chain I D K X SourceResponse Shared S B) (StateT Auxiliary (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (input : PqxdhPrivateAcceptedRoot.Ready) (before : Front Chain M P I D K S B) (state : Auxiliary)
    (result : ((RustM (Option Response) × Option (Receipt (KernelOf Chain))) × Front Chain M P I D K S B) × Auxiliary)
    (supported : result ∈ support ((simulateQ impl
      ((build source initial sender index metadata input).run before)).run state))
    (receipt : Receipt (KernelOf Chain)) (recorded : result.1.1.2 = some receipt) :
    initial = .ok receipt.initial := by
  simp only [build, StateT.run, simulateQ_map] at supported
  have mapped := PqxdhInitialBuilderReceipt.ready_interpretation impl source calls auxForward initial
    ⟨(PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index input before)).server.identity,
      (PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index input before)).identityKeyId⟩
    input metadata (PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index input before))
  rw [mapped] at supported
  change result ∈ support (StateT.run _ state) at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨original, reached, rfl⟩ := supported
  obtain ⟨_, _, _, initialized, _⟩ := used_origin
    (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls) (impl ∘ₛ auxForward) initial _ _ metadata _
      state original reached receipt recorded
  exact initialized
/-- Every original oracle-class allowance is unchanged by receipt recording; all initializer-independent builder work stays in the source budget. -/
theorem queries (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (input : PqxdhPrivateAcceptedRoot.Ready) (before : Front Chain M P I D K S B)
    (predicate : (Spec extra Chain I D K X SourceResponse Shared S B).Domain → Prop)
    [DecidablePred predicate] (budget : Nat) :
    ((build (extra := extra) source initial sender index metadata input).run before).IsQueryBoundP predicate budget ↔
      ((PqxdhInitialPendingBuilder.build (extra := extra) source initial sender index metadata input).run before).IsQueryBoundP predicate budget := by
  rw [← build_erase, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.candidate_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.candidate_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.used_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.used_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.ready_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.ready_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.after_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.after_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.candidate_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.candidate_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.ready_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.ready_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.candidate_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.candidate_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.used_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.used_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.build_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.build_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.build_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.build_initialized

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt.queries
