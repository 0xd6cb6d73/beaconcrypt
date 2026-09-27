import BeaconcryptCore.Computational.RawCtxSelectedMessageDriver

/-!
The selected-material compiler retains the actual receive-window limit under every possible typed service reply. This is source control and resource accounting: selected material does not change counters, and repeated or colliding private requests remain counted. Prior-table work and opening/sealing work use separate budgets. No primitive security premise is introduced.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf RawCtxSelectedMessageDriver RawCtxSelectedParentEntry
open RawCtxInterpretedReceive

def cost {Material Context : Type} : Effect Material Context → Nat
  | .kdfRequested pending => max 1 pending.remaining.val
  | _ => 0

/-- The literal zero/one-remaining source branches cannot ask another KDF question, regardless of material labels or callback values. -/
theorem resume_small {Material Context : Type} (pending : Kdf Material Context)
    (reply : RatchetChain × Material) (small : pending.remaining.val ≤ 1) :
    ∃ next, resume pending (ok reply) = ok next ∧ cost next = 0 := by
  by_cases hzero : pending.remaining = 0#u8
  · simp [resume, hzero, rejected, cost]
  · have hone : pending.remaining = 1#u8 := by scalar_tac
    simp only [resume, hone, if_true]
    obtain ⟨advanced, hadvanced⟩ := control.advance_receive_target_total pending.working_control
    cases hseq : advanced.sequence <;> simp only [hadvanced, hseq, bind_tc_ok, rejected]
    all_goals first | exact ⟨_, rfl, rfl⟩ | skip
    rename_i sequence
    obtain ⟨valid, hvalid⟩ := refined.pending_receive_is_valid_ok pending.entry
      { committed_control := advanced.state, final_receive_chain := reply.1,
        staged_slots := pending.staged_slots, target_sequence := sequence,
        target_material := reply.2, first_slot := pending.first_slot, skipped := pending.skipped }
      pending.target
    simp only [hvalid, bind_tc_ok]
    repeat' first | exact ⟨_, rfl, rfl⟩ | split

/-- The actual remaining-counter allowance decreases for every possible typed chain/material reply. -/
theorem resume_cost {Material Context : Type} (pending : Kdf Material Context) (reply : RatchetChain × Material) :
    cost (normalResume pending reply) + 1 ≤ cost (.kdfRequested pending) := by
  by_cases small : pending.remaining.val ≤ 1
  · obtain ⟨next, hnext, hcost⟩ := resume_small pending reply small
    have same := RustM.ok.inj ((normalResume_exact pending reply).symm.trans hnext)
    rw [same, hcost]
    simp only [cost]
    omega
  · have progress := (resume_progress pending reply).choose_spec.2
    change Progress pending (normalResume pending reply) at progress
    cases hnext : normalResume pending reply with
    | rejected => simp [cost]
    | openRequested => simp [cost]
    | kdfRequested next =>
      have remaining := progress.2
      simp only [hnext] at remaining
      simp only [cost]
      omega

/-- Every adaptive receive continuation retains the refined KDF allowance, including rejected zero-count phases. -/
theorem program_cost {Material Context Plaintext : Type} (effect : Effect Material Context) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP
      (fun request => request.isLeft = true) (cost effect) := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context => simp [program]
    | openRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp [cost]
    | kdfRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp only [Sum.isLeft, not_true_eq_false, false_or, if_true]
      refine ⟨by simp [cost], fun reply => ?_⟩
      apply (ih _ (hdepth ▸ normalResume_rank pending reply) _ rfl).mono
      have decrease := resume_cost pending reply
      omega

/-- Material interpretation changes no source KDF counter or malformed-phase allowance. -/
theorem cost_native {Material Context : Type} (value : Material → RatchetMaterial) (effect : Effect Material Context) :
    RawCtxKdfBudget.kdfCost (nativeEffect (mapEffect value effect)) = cost effect := by
  cases effect <;> rfl

/-- The exact native admission theorem supplies the same 51-call limit for opaque material; no selected key or material-injectivity premise is required. -/
theorem begin_cost {Context : Type} (kernel : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : Context) : cost (normalBegin kernel sequence context) ≤ 51 := by
  let value := interpret (List.Vector.replicate 32 (0 : UInt8))
  have native := RawCtxKdfBudget.begin_cost
    (RawCtxSelectedMessageReveals.nativeKernel (List.Vector.replicate 32 (0 : UInt8)) kernel) sequence context
  change RawCtxKdfBudget.kdfCost (RawCtxOwnerOracle.begin
    ⟨RawCtxMaterialInterpretation.mapRefined value kernel⟩ sequence context) ≤ 51 at native
  rw [normalBegin_native, normalBegin_map, cost_native] at native
  exact native

/-- The complete material-labelled source receive has at most 51 private derivation requests on every callback branch. -/
theorem receive_kdf {Context Plaintext : Type} (kernel : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : Context) :
    (RawCtxInterpretedReceive.receive (Plaintext := Plaintext) kernel sequence context).IsQueryBoundP
      (fun request => request.isLeft = true) 51 :=
  (program_cost _).mono (begin_cost kernel sequence context)

/-- Forwarding the explicit private table costs at most one lookup and no opening or sealing callback. -/
theorem derive_forward {ι : Type} (extra : OracleSpec ι) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (request : SymmetricRatchetKdfRequest) (selected : Bool) :
    OracleComp.IsQueryBoundP
      (simulateQ (fun address => ((PriorSpec + extra).query (.inl address) : OracleComp (PriorSpec + extra) FullOutput))
        (derive parent target nonce next request))
      (fun query => query.isLeft = selected) (if selected then 1 else 0) := by
  cases parent <;> cases selected <;> simp only [derive, routeLater, route]
  all_goals split_ifs <;> simp only [simulateQ_pure, simulateQ_map, simulateQ_spec_query, isQueryBoundP_map_iff]
  all_goals first | trivial | exact (isQueryBoundP_query_iff _ _ _).mpr (by simp)

/-- A receive callback preserves its service class: one possible prior lookup or one possible opening, with no cross-class work. -/
theorem receive_callback {Context Plaintext : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput)
    (query : (ReceiveSpec Slot Context Plaintext).Domain) (selected : Bool) :
    (receiveCompiler parent target nonce next query).IsQueryBoundP
      (fun service => service.isLeft = selected) (if query.isLeft = selected then 1 else 0) := by
  cases query with
  | inl request =>
    change OracleComp.IsQueryBoundP
      (simulateQ (fun address => ((ReceiveServices Context Plaintext).query (.inl address) :
        OracleComp (ReceiveServices Context Plaintext) FullOutput)) (derive parent target nonce next request))
      (fun service => service.isLeft = selected) (if true = selected then 1 else 0)
    have bound := derive_forward (RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot Context →ₒ core.option.Option Plaintext)
      parent target nonce next request selected
    cases selected <;> simpa only [Sum.isLeft, Bool.false_eq_true, Bool.true_eq_false,
      if_true, if_false] using bound
  | inr pending => exact (isQueryBoundP_query_iff _ _ _).mpr (by cases selected <;> simp)

/-- A send callback preserves the explicit prior-lookup or sealing class with at most one request in that class. -/
theorem send_callback {Context Output : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput)
    (query : (RawCtxInterpretedSend.SendSpec Slot Context Output).Domain) (selected : Bool) :
    (sendCompiler parent target nonce next query).IsQueryBoundP
      (fun service => service.isLeft = selected) (if query.isLeft = selected then 1 else 0) := by
  cases query with
  | inl request =>
    change OracleComp.IsQueryBoundP
      (simulateQ (fun address => ((SendServices Context Output).query (.inl address) :
        OracleComp (SendServices Context Output) FullOutput)) (derive parent target nonce next request))
      (fun service => service.isLeft = selected) (if true = selected then 1 else 0)
    have bound := derive_forward (RawCtxInterpretedSend.Seal Slot Context →ₒ Option Output)
      parent target nonce next request selected
    cases selected <;> simpa only [Sum.isLeft, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false] using bound
  | inr pending => exact (isQueryBoundP_query_iff _ _ _).mpr (by cases selected <;> simp)

/-- The actual complete selected-material receive costs at most 51 prior-table lookups, counting repeated fallback requests. -/
theorem receive_prior {Context Plaintext : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : Context) :
    (RawCtxSelectedMessageDriver.receive (Plaintext := Plaintext) parent target nonce next kernel sequence context).IsQueryBoundP
      (fun service => service.isLeft = true) 51 := by
  apply RawCtxSourceOpen.simulate_bound (receiveCompiler parent target nonce next)
    (fun query => query.isLeft = true) (fun service => service.isLeft = true)
  · exact receive_kdf kernel sequence context
  · exact fun query => receive_callback parent target nonce next query true

/-- A service outside the private-lookup summand is exactly an opening or sealing callback. -/
theorem right_pred {ι κ : Type} :
    (fun query : ι ⊕ κ => query.isLeft = false) = (fun query : ι ⊕ κ => query.isRight = true) := by
  funext query
  cases query <;> simp

/-- Every selected-material receive makes at most one actual opening call, including failed commitment and AEAD outcomes. -/
theorem receive_open {Context Plaintext : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : Context) :
    (RawCtxSelectedMessageDriver.receive (Plaintext := Plaintext) parent target nonce next kernel sequence context).IsQueryBoundP
      (fun service => service.isLeft = false) 1 := by
  apply RawCtxSourceOpen.simulate_bound (receiveCompiler parent target nonce next)
    (fun query => query.isLeft = false) (fun service => service.isLeft = false)
  · simpa only [right_pred, RawCtxInterpretedReceive.receive] using program_open_bound (Plaintext := Plaintext) (normalBegin kernel sequence context)
  · exact fun query => receive_callback parent target nonce next query false

/-- Every selected-material send costs at most one prior-table lookup, including a failed final seal. -/
theorem send_prior {Context Output : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (kernel : RawCtxSelectedMessageReveals.Kernel) (context : Context) :
    (RawCtxSelectedMessageDriver.send (Output := Output) parent target nonce next kernel context).IsQueryBoundP
      (fun service => service.isLeft = true) 1 := by
  apply RawCtxSourceOpen.simulate_bound (sendCompiler parent target nonce next)
    (fun query => query.isLeft = true) (fun service => service.isLeft = true)
  · exact RawCtxInterpretedSend.program_kdf_bound _
  · exact fun query => send_callback parent target nonce next query true

/-- Every selected-material send makes at most one actual sealing callback; successful publication is not assumed. -/
theorem send_seal {Context Output : Type} (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (kernel : RawCtxSelectedMessageReveals.Kernel) (context : Context) :
    (RawCtxSelectedMessageDriver.send (Output := Output) parent target nonce next kernel context).IsQueryBoundP
      (fun service => service.isLeft = false) 1 := by
  apply RawCtxSourceOpen.simulate_bound (sendCompiler parent target nonce next)
    (fun query => query.isLeft = false) (fun service => service.isLeft = false)
  · simpa only [right_pred, RawCtxInterpretedSend.send] using
      RawCtxInterpretedSend.program_seal_bound (Output := Output) (RawCtxInterpretedSend.normalBegin kernel context)
  · exact fun query => send_callback parent target nonce next query false

end BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.resume_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.resume_small
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.resume_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.resume_cost
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.program_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.program_cost
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.cost_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.cost_native
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.begin_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.begin_cost
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.receive_kdf
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.derive_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.derive_forward
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.receive_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.receive_callback
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.send_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.send_callback
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.receive_prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.receive_prior
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.right_pred' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.right_pred
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.receive_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.receive_open
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.send_prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.send_prior
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.send_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageDriverBounds.send_seal
