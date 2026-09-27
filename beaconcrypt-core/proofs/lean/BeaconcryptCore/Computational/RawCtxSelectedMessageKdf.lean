import BeaconcryptCore.Computational.RawCtxSelectedMessageReveals
import BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch
import BeaconcryptCore.Computational.RawCtxFunctionalFamily

/-!
Only a selected private KDF address receives a material marker. The simulator retains the original input, nonce and next chain, compares the complete input/domain address and keeps the unchanged prior lookup everywhere else. A retained predecessor entry has priority even when its address equals the selected address. All three coordinates are reconstructed from the same full76 response in the mathematical source interpretation; the executable routing interface receives no selected message key and performs no fresh draw. Public HKDF calls are outside this private routing interface and remain real.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageKdf
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxFreshChainCut RawCtxSelectedParentTable RawCtxSelectedParentEntry

def response (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) : FullOutput :=
  materialChainEquiv.symm ((key, nonce), next)

noncomputable def known (output : FullOutput) : RatchetChain × Slot :=
  let decoded := RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)
  (decoded.1, .known decoded.2)

noncomputable def step (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) : RatchetChain × Slot :=
  if RawCtxKdfRequestTable.address request = RawCtxSelectedParentPrivatePatch.targetAddress target
  then (concreteChain next, .hidden nonce)
  else known (prior (RawCtxKdfRequestTable.address request))

noncomputable def later (prior : Prior) (entry : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) : RatchetChain × Slot :=
  if RawCtxKdfRequestTable.address request = entry.address then known (realize entry target)
  else step prior target nonce next request

/-- Decoding reconstructs exactly the retained next chain, selected message key and original nonce from their one full76 response. -/
theorem decoded_response (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse (response key nonce next)) =
      (concreteChain next, concreteMaterial (key, nonce)) := by
  have parts := materialChainEquiv.apply_symm_apply ((key, nonce), next)
  rw [decoded_parts]
  exact congrArg (fun value => (concreteChain value.2, concreteMaterial value.1)) parts

/-- Known prior values retain their exact material and chain, even when their key bytes alias the selected message key. -/
theorem known_exact (key : RootOutput) (output : FullOutput) :
    (fun value : RatchetChain × Slot => (value.1, interpret key value.2)) (known output) =
      RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output) := rfl

/-- Every actual private request, including exact aliases and distinct domain labels, decodes to the interpreted selected-material route. -/
theorem step_exact (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    RawCtxInterpretedReceive.decodeResponse (RawCtxFunctionalFamily.execute
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) request) =
      ((step prior target nonce next request).1, interpret key (step prior target nonce next request).2) := by
  by_cases same : RawCtxKdfRequestTable.address request = RawCtxSelectedParentPrivatePatch.targetAddress target
  · simp only [RawCtxFunctionalFamily.execute, RawCtxSelectedParentPrivatePatch.privatePatch, step,
      if_pos same, decoded_response, interpret]
  · simp only [RawCtxFunctionalFamily.execute, RawCtxSelectedParentPrivatePatch.privatePatch, step, if_neg same]
    exact (known_exact key _).symm

/-- Retained predecessor priority and every address-collision branch agree with the actual source private lookup; no separation premise removes a collision. -/
theorem later_exact (prior : Prior) (entry : Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    RawCtxInterpretedReceive.decodeResponse (RawCtxFunctionalFamily.execute
      (lookup (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) entry target) request) =
      ((later prior entry target nonce next request).1, interpret key (later prior entry target nonce next request).2) := by
  by_cases parent : RawCtxKdfRequestTable.address request = entry.address
  · simp only [RawCtxFunctionalFamily.execute, lookup, later, if_pos parent]
    exact (known_exact key _).symm
  · simp only [RawCtxFunctionalFamily.execute, lookup, later, if_neg parent]
    exact step_exact prior key target nonce next request

/-- A predecessor retry returns the original retained full response even when its address is also the selected child address. -/
theorem later_parent (prior : Prior) (entry : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) (parent : RawCtxKdfRequestTable.address request = entry.address) :
    later prior entry target nonce next request = (concreteChain target, .known (concreteMaterial entry.material)) := by
  simp only [later, if_pos parent, known, RawCtxSelectedParentEntry.decoded_response]

/-- The exact selected private request resumes the complete original receive effect, retaining rollback state, staged skipped keys, validation and later continuation. -/
theorem receive_step {Context : Type} (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (pending : RawCtxInterpretedReceive.Kdf Slot Context) :
    RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf (interpret key) pending)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxFunctionalFamily.execute
        (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) pending.request)) =
      RawCtxInterpretedReceive.mapEffect (interpret key)
        (RawCtxInterpretedReceive.normalResume pending (step prior target nonce next pending.request)) := by
  rw [step_exact]
  exact RawCtxInterpretedReceive.normalResume_map (interpret key) pending _

/-- The later receive continuation uses the same retained predecessor and selected response even on colliding requests. -/
theorem receive_later {Context : Type} (prior : Prior) (entry : Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (pending : RawCtxInterpretedReceive.Kdf Slot Context) :
    RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf (interpret key) pending)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxFunctionalFamily.execute
        (lookup (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) entry target) pending.request)) =
      RawCtxInterpretedReceive.mapEffect (interpret key)
        (RawCtxInterpretedReceive.normalResume pending (later prior entry target nonce next pending.request)) := by
  rw [later_exact]
  exact RawCtxInterpretedReceive.normalResume_map (interpret key) pending _

/-- The actual send advancement retains all previous state and supplies only the selected or known material marker to the subsequent sealing effect. -/
theorem send_step {Context : Type} (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (pending : RawCtxInterpretedSend.Kdf Slot Context) :
    RawCtxInterpretedSend.ready (RawCtxInterpretedSend.mapKdf (interpret key) pending)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxFunctionalFamily.execute
        (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) pending.request)) =
      RawCtxInterpretedSend.mapSeal (interpret key)
        (RawCtxInterpretedSend.ready pending (step prior target nonce next pending.request)) := by
  rw [step_exact]
  exact RawCtxInterpretedSend.ready_map (interpret key) pending _

/-- The later source send preserves predecessor priority and the full original sealing continuation. -/
theorem send_later {Context : Type} (prior : Prior) (entry : Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (pending : RawCtxInterpretedSend.Kdf Slot Context) :
    RawCtxInterpretedSend.ready (RawCtxInterpretedSend.mapKdf (interpret key) pending)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxFunctionalFamily.execute
        (lookup (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) entry target) pending.request)) =
      RawCtxInterpretedSend.mapSeal (interpret key)
        (RawCtxInterpretedSend.ready pending (later prior entry target nonce next pending.request)) := by
  rw [later_exact]
  exact RawCtxInterpretedSend.ready_map (interpret key) pending _

/-- The existing private table is an explicitly counted lookup service, not a newly assumed cryptographic primitive. -/
abbrev PriorSpec : OracleSpec PqxdhJointKdf.JointKdfAddress := fun _ => FullOutput

noncomputable def priorImpl (prior : Prior) : QueryImpl PriorSpec ProbComp := fun address => pure (prior address)

noncomputable def route (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) : OracleComp PriorSpec (RatchetChain × Slot) :=
  if RawCtxKdfRequestTable.address request = RawCtxSelectedParentPrivatePatch.targetAddress target
  then pure (concreteChain next, .hidden nonce)
  else known <$> (PriorSpec.query (RawCtxKdfRequestTable.address request) : OracleComp PriorSpec FullOutput)

noncomputable def routeLater (entry : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) : OracleComp PriorSpec (RatchetChain × Slot) :=
  if RawCtxKdfRequestTable.address request = entry.address then pure (known (realize entry target))
  else route target nonce next request

/-- Interpreting the counted lookup against the original prior function gives the exact source route. -/
theorem route_exact (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    simulateQ (priorImpl prior) (route target nonce next request) =
      pure (step prior target nonce next request) := by
  simp only [route, step]
  split <;> simp only [simulateQ_pure, simulateQ_map, simulateQ_spec_query, priorImpl, map_pure]

/-- The counted later route preserves predecessor priority in the full original prior interpretation. -/
theorem routeLater_exact (prior : Prior) (entry : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    simulateQ (priorImpl prior) (routeLater entry target nonce next request) =
      pure (later prior entry target nonce next request) := by
  simp only [routeLater, later]
  split
  · rfl
  · exact route_exact prior target nonce next request

/-- A source KDF request makes at most one prior-table lookup; retained selected-address hits make none. -/
theorem route_queries (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    (route target nonce next request).IsTotalQueryBound
      (if RawCtxKdfRequestTable.address request = RawCtxSelectedParentPrivatePatch.targetAddress target then 0 else 1) := by
  simp only [route]
  split
  · trivial
  · change OracleComp.IsTotalQueryBound
      ((PriorSpec.query (RawCtxKdfRequestTable.address request) : OracleComp PriorSpec FullOutput) >>=
        fun output => pure (known output)) 1
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨by omega, fun _ => trivial⟩

/-- A retained predecessor hit and a selected child hit use zero prior lookups; every other source request uses at most one. -/
theorem routeLater_queries (entry : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    (routeLater entry target nonce next request).IsTotalQueryBound
      (if RawCtxKdfRequestTable.address request = entry.address then 0 else
        if RawCtxKdfRequestTable.address request = RawCtxSelectedParentPrivatePatch.targetAddress target then 0 else 1) := by
  simp only [routeLater]
  split
  · trivial
  · exact route_queries target nonce next request

/-- Interpreting the already retained table samples no new bytes in either route. This does not erase the source KDF call or prior lookup bills. -/
theorem uniform (prior : Prior) (entry : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    (simulateQ (priorImpl prior) (route target nonce next request)).IsTotalQueryBound 0 ∧
      (simulateQ (priorImpl prior) (routeLater entry target nonce next request)).IsTotalQueryBound 0 := by
  rw [route_exact, routeLater_exact]
  exact ⟨by trivial, by trivial⟩

end BeaconcryptCore.Computational.RawCtxSelectedMessageKdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.decoded_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.decoded_response
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.known_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.known_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.step_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.step_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.later_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.later_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.later_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.later_parent
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.receive_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.receive_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.receive_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.receive_later
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.send_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.send_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.send_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.send_later
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.route_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.route_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.routeLater_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.routeLater_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.route_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.route_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.routeLater_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.routeLater_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKdf.uniform
