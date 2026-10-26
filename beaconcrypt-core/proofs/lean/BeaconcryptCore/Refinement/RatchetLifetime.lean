import BeaconcryptCore.Refinement.RatchetReceiveReachability

/-! Arbitrary finite send/receive histories preserve the canonical lifetime invariant. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- One complete operation with its arbitrary optional primitive result interpreter. -/
inductive RoleAction (Context Output : Type) where
  | send (context : Context)
      (sealReply : ratchet.RatchetMaterial → Std.U64 → Context → core.option.Option Output)
  | receive (target : Std.U64) (context : Context)
      (openReply : ReceiveOpen Context → core.option.Option Output)

/-- Execute one action by sequencing the extracted phases. -/
def RoleAction.execute {Context Output : Type} (action : RoleAction Context Output)
    (interpret : KdfInterpreter) (entry : ConcreteRatchetKernel) :
    RustM (ConcreteRatchetKernel × core.option.Option Output) :=
  match action with
  | .send context sealReply => sealNext interpret entry context sealReply
  | .receive target context openReply => receiveNext interpret entry target context openReply

/-- Execute a finite mixed history; all state transitions are the actual phase drivers. -/
def executeHistory {Context Output : Type} (interpret : KdfInterpreter)
    (entry : ConcreteRatchetKernel) : List (RoleAction Context Output) →
    RustM (ConcreteRatchetKernel × List (core.option.Option Output))
  | [] => ok (entry, [])
  | action :: actions => do
      let (next, output) ← action.execute interpret entry
      let (finalState, outputs) ← executeHistory interpret next actions
      ok (finalState, output :: outputs)

/-- Every finite mixed history terminates and retains canonical chain and material provenance. -/
theorem executeHistory_preserves_reachability {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (interpret : KdfInterpreter) (sendOrigin receiveOrigin : ratchet.RatchetChain)
    (actions : List (RoleAction Context Output)) :
    ∀ entry, RoleReachable (withInterpreter cr interpret) sendOrigin receiveOrigin entry →
      ∃ finalState outputs, executeHistory interpret entry actions = ok (finalState, outputs) ∧
        outputs.length = actions.length ∧
        RoleReachable (withInterpreter cr interpret) sendOrigin receiveOrigin finalState := by
  induction actions with
  | nil => intro entry h; exact ⟨entry, [], rfl, rfl, h⟩
  | cons action actions ih =>
      intro entry h
      have hstep : ∃ next output, action.execute interpret entry = ok (next, output) ∧
          RoleReachable (withInterpreter cr interpret) sendOrigin receiveOrigin next := by
        cases action with
        | send context sealReply =>
            exact sealNext_preserves_reachability cr interpret sendOrigin receiveOrigin entry h context sealReply
        | receive target context openReply =>
            exact receiveNext_preserves_reachability cr interpret sendOrigin receiveOrigin entry target context openReply h
      obtain ⟨next, output, hrun, hnext⟩ := hstep
      obtain ⟨finalState, outputs, htail, hlength, hfinal⟩ := ih next hnext
      exact ⟨finalState, output :: outputs, by simp! only [executeHistory, hrun, bind_tc_ok, htail],
        by simp only [List.length_cons, hlength], hfinal⟩

end beaconcrypt_core.ratchet.concrete
