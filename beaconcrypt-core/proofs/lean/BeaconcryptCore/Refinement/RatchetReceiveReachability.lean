import BeaconcryptCore.Refinement.RatchetReceiveDriver
import BeaconcryptCore.Refinement.RatchetReceiveAdmission
import BeaconcryptCore.Refinement.RatchetFutureTrace
import BeaconcryptCore.Refinement.RatchetCachedLifecycle

/-! Every receive operation terminates and preserves lifetime reachability under fixed KDF interpretation and arbitrary authentication results. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.concrete

/-- Every canonical receive has a complete extracted execution, without assuming a trace or successful helpers. -/
theorem receiveRun_exists_reachable {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (sendOrigin receiveOrigin : ratchet.RatchetChain)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (h : RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin entry) :
    ∃ next output, ReceiveRun execute openReply entry target context next output ∧
      RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin next := by
  obtain ⟨send, receive, hkernel, hsend⟩ := h
  by_cases hz : target = 0#u64
  · subst target
    exact ⟨entry, .None, ⟨_, hkernel.begin_receive_zero (withInterpreter cr execute)
      receiveOrigin send receive entry context, .rejected entry context⟩,
      send, receive, hkernel, hsend⟩
  have hpositive : 0 < target.val := by scalar_tac
  by_cases hfuture : receive.n < target.val
  · by_cases hcapacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50
    · obtain ⟨pending, opened, hbegin, htrace, hopen⟩ :=
        hkernel.begin_receive_future_trace cr execute receiveOrigin send receive entry context target hfuture hcapacity
      cases hreply : openReply opened with
      | none =>
          have hentry : opened.entry = entry := by obtain ⟨_, he, _, _, _⟩ := hopen; exact he
          have hfinish : opened.finish (openReply opened) = ok (entry, core.option.Option.None) := by
            simp only [hreply, ReceiveOpen.finish, hentry]
          exact ⟨entry, .None, ⟨_, hbegin, htrace.complete (.opened opened entry .None hfinish)⟩,
            send, receive, hkernel, hsend⟩
      | some plaintext =>
          obtain ⟨published, hfinish, hpublication⟩ :=
            hopen.finish_some (withInterpreter cr execute) receiveOrigin send receive entry context target opened plaintext
          exact ⟨{ refined := published }, .Some plaintext,
            ⟨_, hbegin, htrace.complete (.opened opened _ _ (by simpa only [hreply] using hfinish))⟩,
            send, _, hpublication, hsend⟩
    · exact ⟨entry, .None,
        ⟨_, hkernel.begin_receive_capacity_rejected (withInterpreter cr execute) receiveOrigin send receive
          entry target context hfuture (by omega), .rejected entry context⟩,
        send, receive, hkernel, hsend⟩
  · cases hlookup : List.lookup (target.val - 1) receive.skipped with
    | none =>
        exact ⟨entry, .None,
          ⟨_, hkernel.begin_receive_replay (withInterpreter cr execute) receiveOrigin send receive entry target context
            (by omega) hpositive hlookup, .rejected entry context⟩,
          send, receive, hkernel, hsend⟩
    | some material =>
        obtain ⟨opened, hbegin, hopen⟩ := begin_receive_cached_refines (withInterpreter cr execute)
          receiveOrigin send receive entry context target (target.val - 1) material hkernel (by omega) hlookup
        obtain ⟨next, hfinish, hnext⟩ := hopen.finish_preserves_reachability (withInterpreter cr execute)
          sendOrigin receiveOrigin send receive (target.val - 1) material opened hsend (openReply opened)
        exact ⟨next, openReply opened, ⟨_, hbegin, .opened opened next _ hfinish⟩, hnext⟩

/-- Every complete execution from a canonical role preserves reachability, including arbitrary optional callback results. -/
theorem ReceiveRun.preserves_reachability {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (sendOrigin receiveOrigin : ratchet.RatchetChain)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (h : RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin entry)
    (next : ConcreteRatchetKernel) (output : core.option.Option Output)
    (run : ReceiveRun execute openReply entry target context next output) :
    RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin next := by
  obtain ⟨other, otherOutput, otherRun, hother⟩ := receiveRun_exists_reachable cr execute
    sendOrigin receiveOrigin entry target context openReply h
  exact (run.deterministic otherRun).1.symm ▸ hother

/-- The unbounded synchronous receive driver terminates and preserves the role relation for every canonical input. -/
theorem receiveNext_preserves_reachability {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (sendOrigin receiveOrigin : ratchet.RatchetChain)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (h : RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin entry) :
    ∃ next output, receiveNext execute entry target context openReply = ok (next, output) ∧
      RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin next := by
  obtain ⟨next, output, run, hnext⟩ := receiveRun_exists_reachable cr execute sendOrigin receiveOrigin
    entry target context openReply h
  exact ⟨next, output, run.driver_eq, hnext⟩

end beaconcrypt_core.ratchet.concrete
