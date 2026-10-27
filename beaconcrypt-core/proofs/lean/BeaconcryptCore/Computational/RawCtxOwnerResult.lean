import BeaconcryptCore.Computational.RawCtxReceive

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxOwnerResult

/-- Change only the successful public result; rejection remains rejection. -/
def mapReply {Plaintext Result : Type} (f : Plaintext → Result) :
    core.option.Option Plaintext → core.option.Option Result
  | .None => .None
  | .Some plaintext => .Some (f plaintext)

/-- Wrapping the actual plaintext before publication preserves every source publication outcome. -/
theorem finish_map {Context Plaintext Result : Type}
    (opened : ReceiveOpen Context) (reply : core.option.Option Plaintext)
    (f : Plaintext → Result) :
    opened.finish (mapReply f reply) = (do
      let result ← opened.finish reply
      ok (result.1, mapReply f result.2)) := by
  cases reply with
  | none => simp [ReceiveOpen.finish, mapReply]
  | some plaintext =>
    cases h : opened.prepared <;>
      simp [ReceiveOpen.finish, mapReply, h, bind_assoc]

/-- Successful-result wrapping leaves the same extracted KDF path and final kernel. -/
theorem execution_map {Context Plaintext Result : Type}
    (execute : KdfInterpreter)
    (openReply : ReceiveOpen Context → core.option.Option Plaintext)
    (f : Plaintext → Result) (effect : ReceiveEffect Context)
    (kernel : ConcreteRatchetKernel) (reply : core.option.Option Plaintext)
    (run : ReceiveExecution execute openReply effect kernel reply) :
    ReceiveExecution execute (fun pending => mapReply f (openReply pending))
      effect kernel (mapReply f reply) := by
  induction run with
  | rejected entry context => exact .rejected entry context
  | resume pending next result opened hresume tail ih =>
      exact .resume pending next result (mapReply f opened) hresume ih
  | opened pending result opened hfinish =>
      apply ReceiveExecution.opened
      simp [finish_map, hfinish]

/-- The actual total receive driver can wrap its true optional result at either boundary. -/
theorem receiveNext_map {Context Plaintext Result : Type}
    (execute : KdfInterpreter)
    (openReply : ReceiveOpen Context → core.option.Option Plaintext)
    (f : Plaintext → Result) (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    receiveNext execute entry target context
      (fun pending => mapReply f (openReply pending)) = (do
        let result ← receiveNext execute entry target context openReply
        ok (result.1, mapReply f result.2)) := by
  obtain ⟨kernel, reply, run⟩ := receiveRun_exists execute entry target context openReply
  have mapped : ReceiveRun execute (fun pending => mapReply f (openReply pending))
      entry target context kernel (mapReply f reply) := by
    obtain ⟨effect, hbegin, execution⟩ := run
    exact ⟨effect, hbegin, execution_map execute openReply f effect kernel reply execution⟩
  rw [run.driver_eq, mapped.driver_eq]
  rfl

end BeaconcryptCore.Computational.RawCtxOwnerResult

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerResult.finish_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerResult.finish_map

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerResult.execution_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerResult.execution_map

/--
info: 'BeaconcryptCore.Computational.RawCtxOwnerResult.receiveNext_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerResult.receiveNext_map
