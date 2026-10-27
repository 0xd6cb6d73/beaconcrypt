-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend

/-! Exact dictionary and writer-log retention by non-record environment callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginBuffers PqxdhRecordFactsOriginSend
open PqxdhRecordLiftWorldCompiler (Label StoredKernel)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Exact fields read by dictionary attribution and the source publication boundary. -/
structure Kept (before after : CtxPrivate n) : Prop where
  keys : after.keys = before.keys
  produced : after.base.produced = before.base.produced
  pending : after.base.pending = before.base.pending

/-- Reflexivity of the retained attribution fields. -/
theorem Kept.refl (state : CtxPrivate n) : Kept state state := ⟨rfl, rfl, rfl⟩

/-- Source continuations compose retention at their actual intervening state. -/
theorem Kept.trans (before middle after : CtxPrivate n) (first : Kept before middle)
    (second : Kept middle after) : Kept before after :=
  ⟨second.keys.trans first.keys, second.produced.trans first.produced, second.pending.trans first.pending⟩

/-- Allocation consumes the real sampler and retains all record dictionaries and writer logs. -/
theorem allocate_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : PqxdhRecordLiftInterface.Slot n)
    (before : CtxPrivate n) (result : Unit × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.allocate slot)).run before)) :
    Kept before result.2 := by
  simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.sampled, StateT.run, bind_pure_comp, Functor.map_map,
    support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ⟨rfl, rfl, rfl⟩

/-- Exactly the private services available to non-record environment effects. -/
def Environmental : PqxdhRecordLiftProtocol.Service n → Prop
  | .allocate _ | .coin _ | .hash _ | .charge _ => True
  | _ => False

/-- Every actual environment service preserves the full coordinate states and both writer logs; coins and hashes still execute with their source counters and cache. -/
theorem environmental_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (environmental : Environmental query)
    (before : CtxPrivate n) (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec query).run before)) :
    Kept before result.2 := by
  cases query
  all_goals first | exact False.elim environmental | skip
  case allocate slot => exact allocate_kept modes replace setup codec slot before result supported
  case charge kind =>
    simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter, StateT.run,
      map_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨rfl, rfl, rfl⟩
  all_goals
    simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
      PqxdhRecordLiftProtocol.sampled, StateT.run, bind_pure_comp, Functor.map_map,
      support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact ⟨rfl, rfl, rfl⟩

/-- Resolving a role and known or hidden kernel reference preserves attribution fields and does not seal a record. -/
theorem resolve_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (role : PqxdhRecordLiftInterface.Role)
    (ref : PqxdhRecordLiftInterface.KernelRef n) (before : CtxPrivate n) (result : StoredKernel n × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.resolve role ref)).run before)) : Kept before result.2 := by
  cases ref with
  | known kernel =>
    simp only [PqxdhRecordLiftProtocol.resolve, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Kept.refl before
  | hidden slot =>
    simp only [PqxdhRecordLiftProtocol.resolve, bind_pure_comp, simulateQ_map,
      simulateQ_spec_query, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact allocate_kept modes replace setup codec slot before inner reached

/-- Actual Server installation preserves record dictionaries and logs through its vacant-peer and one-use admission checks. -/
theorem installServer_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : PqxdhRecordLiftInterface.KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (before : CtxPrivate n)
    (result : (Bool × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.installServer keyId identity ref control)).run before)) :
    Kept before result.2 := by
  simp only [PqxdhRecordLiftProtocol.installServer] at supported
  repeat' split at supported
  case h_2.isTrue =>
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact resolve_kept modes replace setup codec .server ref before inner reached
  all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  all_goals subst result
  all_goals exact Kept.refl before

/-- Actual Beacon installation preserves attribution fields through its init-sent and one-use admission checks. -/
theorem installBeacon_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (owner : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell) (ref : PqxdhRecordLiftInterface.KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (before : CtxPrivate n)
    (result : (Bool × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.installBeacon owner shell ref control)).run before)) :
    Kept before result.2 := by
  simp only [PqxdhRecordLiftProtocol.installBeacon] at supported
  split at supported
  · simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact resolve_kept modes replace setup codec .beacon ref before inner reached
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Kept.refl before

/-- Lifting an environment service into the actual control client preserves its reply and attribution fields. -/
theorem lift_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (environmental : Environmental query)
    (control : PqxdhRecordLiftProtocol.Control n) (before : CtxPrivate n)
    (result : ((PqxdhRecordLiftProtocol.ServiceSpec n).Range query × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      ((StateT.lift ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) : PqxdhRecordLiftProtocol.Client n _).run control)).run before)) :
    Kept before result.2 := by
  change result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
    ((fun reply => (reply, control)) <$> ((PqxdhRecordLiftProtocol.ServiceSpec n).query query :
      OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _))).run before) at supported
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact environmental_kept modes replace setup codec query environmental before inner reached

/-- Every frozen environment capability preserves all record dictionaries and writer logs. -/
theorem capability_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (PqxdhRecordLiftInterface.CapabilitySpec n).Domain)
    (control : PqxdhRecordLiftProtocol.Control n) (before : CtxPrivate n)
    (result : ((PqxdhRecordLiftInterface.CapabilitySpec n).Range query × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.capability query control)).run before)) : Kept before result.2 := by
  cases query
  case installServer keyId identity ref =>
    exact installServer_kept modes replace setup codec keyId identity ref control before result supported
  case installBeacon owner shell ref =>
    exact installBeacon_kept modes replace setup codec owner shell ref control before result supported
  case hash bytes =>
    exact lift_kept modes replace setup codec (.hash bytes) trivial control before result supported
  case advanceOwner owner phase =>
    simp only [PqxdhRecordLiftProtocol.capability] at supported
    repeat' split at supported
    all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    all_goals subst result
    all_goals exact Kept.refl before
  all_goals simp only [PqxdhRecordLiftProtocol.capability, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at supported
  all_goals subst result
  all_goals exact Kept.refl before

/-- Charging and dispatching every actual environment effect preserve record attribution fields. -/
theorem effects_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (control : PqxdhRecordLiftProtocol.Control n) (before : CtxPrivate n)
    (result : ((PqxdhRecordLiftInterface.EnvEffects n).Range query × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      ((PqxdhRecordLiftProtocol.effects query).run control)).run before)) : Kept before result.2 := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at supported
  obtain ⟨charged, reached, continued⟩ := supported
  have kept := lift_kept modes replace setup codec (.charge (PqxdhRecordLiftInterface.effectKind query))
    trivial control before charged reached
  apply Kept.trans before charged.2 result.2 kept
  cases query with
  | inl coin => exact lift_kept modes replace setup codec (.coin coin) trivial charged.1.2 charged.2 result continued
  | inr capability => exact capability_kept modes replace setup codec capability charged.1.2 charged.2 result continued

/-- Installing the constructed Server changes source control only and retains all attribution fields. -/
theorem initialize_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (control : PqxdhRecordLiftProtocol.Control n) (before : CtxPrivate n)
    (result : (Unit × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.initializeServer created control)).run before)) : Kept before result.2 := by
  cases existing : control.server <;>
    simp only [PqxdhRecordLiftProtocol.initializeServer, existing, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported <;>
    subst result <;> exact Kept.refl before

/-- Retained dictionary and produced-log fields retain every attributed frame witness. -/
theorem Kept.closed (before after : CtxPrivate n) (kept : Kept before after)
    (claims : Label n → PqxdhDeploymentInterface.FrameTag → Prop) (closed : Closed claims before) :
    Closed claims after := by
  intro label entry member
  rw [kept.keys] at member
  simpa only [kept.produced] using closed label entry member

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient


/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.Kept.refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.Kept.refl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.Kept.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.Kept.trans

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.allocate_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.allocate_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.environmental_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.environmental_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.resolve_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.resolve_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.installServer_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.installServer_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.installBeacon_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.installBeacon_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.lift_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.lift_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.capability_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.capability_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.effects_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.effects_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.initialize_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.initialize_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.Kept.closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient.Kept.closed
