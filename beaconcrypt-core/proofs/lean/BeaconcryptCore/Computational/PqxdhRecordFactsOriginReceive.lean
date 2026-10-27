-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles

/-! Exact hidden source receive history in the ideal record interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordLiftWorldCompiler PqxdhRecordLiftWorldProvenance
open PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginDictionary PqxdhRecordFactsOriginServices
open PqxdhRecordLiftCtxLink PqxdhRecordLiftCtxAvailability
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- A source lookup retains all keyed state and both writer logs while updating its actual chain table and counters. -/
theorem lookup_preserves (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (coordinate : Label n)
    (before : CtxPrivate n) (result : Unit × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.lookup coordinate)).run before)) :
    result.2.keys = before.keys ∧ result.2.base.produced = before.base.produced ∧
      result.2.base.pending = before.base.pending ∧ result.2.base.seeds = before.base.seeds := by
  rw [show ctxInterpreter modes replace setup codec (.lookup coordinate) =
    ctxInterpreterWith tableKey modes replace setup codec (.lookup coordinate) from rfl,
    lookup_factor, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every keyed CTX request retains the source production log, writer buffer and sampled seed map. -/
theorem keyed_logs (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (before : CtxPrivate n)
    (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((keyed modes decode crypto query).run before)) :
    result.2.base.produced = before.base.produced ∧ result.2.base.pending = before.base.pending ∧
      result.2.base.seeds = before.base.seeds := by
  obtain ⟨_, _, _, _, seeds, produced, pending⟩ := keyed_witness modes decode crypto query before result supported
  exact ⟨produced, pending, seeds⟩

/-- The whole hidden opening service retains the production log, writer buffer and seeds across every parser and verification outcome. -/
theorem opening_logs (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (pending : PqxdhRecordLiftProtocol.Opening n)
    (before : CtxPrivate n) (result : core.option.Option RawCtxWholeOwner.Decrypted × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.opening pending)).run before)) :
    result.2.base.produced = before.base.produced ∧ result.2.base.pending = before.base.pending ∧
      result.2.base.seeds = before.base.seeds := by
  refine PqxdhRecordLiftFlat.support_keep_oracle
    (keyed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
    (fun state : CtxPrivate n => state.base.produced = before.base.produced ∧
      state.base.pending = before.base.pending ∧ state.base.seeds = before.base.seeds)
    ?_ _ before ⟨rfl, rfl, rfl⟩ result supported
  intro query state kept next reached
  obtain ⟨produced, pending, seeds⟩ := keyed_logs modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto query state next reached
  exact ⟨produced.trans kept.1, pending.trans kept.2.1, seeds.trans kept.2.2⟩

/-- Fields that a receive leaves unchanged. Every other private field stays in the actual supported poststate. -/
structure Retained (before after : CtxPrivate n) : Prop where
  seals : ∀ label, (after.keys label).1.successfulSeals = (before.keys label).1.successfulSeals
  produced : after.base.produced = before.base.produced
  pending : after.base.pending = before.base.pending
  seeds : after.base.seeds = before.base.seeds

/-- Literal reflexivity of the retained fields. -/
theorem Retained.refl (state : CtxPrivate n) : Retained state state := by
  exact ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-- Concrete field equalities compose across the actual intervening state. -/
theorem Retained.trans (first middle last : CtxPrivate n)
    (left : Retained first middle) (right : Retained middle last) : Retained first last := by
  exact ⟨fun label => (right.seals label).trans (left.seals label), right.produced.trans left.produced,
    right.pending.trans left.pending, right.seeds.trans left.seeds⟩

/-- Interpret the literal opaque recursive receive through the same global CTX service as the protocol. -/
noncomputable def receiveRun (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext)
    (state : CtxPrivate n) : ProbComp ((LabeledKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n) :=
  (simulateQ (ctxInterpreter modes replace setup codec)
    (simulateQ PqxdhRecordLiftProtocol.localLift (PqxdhRecordLiftOpaqueDrivers.receiveProgram effect))).run state

/-- Every source receive outcome retains all seal dictionaries and both writer logs, including rejection and failed-opening rollback. -/
theorem receive_retained (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext)
    (before : CtxPrivate n)
    (result : (LabeledKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support (receiveRun modes replace setup codec effect before)) :
    Retained before result.2 := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect before result with
  | h depth ih =>
      cases effect with
      | rejected entry context =>
          simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          exact supported ▸ Retained.refl before
      | openRequested pending =>
          simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, bind_pure_comp,
            simulateQ_map, simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift,
            StateT.run_map, support_map] at supported
          obtain ⟨opened, reached, rfl⟩ := supported
          have kept := opening_logs modes replace setup codec pending before opened reached
          exact ⟨opening_seals modes ideal replace setup codec pending before opened reached,
            kept.1, kept.2.1, kept.2.2⟩
      | kdfRequested pending =>
          simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind,
            simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift, StateT.run_bind,
            mem_support_bind_iff] at supported
          obtain ⟨looked, reached, continued⟩ := supported
          have kept := lookup_preserves modes replace setup codec pending.request before looked reached
          exact Retained.trans before looked.2 result.2
            ⟨fun label => congrArg (fun keys => (keys label).1.successfulSeals) kept.1,
              kept.2.1, kept.2.2.1, kept.2.2.2⟩
            (ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending
              (PqxdhRecordLiftChainState.advance pending.request 1, pending.request)) _ looked.2 result continued rfl)

/-- Source commitment or rollback returns exactly the optional plaintext supplied by the opening service. -/
theorem finish_reply (pending : PqxdhRecordLiftProtocol.Opening n)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    (RawCtxChainReceive.normalFinish pending reply).2 = reply := by
  have executed := RawCtxChainReceive.normalFinish_exact pending reply
  generalize RawCtxChainReceive.normalFinish pending reply = result at executed ⊢
  cases reply with
  | none => exact congrArg Prod.snd (RustM.ok.inj executed).symm
  | some plaintext =>
      cases shape : pending.prepared <;> simp only [RawCtxInterpretedOpening.finish, shape] at executed
      all_goals obtain ⟨published, _, equal⟩ := PqxdhFirstRecordReplay.rust_bind_ok executed
      all_goals exact congrArg Prod.snd (RustM.ok.inj equal).symm

/-- A returned plaintext has an exact earlier seal at the source receive coordinate's slot and direction. -/
def ReceiveOrigin (codec : PqxdhServerAuthExperiment.Codec Reader Response) (anchor : Label n)
    (context : RawCtxWholeOwner.OpenContext) (before : CtxPrivate n) (opened : RawCtxWholeOwner.Decrypted) : Prop :=
  ∃ label, label.slot = anchor.slot ∧ label.direction = anchor.direction ∧
    ∃ frame, codec.frameRead context.raw = some frame ∧
      ∃ entry ∈ (before.keys label).1.successfulSeals, Matches frame entry ∧ entry.input.plaintext = opened.plaintext

/-- Successful recursive source receive preserves getter attribution through every skipped-key callback and returns an earlier exact seal witness. -/
theorem receive_origin (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (entry : LabeledKernel n)
    (context : RawCtxWholeOwner.OpenContext) (target : Std.U64)
    (aligned : PqxdhRecordLiftChainState.Aligned entry)
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext)
    (tracked : PqxdhRecordLiftChainState.Tracked entry context effect)
    (admitted : PqxdhFirstRecordReplay.Admitted entry target effect)
    (attributed : PqxdhRecordLiftMaterialTable.EffectAttributed entry.receive_chain effect)
    (before : CtxPrivate n)
    (result : (LabeledKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support (receiveRun modes replace setup codec effect before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    ReceiveOrigin codec entry.receive_chain context before opened := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect before result with
  | h depth ih =>
      cases effect with
      | rejected original prior =>
          simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          simp only [supported, reduceCtorEq] at accepted
      | openRequested pending =>
          simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, bind_pure_comp,
            simulateQ_map, simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift,
            StateT.run_map, support_map] at supported
          obtain ⟨reply, reached, rfl⟩ := supported
          have serviceAccepted : reply.1 = .Some opened := (finish_reply pending reply.1).symm.trans accepted
          obtain ⟨label, material, frame, decoded, sealedEntry, member, matched, plaintext⟩ :=
            opening_frame modes ideal replace setup codec pending before reply.2 opened
              (by simpa only [← serviceAccepted, Prod.mk.eta] using reached)
          obtain ⟨sequence, _, origin⟩ := PqxdhRecordLiftMaterialTable.opening_attributed
            entry.receive_chain pending attributed label material
          exact ⟨label, origin.1, origin.2.1, frame, by simpa only [tracked.2.1] using decoded,
            sealedEntry, member, matched, plaintext⟩
      | kdfRequested pending =>
          simp only [receiveRun, PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind,
            simulateQ_spec_query, PqxdhRecordLiftProtocol.localLift, StateT.run_bind,
            mem_support_bind_iff] at supported
          obtain ⟨looked, reached, continued⟩ := supported
          have nextOrigin := ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending
            (PqxdhRecordLiftChainState.advance pending.request 1, pending.request)) _
            (PqxdhRecordLiftChainState.resume_tracked entry context pending pending.request tracked)
            (PqxdhFirstRecordReplay.resume_admitted entry target pending
              (PqxdhRecordLiftChainState.advance pending.request 1, pending.request) admitted)
            (PqxdhRecordLiftMaterialTable.resume_source_attributed entry context target pending aligned tracked admitted
              attributed.1 attributed.2) looked.2 result continued accepted rfl
          simpa only [ReceiveOrigin, (lookup_preserves modes replace setup codec pending.request before looked reached).1]
            using nextOrigin

/-- The source admission operation supplies every callback provenance premise from the existing kernel certificate. -/
theorem admitted_origin (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (entry : LabeledKernel n)
    (context : RawCtxWholeOwner.OpenContext) (target : Std.U64)
    (certified : PqxdhRecordLiftChainCoordinates.Certified entry) (before : CtxPrivate n)
    (result : (LabeledKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support (receiveRun modes replace setup codec
      (RawCtxChainReceive.normalBegin entry target context) before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    ReceiveOrigin codec entry.receive_chain context before opened := by
  exact receive_origin modes ideal replace setup codec entry context target certified.2.1 _
    (PqxdhRecordLiftChainState.begin_tracked entry context target)
    (PqxdhFirstRecordReplay.begin_admitted entry target context certified.1.capacity)
    (PqxdhRecordLiftMaterialTable.begin_attributed entry.receive_chain entry certified.2.2 target context)
    before result supported opened accepted

/-- A successful actual hidden kernel receive returns a matching pre-existing CTX seal at the installed slot and opposite physical direction, retaining all seal histories and writer logs. -/
theorem kernel_receive_origin (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (role : PqxdhRecordLiftInterface.Role)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : LabeledKernel n)
    (oriented : Oriented role (.hidden slot entry)) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (before : CtxPrivate n)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelReceive (.hidden slot entry) target context)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (accepted : result.1.2 = .Some opened) :
    Retained before result.2 ∧ ∃ label, label.slot = slot ∧ label.direction = !sendDirection role ∧
      ∃ frame, codec.frameRead context.raw = some frame ∧
        ∃ old ∈ (before.keys label).1.successfulSeals, Matches frame old ∧ old.input.plaintext = opened.plaintext := by
  simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
    StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  refine ⟨receive_retained modes ideal replace setup codec _ before inner reached, ?_⟩
  obtain ⟨label, origin, direction, rest⟩ := admitted_origin modes ideal replace setup codec entry context target
    oriented.1 before inner reached opened accepted
  exact ⟨label, origin.trans oriented.2.1.2, direction.trans oriented.2.2.2, rest⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.lookup_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.lookup_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.keyed_logs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.keyed_logs

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.opening_logs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.opening_logs

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.Retained.refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.Retained.refl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.Retained.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.Retained.trans

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.receive_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.receive_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.finish_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.finish_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.receive_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.receive_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.admitted_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.admitted_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.kernel_receive_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive.kernel_receive_origin
