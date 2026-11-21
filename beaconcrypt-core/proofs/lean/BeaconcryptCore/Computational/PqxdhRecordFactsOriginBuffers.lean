-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices

/-! Dictionary provenance through the source's literal pending and tagged writer logs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginServices
open PqxdhDeploymentInterface (FrameTag)
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Every dictionary entry is represented by a frame already attributed in the produced log. -/
def Closed (claims : Label n → FrameTag → Prop) (secret : CtxPrivate n) : Prop :=
  ∀ label entry, entry ∈ (secret.keys label).1.successfulSeals →
    ∃ tag frame, claims label tag ∧ (tag, frame) ∈ secret.base.produced ∧ Matches frame entry

/-- During one owner operation, a new dictionary entry may still be in that owner's literal writer buffer. -/
def Buffered (claims : Label n → FrameTag → Prop) (tag : FrameTag) (secret : CtxPrivate n) : Prop :=
  ∀ label entry, entry ∈ (secret.keys label).1.successfulSeals →
    ∃ frame, Matches frame entry ∧
      ((frame ∈ secret.base.pending ∧ claims label tag) ∨
        ∃ prior, claims label prior ∧ (prior, frame) ∈ secret.base.produced)

/-- A closed dictionary is represented during any subsequent owner operation. -/
theorem closed_buffered (claims : Label n → FrameTag → Prop) (tag : FrameTag)
    (secret : CtxPrivate n) (closed : Closed claims secret) : Buffered claims tag secret := by
  intro label entry member
  obtain ⟨prior, frame, claimed, produced, matched⟩ := closed label entry member
  exact ⟨frame, matched, Or.inr ⟨prior, claimed, produced⟩⟩

/-- Empty pending logs leave only attributed produced frames. -/
theorem buffered_closed (claims : Label n → FrameTag → Prop) (tag : FrameTag)
    (secret : CtxPrivate n) (buffered : Buffered claims tag secret) (empty : secret.base.pending = []) :
    Closed claims secret := by
  intro label entry member
  obtain ⟨frame, matched, pending | ⟨prior, claimed, produced⟩⟩ := buffered label entry member
  · exact False.elim (List.not_mem_nil (empty ▸ pending.1))
  · exact ⟨prior, frame, claimed, produced, matched⟩

/-- The literal publication operation converts pending source frames to tagged produced frames, regardless of writer success. -/
theorem publish_closed (claims : Label n → FrameTag → Prop) (tag : FrameTag)
    (secret : CtxPrivate n) (buffered : Buffered claims tag secret) :
    Closed claims { secret with base := PqxdhRecordLiftProtocol.publish tag secret.base } := by
  intro label entry member
  obtain ⟨frame, matched, pending | ⟨prior, claimed, produced⟩⟩ := buffered label entry member
  · refine ⟨tag, frame, pending.2, ?_, matched⟩
    exact List.mem_append_right _ (List.mem_map.mpr ⟨frame, pending.1, rfl⟩)
  · exact ⟨prior, frame, claimed, List.mem_append_left _ produced, matched⟩

/-- Only the dictionary and the two writer logs are read by buffered provenance. -/
theorem buffered_preserved (claims : Label n → FrameTag → Prop) (tag : FrameTag)
    (before after : CtxPrivate n) (buffered : Buffered claims tag before)
    (keys : ∀ label, (after.keys label).1.successfulSeals = (before.keys label).1.successfulSeals)
    (produced : after.base.produced = before.base.produced) (pending : after.base.pending = before.base.pending) :
    Buffered claims tag after := by
  intro label entry member
  rw [keys label] at member
  simpa only [produced, pending] using buffered label entry member

/-- Expanding the set of established handle claims retains every prior attributed dictionary entry. -/
theorem closed_claims_mono (before after : Label n → FrameTag → Prop)
    (mono : ∀ label tag, before label tag → after label tag)
    (secret : CtxPrivate n) (closed : Closed before secret) : Closed after secret := by
  intro label entry member
  obtain ⟨tag, frame, claimed, produced, matched⟩ := closed label entry member
  exact ⟨tag, frame, mono label tag claimed, produced, matched⟩

/-- Initial coordinate dictionaries contain no seal entries. -/
theorem initial_closed (claims : Label n → FrameTag → Prop) : Closed claims CtxPrivate.initial := by
  intro label entry member
  exact False.elim (List.not_mem_nil member)

/-- The actual CTX publication callback moves exactly the literal source pending log. -/
theorem publish_callback (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (tag : FrameTag) (secret : CtxPrivate n) :
    (ctxInterpreter modes replace setup codec (.publish tag)).run secret =
      pure ((), { secret with base := PqxdhRecordLiftProtocol.publish tag secret.base }) := by
  simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter, StateT.run, map_pure]

/-- Actual publication closes buffered provenance and leaves the literal pending log empty. -/
theorem publish_buffered_closed (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (claims : Label n → FrameTag → Prop) (tag : FrameTag)
    (before : CtxPrivate n) (buffered : Buffered claims tag before) (result : Unit × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.publish tag)).run before)) :
    Closed claims result.2 ∧ result.2.base.pending = [] := by
  rw [publish_callback, support_pure, Set.mem_singleton_iff] at supported
  subst result
  exact ⟨publish_closed claims tag before buffered, rfl⟩

/-- The exact hidden sealing service extends the current owner's buffered provenance, also when its writer returns failure. -/
theorem sealing_buffered (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (claims : Label n → FrameTag → Prop) (tag : FrameTag)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (claimed : claims pending.material tag)
    (before : CtxPrivate n) (buffered : Buffered claims tag before)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.sealing pending)).run before)) :
    Buffered claims tag result.2 := by
  obtain ⟨produced, unchanged | ⟨width, record, inserted, logged, reply⟩⟩ :=
    sealing_trace modes ideal replace setup codec pending before result supported
  · intro label entry member
    rw [unchanged.2.2 label] at member
    simpa only [Buffered, unchanged.2.1, produced] using buffered label entry member
  · have carry (label : Label n) (entry : CtxSuccessfulSeal)
        (member : entry ∈ (before.keys label).1.successfulSeals) :
        ∃ frame, Matches frame entry ∧
          ((frame ∈ result.2.base.pending ∧ claims label tag) ∨
            ∃ prior, claims label prior ∧ (prior, frame) ∈ result.2.base.produced) := by
      obtain ⟨frame, matched, oldPending | oldProduced⟩ := buffered label entry member
      · exact ⟨frame, matched, Or.inl ⟨logged ▸ List.mem_append_left _ oldPending.1, oldPending.2⟩⟩
      · exact ⟨frame, matched, Or.inr (produced ▸ oldProduced)⟩
    intro label entry member
    by_cases same : label = pending.material
    · subst label
      rw [inserted, List.mem_cons] at member
      rcases member with rfl | prior
      · refine ⟨⟨pending.sequence, pending.context.senderId, record.encode⟩, ?_, Or.inl ⟨?_, claimed⟩⟩
        · exact ⟨rfl, rfl, rfl⟩
        · rw [logged]
          exact List.mem_append_right _ (List.mem_cons_self ..)
      · exact carry pending.material entry prior
    · apply carry label entry
      rwa [PqxdhRecordLiftCtxHybrid.sealing_other modes replace setup codec pending before result supported label same] at member

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers


/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.closed_buffered' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.closed_buffered

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.buffered_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.buffered_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.publish_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.publish_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.buffered_preserved' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.buffered_preserved

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.closed_claims_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.closed_claims_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.initial_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.initial_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.publish_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.publish_callback

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.publish_buffered_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.publish_buffered_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.sealing_buffered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers.sealing_buffered
