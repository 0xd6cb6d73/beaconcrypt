-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient

/-! The actual adaptive source world establishes dictionary origin from initialization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginBuffers PqxdhRecordFactsOriginSend
open PqxdhRecordFactsOriginWorld PqxdhRecordFactsOriginAmbient
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface
variable {n : Nat} {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

/-- Source control safety, actual dictionary-frame attribution and an empty writer buffer at command boundaries. -/
def Invariant (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) : Prop :=
  PqxdhRecordLiftProtocolHistory.Safe control ∧ Closed (Claims control) secret ∧ secret.base.pending = []

/-- Every actual source dispatcher request preserves the origin invariant, including all environment effects. -/
theorem handler_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) (before : CtxPrivate n)
    (invariant : Invariant control before)
    (result : ((WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      ((PqxdhRecordLiftProtocol.handler codec.frameRead route query).run control)).run before)) :
    Invariant result.1.2 result.2 := by
  have progress := PqxdhRecordLiftProtocolHistory.handler codec.frameRead route query control invariant.1 result.1
    (PqxdhRecordLiftFlat.support_run_fst (ctxInterpreter modes replace setup codec) _ before result supported)
  refine ⟨progress.1, ?_⟩
  cases query with
  | inl created =>
    have kept := initialize_kept modes replace setup codec created control before result supported
    exact ⟨closed_claims_mono (Claims control) (Claims result.1.2) (claims_step control result.1.2 progress)
      result.2 (kept.closed before result.2 (Claims control) invariant.2.1), kept.pending.trans invariant.2.2⟩
  | inr outer =>
    cases outer with
    | inl effect =>
      have kept := effects_kept modes replace setup codec effect control before result supported
      exact ⟨closed_claims_mono (Claims control) (Claims result.1.2) (claims_step control result.1.2 progress)
        result.2 (kept.closed before result.2 (Claims control) invariant.2.1), kept.pending.trans invariant.2.2⟩
    | inr record =>
      cases record with
      | inl serverQuery =>
        cases serverQuery with
        | inl send =>
          exact serverSend_closed modes ideal replace setup codec route control invariant.1
            send.1 send.2 before invariant.2.1 invariant.2.2 result supported
        | inr raw =>
          exact serverReceive_closed modes ideal replace setup codec route control invariant.1
            raw before invariant.2.1 invariant.2.2 result supported
      | inr beaconQuery =>
        rcases beaconQuery with ⟨owner, query⟩
        cases query with
        | inl plaintext =>
          exact beaconSend_closed modes ideal replace setup codec control invariant.1
            owner plaintext before invariant.2.1 invariant.2.2 result supported
        | inr raw =>
          exact beaconReceive_closed modes ideal replace setup codec control invariant.1
            owner raw before invariant.2.1 invariant.2.2 result supported

/-- Every adaptive source schedule preserves dictionary origin at its complete actual resulting control and private state. -/
theorem schedule_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) X) (control : PqxdhRecordLiftProtocol.Control n) (before : CtxPrivate n)
    (invariant : Invariant control before) (result : (X × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route client control)).run before)) :
    Invariant result.1.2 result.2 := by
  induction client using OracleComp.inductionOn generalizing control before result with
  | pure value =>
    simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact invariant
  | query_bind query next ih =>
    simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨inner, reached, continued⟩ := supported
    exact ih inner.1.1 inner.1.2 inner.2
      (handler_invariant modes ideal replace setup codec route query control before invariant inner reached)
      result continued

/-- Actual empty source control and dictionaries establish the invariant without an origin premise. -/
theorem initial_invariant : Invariant (PqxdhRecordLiftProtocol.initialControl : PqxdhRecordLiftProtocol.Control n)
    CtxPrivate.initial :=
  ⟨PqxdhRecordLiftProtocolHistory.initial_safe, initial_closed (Claims PqxdhRecordLiftProtocol.initialControl), rfl⟩

/-- The complete actual CTX world establishes dictionary provenance for arbitrary environments, adaptive adversaries and supported outcomes. -/
theorem ctxRun_invariant {E : Type} (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : PqxdhRecordLiftIdeal.Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    Invariant result.1.2 result.2 :=
  schedule_invariant modes ideal replace setup codec route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)
    PqxdhRecordLiftProtocol.initialControl CtxPrivate.initial initial_invariant result supported

/-- Every actual ideal-world dictionary entry has an exact produced source frame on an installed sender with its slot and physical direction. -/
theorem ctxRun_dictionary_origin {E : Type} (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : PqxdhRecordLiftIdeal.Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    ∃ handle frame, PqxdhRecordFactsOriginHandles.OwnsLabel result.1.2 label handle ∧
      (some handle, frame) ∈ result.2.base.produced ∧ PqxdhRecordFactsOriginReplay.Matches frame entry := by
  have invariant := ctxRun_invariant modes ideal replace setup codec route env serverKid bounds mode adversary result supported
  obtain ⟨tag, frame, ⟨handle, rfl, owned⟩, produced, matched⟩ := invariant.2.1 label entry member
  exact ⟨handle, frame, owned, produced, matched⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant


/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.handler_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.handler_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.schedule_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.schedule_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.initial_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.initial_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.ctxRun_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.ctxRun_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.ctxRun_dictionary_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant.ctxRun_dictionary_origin
