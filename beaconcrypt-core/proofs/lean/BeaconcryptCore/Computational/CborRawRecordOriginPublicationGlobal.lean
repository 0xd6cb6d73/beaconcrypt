-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginPrefixes
import BeaconcryptCore.Computational.CborRawRecordOriginStartup
import BeaconcryptCore.Computational.CborRawRecordOriginProjection
import BeaconcryptCore.Computational.CborRawRecordOriginObservation
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent

/-! Concrete initialized raw CBOR publication witnesses. Startup and actual Server installation derive empty dictionaries; the original full ledger retains each receive's exact earlier transcript. Erased-world failed writers are transported only through the proved retained observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal
open PqxdhRecordLiftInterface
open PqxdhRecordLiftIdeal hiding ctxRun
open PqxdhRecordLiftProtocol (Control)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Entry)
open PqxdhRecordLiftProtocolHistory (Safe)
open PqxdhRecordFactsOriginAmbient (Kept)
open PqxdhRecordFactsOriginPublicationHistory (History)
open PqxdhRecordFactsOriginPublicationPrefixes (Prefixes)
open PqxdhRecordFactsOriginPublicationEvent (FailedWriterAt forged_failed)
open CborRawRecordOriginObservation (ctxRun erasedRun retained_support retained_view retained_failed)
open CborRawRecordOriginPrefixes (full_program_invariant)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

private abbrev RecordAd := Aeneas.Std.Array Aeneas.Std.U8 151#usize

/-- The actual cursor-aware startup derives the original empty source dictionaries and writer logs. -/
theorem startup_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E)
    (result : (((Option (PqxdhLiveServerConstruction.Created RecordAd × E) × CborRecordWorldClient.Shell) × Control n) × CtxPrivate n))
    (supported : result ∈ support (CborRawRecordOriginFlatten.startup (ctxInterpreter modes replace setup codec) env codec route CtxPrivate.initial)) :
    Kept CtxPrivate.initial result.2 := by
  have projected : ((result.1.1.1, result.1.2), result.2) ∈ support
      (PqxdhRecordLiftFlat.startup modes replace setup codec route env) := by
    change ((result.1.1.1, result.1.2), result.2) ∈ support
      ((simulateQ (ctxInterpreter modes replace setup codec)
        ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
          (simulateQ coinLift env.start)).run PqxdhRecordLiftProtocol.initialControl)).run CtxPrivate.initial)
    rw [← CborRawRecordOriginProjection.startup_project _ env codec route CtxPrivate.initial, support_map]
    exact ⟨result, supported, rfl⟩
  exact PqxdhRecordFactsOriginPublicationGlobal.startup_kept modes replace setup codec route env _ projected

/-- Actual cursor-aware installation retains all reached private coordinate dictionaries and writer logs. -/
theorem install_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created RecordAd) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (before : CtxPrivate n) (result : (CborRecordWorldClient.Shell × Control n) × CtxPrivate n)
    (supported : result ∈ support (CborRawRecordOriginFlatten.install (ctxInterpreter modes replace setup codec) codec route created shell control before)) :
    Kept before result.2 := by
  rw [CborRawRecordOriginProjection.install_eq, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordFactsOriginAmbient.initialize_kept modes replace setup codec created control before inner reached

/-- The actual initialized raw program derives its literal prefix and failed-writer witness. -/
theorem ctxRun_prefixes (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ result.1.1, Prefixes codec route result.1.2 result.2 value.2.1.2.transcript := by
  change result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
    (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)).run CtxPrivate.initial) at supported
  rw [CborRawRecordOriginFlatten.program_flat, mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  have bornSafe := CborRawRecordOriginStartup.startup_safe (ctxInterpreter modes replace setup codec) env codec route CtxPrivate.initial born bornSupported
  have bornKept := startup_kept modes replace setup codec route env born bornSupported
  cases bornEq : born.1.1.1 with
  | none =>
    simp only [bornEq] at continued
    obtain rfl := (mem_support_pure_iff _ _).mp continued
    simp
  | some initial =>
    rcases initial with ⟨created, initial⟩
    simp only [bornEq] at continued
    rw [mem_support_bind_iff] at continued
    obtain ⟨installed, installSupported, continued⟩ := continued
    have installedSafe := CborRawRecordOriginStartup.install_safe (ctxInterpreter modes replace setup codec) codec route
      created born.1.1.2 born.1.2 bornSafe born.2 installed installSupported
    have installedKept := install_kept modes replace setup codec route created born.1.1.2 born.1.2 born.2 installed installSupported
    have empty : History codec installed.1.2 installed.2 [] := by
      intro label entry member
      rw [installedKept.keys, bornKept.keys] at member
      exact False.elim (List.not_mem_nil member)
    rw [support_map] at continued
    obtain ⟨final, finalSupported, rfl⟩ := continued
    have complete := full_program_invariant modes ideal replace setup codec route readback env serverKid bounds
      (PqxdhDeploymentInterface.asModeO mode adversary) _
        ⟨⟨installedSafe, empty⟩, by simp [Prefixes, PqxdhDeploymentSecrecy.Ledger.empty]⟩ final finalSupported
    intro value member
    obtain rfl := Option.mem_some_iff.mp member
    exact complete.2


/-- The actual initialized raw program derives its literal prefix and failed-writer witness. -/
theorem ctxView_prefixes (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ (ctxView result).result, Prefixes codec route result.1.2 result.2 value.2.1.transcript := by
  intro value member
  change value ∈ result.1.1.map _ at member
  rw [Option.mem_def, Option.map_eq_some_iff] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  exact ctxRun_prefixes modes ideal replace setup codec route readback env serverKid bounds mode adversary
    result supported original originalMember


/-- The actual initialized raw program derives its literal prefix and failed-writer witness. -/
theorem ctxRun_unpublished_failed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary))
    (unpublished : UnpublishedAccept codec route (ctxView result)) :
    ∃ value ∈ (ctxView result).result, ∃ before event after,
      value.2.1.transcript = before ++ event :: after ∧
      FailedWriterAt codec route result.1.2 result.2 event := by
  obtain ⟨value, present, before, event, after, split, forged⟩ := unpublished
  have history := ctxView_prefixes modes ideal replace setup codec route readback env serverKid bounds mode adversary
    result supported value present before event after split
  exact ⟨value, present, before, event, after, split, forged_failed codec route result.1.2 result.2 before event history forged⟩


/-- The actual initialized raw program derives its literal prefix and failed-writer witness. -/
theorem erased_unpublished_failed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (erasedRun modes replace setup codec route env serverKid bounds mode adversary))
    (unpublished : UnpublishedAccept codec route (ctxView result)) :
    ∃ value ∈ (ctxView result).result, ∃ before event after,
      value.2.1.transcript = before ++ event :: after ∧
      FailedWriterAt codec route result.1.2 result.2 event := by
  obtain ⟨original, reached, same⟩ := retained_support modes ideal replace setup codec route env serverKid bounds mode adversary result supported
  have view := retained_view original result same
  have originalEvent : UnpublishedAccept codec route (ctxView original) := view ▸ unpublished
  obtain ⟨value, present, before, event, after, split, failed⟩ :=
    ctxRun_unpublished_failed modes ideal replace setup codec route readback env serverKid bounds mode adversary original reached originalEvent
  exact ⟨value, view ▸ present, before, event, after, split, retained_failed codec route original result same event failed⟩


end BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.startup_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.startup_kept
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.install_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.install_kept
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.ctxRun_prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.ctxRun_prefixes
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.ctxView_prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.ctxView_prefixes
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.ctxRun_unpublished_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.ctxRun_unpublished_failed
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.erased_unpublished_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal.erased_unpublished_failed
