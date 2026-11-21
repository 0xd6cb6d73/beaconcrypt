-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationTemporal

/-! Every accepted observation keeps its own actual earlier transcript prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes
open PqxdhRecordLiftIdeal PqxdhRecordLiftInterface PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginControl PqxdhRecordFactsOriginMonotone
open PqxdhRecordFactsOriginPublicationHistory PqxdhRecordFactsOriginPublicationTemporal
open PqxdhRecordLiftProtocolHistory (Safe)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Entry FullSpec FreshBounds)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Splitting a transcript after one append selects either an earlier event or that literal final event. -/
theorem split_snoc {α : Type} (transcript : List α) (last : α) (before : List α) (event : α) (after : List α)
    (equal : transcript ++ [last] = before ++ event :: after) :
    (∃ tail, transcript = before ++ event :: tail) ∨ (before = transcript ∧ event = last ∧ after = []) := by
  induction transcript generalizing before with
  | nil =>
    cases before with
    | nil => simp only [List.nil_append, List.cons.injEq] at equal; exact Or.inr ⟨rfl, equal.1.symm, equal.2.symm⟩
    | cons head rest =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at equal
      exact False.elim (by have := congrArg List.length equal.2; simp at this)
  | cons head rest ih =>
    cases before with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at equal
      exact Or.inl ⟨rest, by simp only [List.nil_append, equal.1]⟩
    | cons first tail =>
      simp only [List.cons_append, List.cons.injEq] at equal
      rcases ih tail equal.2 with ⟨remaining, old⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨remaining, by simp only [List.cons_append, equal.1, old]⟩
      · exact Or.inr ⟨by simp only [equal.1], rfl, rfl⟩

/-- Every receive is related to its own prefix of the actual transcript, under the current source state. -/
def Prefixes (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (transcript : List Entry) : Prop :=
  ∀ before event after, transcript = before ++ event :: after →
    ReceivedBefore codec route control secret before event

/-- Source safety and current publication history, together with all past receive-prefix witnesses. -/
def Invariant (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (state : PqxdhDeploymentSecrecy.Ledger × NativeState n E) : Prop :=
  PqxdhRecordFactsOriginPublicationLedger.Invariant codec state ∧
    Prefixes codec route state.2.1.2 state.2.2 state.1.transcript

/-- Appending one literal ledger reply transports prior prefix witnesses and establishes the current receive's prefix. -/
theorem full_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec route before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Invariant codec route result.2 := by
  have progress := full_step modes replace setup codec route env serverKid bounds query before good.1.1 result supported
  have grows := full_grows modes ideal replace setup codec route env serverKid bounds query before result supported
  have recorded := PqxdhRecordFactsOriginLedger.full_record modes ideal replace setup codec route readback
    env serverKid bounds query before good.1.1 result supported
  refine ⟨PqxdhRecordFactsOriginPublicationLedger.full_invariant modes ideal replace setup codec route readback
    env serverKid bounds query before good.1 result supported, ?_⟩
  intro earlier event later split
  rw [recorded.1] at split
  rcases split_snoc before.1.transcript ⟨query, result.1⟩ earlier event later split with ⟨tail, old⟩ | ⟨rfl, rfl, rfl⟩
  · exact receivedBefore_mono codec route before.2.1.2 result.2.2.1.2 before.2.2 result.2.2.2 progress
      (fun handle known => full_known modes replace setup codec route env serverKid bounds query before handle known result supported)
      grows.seals earlier event (good.2 earlier event tail old)
  · exact full_receivedBefore modes ideal replace setup codec route readback env serverKid bounds query
      before good.1.1 good.1.2 result supported

/-- Arbitrary adaptive full continuations preserve every receive's original prefix and exact accepted-frame witness. -/
theorem full_program_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : Invariant codec route before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((simulateQ (fullImpl modes replace setup codec route env serverKid bounds) client).run before)) :
    Invariant codec route result.2 :=
  support_keep_oracle (fullImpl modes replace setup codec route env serverKid bounds) (Invariant codec route)
    (fun query state valid => full_invariant modes ideal replace setup codec route readback env serverKid bounds query state valid)
    client before good result supported

/-- The complete initialized adaptive source supplies every accepted record’s true prior prefix, with no initial-history premise. -/
theorem ctxRun_prefixes (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ result.1.1, Prefixes codec route result.1.2 result.2 value.2.1.2.transcript := by
  rw [ctxRun_flat, mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  have bornSafe := PqxdhRecordFactsOriginGlobal.startup_safe modes replace setup codec route env born bornSupported
  have bornKept := PqxdhRecordFactsOriginPublicationGlobal.startup_kept modes replace setup codec route env born bornSupported
  cases bornEq : born.1.1 with
  | none =>
    simp only [bornEq] at continued
    obtain rfl := (mem_support_pure_iff _ _).mp continued
    simp
  | some initial =>
    rcases initial with ⟨created, initial⟩
    simp only [bornEq] at continued
    rw [mem_support_bind_iff] at continued
    obtain ⟨installed, installSupported, continued⟩ := continued
    have installedSafe := PqxdhRecordFactsOriginGlobal.install_safe modes replace setup codec route
      created born.1.2 bornSafe born.2 installed installSupported
    have installedKept := PqxdhRecordFactsOriginAmbient.initialize_kept modes replace setup codec created born.1.2 born.2 installed installSupported
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

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes.split_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes.split_snoc

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes.full_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes.full_program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes.full_program_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes.ctxRun_prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes.ctxRun_prefixes
