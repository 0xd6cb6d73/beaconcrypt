-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginLedger
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant

/-! Initialized complete-world record provenance and the structural unproduced-record event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginControl
open PqxdhRecordFactsOriginPublished PqxdhRecordFactsOriginAccepted
open PqxdhRecordFactsOriginNative PqxdhRecordFactsOriginMonotone
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Receiver Spec FullSpec Entry Secrecy FreshBounds Mode ModeSpec asModeO)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The actual environment startup derives source control safety before any ledger is created. -/
theorem startup_safe (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E)
    (result : (Option (PqxdhLiveServerConstruction.Created Unit × E) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support (startup modes replace setup codec route env)) :
    Safe result.1.2 :=
  (PqxdhRecordLiftProtocolHistory.interpreted_schedule (ctxInterpreter modes replace setup codec)
    codec.frameRead route (simulateQ coinLift env.start) PqxdhRecordLiftProtocol.initialControl
    PqxdhRecordLiftProtocolHistory.initial_safe CtxPrivate.initial result supported).1

/-- Actual Server installation preserves the derived source control safety and all permitted reply paths. -/
theorem install_safe (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created Unit) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) (secret : CtxPrivate n)
    (result : (Unit × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support (install modes replace setup codec route created control secret)) :
    Safe result.1.2 :=
  (PqxdhRecordLiftProtocolHistory.handler codec.frameRead route (.inl created) control safe result.1
    (support_run_fst (ctxInterpreter modes replace setup codec) _ secret result supported)).1

/-- The initialized complete source execution supplies record evidence for every literal transcript entry. -/
theorem ctxRun_entryFacts (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript,
      EntryFacts codec route result.1.2 result.2 entry := by
  rw [ctxRun_flat] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  have bornSafe := startup_safe modes replace setup codec route env born bornSupported
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
    have installedSafe := install_safe modes replace setup codec route created born.1.2 bornSafe born.2 installed installSupported
    rw [support_map] at continued
    obtain ⟨final, finalSupported, rfl⟩ := continued
    have complete := PqxdhRecordFactsOriginLedger.full_program_invariant modes ideal replace setup codec route readback
      env serverKid bounds (asModeO mode adversary) _
      (PqxdhRecordFactsOriginLedger.empty_invariant codec route _ installedSafe) final finalSupported
    intro value member
    have equal := Option.some.inj member
    subst value
    exact complete.2

/-- The public view retains exactly the ledger facts established by the complete source execution. -/
theorem ctxView_entryFacts (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ (ctxView result).result, ∀ entry ∈ value.2.1.transcript,
      EntryFacts codec route result.1.2 result.2 entry := by
  intro value member
  change value ∈ result.1.1.map _ at member
  rw [Option.mem_def, Option.map_eq_some_iff] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  exact ctxRun_entryFacts modes ideal replace setup codec route readback env serverKid bounds mode adversary
    result supported original originalMember

/-- A supported initialized ideal CTX execution cannot accept an unproduced hidden-counterpart frame. -/
theorem ctxRun_not_unproduced (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ¬UnproducedAccept codec route (ctxView result) := by
  rintro ⟨value, valueMember, entry, entryMember, receiver, raw, decrypted, handle, slot, frame,
    received, routed, hidden, decoded, neverProduced⟩
  have facts := ctxView_entryFacts modes ideal replace setup codec route readback env serverKid bounds mode adversary
    result supported value valueMember entry entryMember
  obtain ⟨actualHandle, actualRouted, accepted⟩ := facts.2 receiver raw decrypted received
  have handleEq : actualHandle = handle := Option.some.inj (actualRouted.symm.trans routed)
  subst actualHandle
  rcases accepted with known | ⟨label, installed, direction, actualFrame, actualDecoded, sealedEntry, member, matched, _⟩
  · have absent := known_no_slot result.1.2 handle known
    change handleSlot result.1.2 handle = some slot at hidden
    rw [absent] at hidden
    cases hidden
  · have slotEq : label.slot = slot := Option.some.inj (installed.symm.trans hidden)
    have frameEq : actualFrame = frame := Option.some.inj (actualDecoded.symm.trans decoded)
    subst actualFrame
    obtain ⟨sender, producedFrame, owns, produced, producedMatches⟩ :=
      PqxdhRecordFactsOriginInvariant.ctxRun_dictionary_origin modes ideal replace setup codec route
        env serverKid bounds mode adversary result supported label sealedEntry member
    have sameFrame := matches_unique frame producedFrame sealedEntry matched producedMatches
    subst producedFrame
    have counterpart := counterpart_of_opposite result.1.2 label sender handle owns direction
    rw [slotEq] at counterpart
    exact neverProduced sender counterpart produced

/-- The structural origin event has probability zero in every initialized ideal CTX assignment and observation mode. -/
theorem ctxRun_unproduced_zero (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[(fun result => unproducedEvent codec route (ctxView result)) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} = 0 := by
  rw [← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_eq_zero_of_not_mem_support
  rw [support_map]
  rintro ⟨result, supported, winning⟩
  have impossible := ctxRun_not_unproduced modes ideal replace setup codec route readback env serverKid bounds mode adversary
    result supported
  simp only [unproducedEvent, decide_eq_true_eq] at winning
  exact impossible winning

/-- The integrity replay world satisfies the first zero-probability conjunct of `OriginStatement`. -/
theorem idealAuth_unproduced_zero (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[(fun result => unproducedEvent codec route (ctxView result)) <$>
      idealAuth setup codec route env serverKid bounds mode adversary] {true} = 0 :=
  ctxRun_unproduced_zero (fun _ => .replay) (by intro label; decide) id setup codec route readback
    env serverKid bounds mode adversary

/-- The mode-selected ideal-record world satisfies the second zero-probability conjunct of `OriginStatement`. -/
theorem idealRecords_unproduced_zero (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[(fun result => unproducedEvent codec route (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds mode adversary] {true} = 0 :=
  ctxRun_unproduced_zero (fun _ => recordMode mode) (by intro label; cases mode <;> decide) id setup codec route readback
    env serverKid bounds mode adversary

/-- Random ciphertexts in either observation mode also preserve exact structural origin. -/
theorem randomRecords_unproduced_zero (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[(fun result => unproducedEvent codec route (ctxView result)) <$>
      randomRecords setup codec route env serverKid bounds mode adversary] {true} = 0 :=
  ctxRun_unproduced_zero (fun _ => .random) (by intro label; decide) id setup codec route readback
    env serverKid bounds mode adversary

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.startup_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.startup_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.install_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.install_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.ctxRun_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.ctxRun_entryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.ctxView_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.ctxView_entryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.ctxRun_not_unproduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.ctxRun_not_unproduced

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.ctxRun_unproduced_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.ctxRun_unproduced_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.idealAuth_unproduced_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.idealAuth_unproduced_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.idealRecords_unproduced_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.idealRecords_unproduced_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.randomRecords_unproduced_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal.randomRecords_unproduced_zero
