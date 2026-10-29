-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginPublicationGlobal
import BeaconcryptCore.Computational.CborRawRecordOriginProduced

/-! Structural origin for actual raw cursor records. Each successful receive consults an already produced hidden seal from its actual source dictionary, while refused sends preserve the full state and original transcript ordering. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginStructural
open PqxdhRecordLiftIdeal hiding ctxRun
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginAccepted PqxdhRecordFactsOriginReplay
open CborRawRecordOriginObservation (ctxRun)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Actual initialized raw source records derive this structural origin fact. -/
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
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp entryMember
  have facts := CborRawRecordOriginPublicationGlobal.ctxView_prefixes modes ideal replace setup codec route readback
    env serverKid bounds mode adversary result supported value valueMember before entry after split
  obtain ⟨actualHandle, actualRouted, accepted⟩ := facts receiver raw decrypted received
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
      CborRawRecordOriginProduced.ctxRun_dictionary_origin modes ideal replace setup codec route
        env serverKid bounds mode adversary result supported label sealedEntry member
    have sameFrame := matches_unique frame producedFrame sealedEntry matched producedMatches
    subst producedFrame
    have counterpart := counterpart_of_opposite result.1.2 label sender handle owns direction
    rw [slotEq] at counterpart
    exact neverProduced sender counterpart produced


/-- Actual initialized raw source records derive this structural origin fact. -/
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


/-- The exact arbitrary-client CTX endpoint used by raw record crypto has zero unproduced-acceptance probability. -/
theorem ctxRunOf_unproduced_zero (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[(fun result => unproducedEvent codec route (ctxView result)) <$>
      PqxdhRecordLiftLaterWorlds.ctxRunOf modes replace setup codec route
        (CborRawRecordLiftBounds.client env setup.source.crypto codec serverKid bounds mode adversary)] {true} = 0 := by
  rw [CborRawRecordOriginObservation.ctxRunOf_eq]
  exact ctxRun_unproduced_zero modes ideal replace setup codec route readback env serverKid bounds mode adversary

end BeaconcryptCore.Computational.CborRawRecordOriginStructural

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginStructural.ctxRun_not_unproduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginStructural.ctxRun_not_unproduced
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginStructural.ctxRun_unproduced_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginStructural.ctxRun_unproduced_zero
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginStructural.ctxRunOf_unproduced_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginStructural.ctxRunOf_unproduced_zero
