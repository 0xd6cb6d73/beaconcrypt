-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryDeployment
import BeaconcryptCore.Computational.PqxdhBoundaryDeploymentLater

/-!
# Production composition of items 3 and 7: generic transfer lemmas

The production composition instantiates the CE-12 headlines of item 3 at the production codec `codec′ = PqxdhBoundaryRecordPrelude.withReader codec reader` and route `route′ = RawCtxFrameDecoding.sender reader.model` of item 7 and moves every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`) or of the LQ-F experiment (`PqxdhDeploymentLaterServerGame.game`) to the production source game of PB-D (`PqxdhBoundaryDeployment.sourceGame`, `PqxdhBoundaryDeploymentLater.laterSourceGame`), at the identity index 0 of the headlines. This module holds the generic part, which does not mention any headline.

- `observe_zero` and `observe_later_zero`: for every observation of the game's returned value, the observation read back through `unwrap` on the source game is the same computation as the observation on the game at codec′ and route′ (through `classical_zero` and `later_zero` and `unwrap_okMap`).
- `evalDist_zero` and `evalDist_later_zero`: the same as an equality of output distributions, for every measurable observation, hence for every event of the returned value (through `classical_evalDist` and `later_evalDist` at index 0).
- `chance` and `chance_later`: the Boolean form that the headlines use, `𝒟[(decision ∘ unwrap) <$> source] {true} = 𝒟[decision <$> game] {true}`; the production headline modules rewrite every game occurrence with these two lemmas.
- `frameReadBack_withReader` and `readWritable_withReader`: what the two codec-dependent contracts that some headlines take say at codec′ (`Iff.rfl`). They are readings of carried premises, not discharges.

`unwrap` reads the Rust `fail` and `div` results as `none`; the source games never produce them (`classical_normal`, `later_normal`). No assumption or contract is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentLater (PostSpec)
open PqxdhDeploymentLaterServerGame (Reveal)

variable {ι KemSK Reader Response Message Root A X Out Z : Type} {baseSpec : OracleSpec ι}

/-- Observation transfer for the classical game at index 0 (through `classical_zero`): every observation of the CE game's returned value at the production codec and route is the same computation as the observation read back through `unwrap` on the classical source game. -/
theorem observe_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (observe : PqxdhBoundaryDeployment.GameOutcome KemSK X × A → Z) :
    (observe ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime =
      observe <$> (PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode adversary).run runtime := by
  rw [PqxdhBoundaryDeployment.classical_zero, Functor.map_map]
  congr 1
  funext outcome
  simp only [Function.comp_apply, PqxdhBoundaryDeployment.unwrap_okMap]

/-- Distribution transfer for the classical game at index 0 (through `classical_evalDist`): for every measurable observation of the CE game's returned value, its output distribution on the CE game at the production codec and route equals the distribution of the observation read back through `unwrap` on the classical source game; in particular every event of the returned value has the same probability on both. -/
theorem evalDist_zero [MeasurableSpace Z] (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (observe : PqxdhBoundaryDeployment.GameOutcome KemSK X × A → Z) :
    𝒟[(observe ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] =
      𝒟[observe <$> (PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode adversary).run runtime] :=
  PqxdhBoundaryDeployment.classical_evalDist setup codec reader erased checks ensureInit 0 bounds mode adversary runtime
    observe

/-- Boolean-event transfer for the classical game at index 0: the chance of a decision on the CE game's returned value at the production codec and route equals the chance of the same decision read back through `unwrap` on the classical source game. -/
theorem chance (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (decision : PqxdhBoundaryDeployment.GameOutcome KemSK X × A → Bool) :
    𝒟[(decision ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} =
      𝒟[decision <$> (PqxdhDeploymentSecrecy.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
        (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode adversary).run runtime] {true} :=
  congrArg (fun measure => measure {true})
    (evalDist_zero setup codec reader erased checks ensureInit bounds mode adversary runtime decision)

/-- Observation transfer for the LQ-F game at index 0 (through `later_zero`): every observation of the LQ-F game's returned value at the production codec and route is the same computation as the observation read back through `unwrap` on the LQ-F source game. -/
theorem observe_later_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (observe : PqxdhBoundaryDeploymentLater.GameOutcome KemSK Out × A → Z) :
    (observe ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime =
      observe <$> (PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode first second).run runtime := by
  rw [PqxdhBoundaryDeploymentLater.later_zero, Functor.map_map]
  congr 1
  funext outcome
  simp only [Function.comp_apply, PqxdhBoundaryDeploymentLater.unwrap_okMap]

/-- Distribution transfer for the LQ-F game at index 0 (through `later_evalDist`): for every measurable observation of the LQ-F game's returned value, its output distribution on the LQ-F game at the production codec and route equals the distribution of the observation read back through `unwrap` on the LQ-F source game. -/
theorem evalDist_later_zero [MeasurableSpace Z] (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (observe : PqxdhBoundaryDeploymentLater.GameOutcome KemSK Out × A → Z) :
    𝒟[(observe ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] =
      𝒟[observe <$> (PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode first second).run runtime] :=
  PqxdhBoundaryDeploymentLater.later_evalDist setup codec reader erased checks ensureInit 0 bounds mode first second
    runtime observe

/-- Boolean-event transfer for the LQ-F game at index 0: the chance of a decision on the LQ-F game's returned value at the production codec and route equals the chance of the same decision read back through `unwrap` on the LQ-F source game. -/
theorem chance_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (decision : PqxdhBoundaryDeploymentLater.GameOutcome KemSK Out × A → Bool) :
    𝒟[(decision ∘ PqxdhBoundaryDeploymentLater.unwrap) <$>
        (PqxdhBoundaryDeploymentLater.laterSourceGame setup codec reader erased checks ensureInit 0 bounds mode first
          second).run runtime] {true} =
      𝒟[decision <$> (PqxdhDeploymentLaterServerGame.game setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        checks (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode first second).run runtime] {true} :=
  congrArg (fun measure => measure {true})
    (evalDist_later_zero setup codec reader erased checks ensureInit bounds mode first second runtime decision)

/-- Reading of a carried premise at the production codec: the frame read-back law at codec′ says that the production decoder `RawCtxFrameDecoding.decode reader.model` reads back every frame that the abstract frame writer produces, as a nonempty byte string (definitional; carried, not discharged). -/
theorem frameReadBack_withReader (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) :
    PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader) ↔
      ∀ frame bytes, codec.frameWrite frame = some bytes →
        bytes ≠ [] ∧ RawCtxFrameDecoding.decode reader.model bytes = some frame :=
  Iff.rfl

/-- Reading of a carried premise at the production codec: the writer-totality law at codec′ is the totality of the abstract frame writer on every frame that the production decoder accepts (definitional; carried, not discharged). -/
theorem readWritable_withReader (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) :
    PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec reader).frameWrite
        (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead ↔
      PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite (RawCtxFrameDecoding.decode reader.model) :=
  Iff.rfl

end BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.observe_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.observe_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.evalDist_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.evalDist_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.chance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.chance

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.observe_later_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.observe_later_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.evalDist_later_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.evalDist_later_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.chance_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.chance_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.frameReadBack_withReader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.frameReadBack_withReader

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.readWritable_withReader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer.readWritable_withReader
