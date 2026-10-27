import BeaconcryptCore.Computational.PqxdhServerAuthEntryState
import BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor
import BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor
import BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The concrete omitted-entry services consume only the selected 108-byte output. Both opposite-role callbacks are unused by the proved source continuations; their closed no-op instantiations capture no selected secret and make no query. Real public derivations and every reached source primitive effect remain unchanged. -/
noncomputable def factorServices (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) :
    Services Response HiddenTable where
  derive := hiddenDerive setup.hmac setup.joint setup.dh context.seed context.scalar
  table := hiddenPublic
  hiddenBuild token payload server := PqxdhServerAuthLoggedSendFactor.factored
    (fun entry _ _ => pure (entry, .None))
    (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
    (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)
    (PqxdhServerAuthCtxMaterial.factor value) token.pending payload () server
  hiddenAfter pending := PqxdhServerAuthBeaconFactor.factored
    (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
    (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response))
    codec.frameRead (PqxdhPhase2DhRootConsumer.cleared pending) (PqxdhServerAuthCtxMaterial.factor value)

/-- Complete service equality instantiates both actual source continuation theorems. The root disappears from the executable interface without dropping the native states, optional results, seal log or shared cache. -/
theorem source_factor_services (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (root : RootOutput) :
    sourceHiddenServices setup codec checks context root =
      factorServices setup codec checks context (PqxdhServerAuthKeySchedule.fromRoot setup.source root) := by
  simp only [sourceHiddenServices, factorServices, PqxdhServerAuthCtxMaterial.factor_source]
  congr 1
  · funext token payload server
    exact PqxdhServerAuthLoggedSendFactor.logged_server_send_factor setup codec checks _ _ _ _ _ _
  · funext pending
    exact PqxdhServerAuthBeaconFactor.beacon_afterRoot_factor setup codec _ _ _

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The unchanged adaptive adversary under the complete omitted-entry interpreter, starting from the actual sampled source context and empty private annotations. -/
noncomputable def hiddenRun (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable) : ProbComp (HiddenState KemSK) :=
  Prod.snd <$> (simulateQ (hiddenHandler setup codec checks context Q j services)
    (adversary (contextInput setup revealSeed context))).run
      ((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false)

/-- The original per-entry event, with the private source refusal branch rejected. No plaintext or session witness is supplied by the adversary to this decision. -/
noncomputable def hiddenDecision (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK) : Bool := by
  classical
  exact decide (state.1.2.2.bad = false ∧ EntryEvent setup context.seed context.scalar Q j state.1.1.ghost)

/-- The concrete key-schedule reduction continuation. Its arguments contain neither the selected PRK nor the selected root or first initial chain. The complete source context remains private to the interpreter and is presented through the original public-input function. -/
noncomputable def entryDistinguisher (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) : ProbComp Bool :=
  hiddenDecision setup context Q j <$>
    hiddenRun setup codec checks adversary revealSeed context Q j (factorServices setup codec checks context value)

/-- Mathematical source comparison before key-schedule replacement; only its two actual continuation callbacks take the selected root. -/
noncomputable def sourceHiddenDecision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (prk : HmacBlock) : ProbComp Bool :=
  hiddenDecision setup context Q j <$>
    hiddenRun setup codec checks adversary revealSeed context Q j
      (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk))

/-- Complete actual adaptive source factorization, including the original final event, follows from exact equality of the two source continuation services. -/
theorem source_hidden_factor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (prk : HmacBlock) :
    sourceHiddenDecision setup codec checks adversary revealSeed Q j context prk =
      entryDistinguisher setup codec checks adversary revealSeed Q j context
        (PqxdhServerAuthKeySchedule.keySchedule setup.source setup.hmac prk) := by
  simp only [sourceHiddenDecision, entryDistinguisher, PqxdhServerAuthKeySchedule.keySchedule,
    source_factor_services]

/-- The uniform per-entry game uses the same real source context and same adaptive experiment, replacing only the joint selected 108-byte output. -/
noncomputable def uniformEntryGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) : ProbComp Bool := do
  let context ← contextSample setup codec
  let value ← $ᵗ PqxdhServerAuthKeySchedule.Output
  entryDistinguisher setup codec checks adversary revealSeed Q j context value

/-- The factored source game retains the actual context-before-PRK sampling order. -/
noncomputable def realEntryGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) : ProbComp Bool := do
  let context ← contextSample setup codec
  let prk ← $ᵗ HmacBlock
  sourceHiddenDecision setup codec checks adversary revealSeed Q j context prk

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.source_factor_services' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.source_factor_services
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.source_hidden_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.source_hidden_factor
