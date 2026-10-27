-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationLedger

/-! Publication history derived from actual source initialization and the empty ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationGlobal
open PqxdhRecordLiftIdeal PqxdhRecordLiftInterface PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginPublicationHistory PqxdhRecordFactsOriginPublicationNative
open PqxdhRecordFactsOriginPublicationLedger PqxdhRecordFactsOriginAmbient
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Entry Spec FullSpec FreshBounds Mode ModeSpec asModeO)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Every startup coin dispatches through the same literal restricted environment effect route. -/
theorem coin_lift (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : ProbComp X) :
    simulateQ (PqxdhRecordLiftProtocol.handler (n := n) codec.frameRead route) (simulateQ coinLift client) =
      simulateQ PqxdhRecordLiftProtocol.effects
        (simulateQ (fun coin => ((EnvEffects n).query (.inl coin) : OracleComp (EnvEffects n) _)) client) := by
  induction client using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, coinLift, simulateQ_spec_query, PqxdhRecordLiftProtocol.handler, ih]

/-- Actual startup retains the initial empty coordinate dictionaries and writer logs. -/
theorem startup_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E)
    (result : (Option (PqxdhLiveServerConstruction.Created Unit × E) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support (startup modes replace setup codec route env)) :
    Kept CtxPrivate.initial result.2 := by
  simp only [startup, coin_lift] at supported
  exact effects_program_kept modes replace setup codec _ _ _ result supported

/-- The complete initialized adaptive source supplies publication history at its actual final transcript, with no initial-history premise. -/
theorem ctxRun_history (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ result.1.1, History codec result.1.2 result.2 value.2.1.2.transcript := by
  rw [ctxRun_flat, mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  have bornSafe := PqxdhRecordFactsOriginGlobal.startup_safe modes replace setup codec route env born bornSupported
  have bornKept := startup_kept modes replace setup codec route env born bornSupported
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
    have installedKept := initialize_kept modes replace setup codec created born.1.2 born.2 installed installSupported
    have empty : History codec installed.1.2 installed.2 [] := by
      intro label entry member
      rw [installedKept.keys, bornKept.keys] at member
      exact False.elim (List.not_mem_nil member)
    rw [support_map] at continued
    obtain ⟨final, finalSupported, rfl⟩ := continued
    have complete := full_program_invariant modes ideal replace setup codec route readback env serverKid bounds
      (asModeO mode adversary) _ ⟨installedSafe, empty⟩ final finalSupported
    intro value member
    obtain rfl := Option.mem_some_iff.mp member
    exact complete.2

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationGlobal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationGlobal.coin_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationGlobal.coin_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationGlobal.startup_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationGlobal.startup_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationGlobal.ctxRun_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationGlobal.ctxRun_history
