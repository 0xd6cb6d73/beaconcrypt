-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftHiding
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets

/-!
# Record-lift later hiding (items 4 and 5, stage S6, R6)

**Statement.** `later_idealRecords_hiding` proves `PqxdhRecordLiftLaterTargets.LaterHidingStatement` as defined: for every environment, reveal function, mode-P run-phase adversary and post adversary (no `Frame` or budget premise), replacing every hidden seal plaintext by one of equal length leaves the law of the hiding projection `hidingView` of `laterIdealRecords` unchanged, as an equality of the mapped computations. `later_hiding_replace` states the same for any two replacements that agree on lengths.

**Method.** The syntactic coupling of `PqxdhRecordLiftHiding` (`Coupled`) carries over: the run phase is coupled with itself exactly as before (`PqxdhRecordLiftHiding.worldProgram_couple`), and the post phase is coupled with itself with equal results (`post_couple`), because each post request is a coin, HMAC or hash command whose replies related by `SpecRel` are equal (`postEmbed_couple`) and the environment and native commands are coupled with themselves (`PqxdhRecordLiftHiding.native_couple`). Started from equal environment states and outputs (which `ResultRel` gives), the post phase therefore produces equal outputs and environment states, and the run-phase ledger is kept, so the two-phase program is coupled with itself (`laterProgram_couple`); the compiled client and the random-mode interpreter layers are those of `PqxdhRecordLiftHiding` (`schedule_couple`, `interpreter_couple`), which gives `laterCtxRun_couple`, and `hidingView_rel` reads only fields that agree on related results.

**Contracts.** No theorem of this module has an assumption or contract hypothesis, and no proof step uses a contract (per-theorem closure probe). New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftHiding PqxdhRecordLiftLaterWorlds
open PqxdhRecordLiftLaterTargets
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X Out R : Type}

/-- A post-phase request is coupled with itself with equal replies: it is a coin, HMAC or hash command, never a raw receive. -/
theorem postEmbed_couple (query : PostSpec.Domain) :
    Coupled SpecRel (EqRel query) (PqxdhDeploymentLater.postEmbed query) (PqxdhDeploymentLater.postEmbed query) := by
  rcases query with coin | (⟨key, message⟩ | bytes)
  · exact (Coupled.query (Rr := SpecRel) (.inl coin)).mono fun _ _ same => same
  · exact (Coupled.query (Rr := SpecRel) (.inr (.hmac key message))).mono fun _ _ same => same
  · exact (Coupled.query (Rr := SpecRel) (.inr (.hash bytes))).mono fun _ _ same => same

/-- The post phase is coupled with itself with equal results: it issues only environment commands, coins and hashes, whose World replies related by `WorldRel` are equal. -/
theorem post_couple (env : Environment n E) (adversary : OracleComp PostSpec Out) (state : E) :
    Coupled WorldRel (fun p₁ p₂ => p₁ = p₂) ((PqxdhRecordLiftLater.post env adversary).run state)
      ((PqxdhRecordLiftLater.post env adversary).run state) := by
  unfold PqxdhRecordLiftLater.post
  have inner : Coupled SpecRel (fun a b => a = b) (simulateQ PqxdhDeploymentLater.postEmbed adversary)
      (simulateQ PqxdhDeploymentLater.postEmbed adversary) :=
    Coupled.simulateQ (Rr := EqRel) _ _ postEmbed_couple (Coupled.refl _ eqRel_eq fun _ => rfl)
  exact (Coupled.simulateQ_run _ _ Eq (fun q e₁ _ he => he ▸ native_couple env q e₁) inner state state rfl).mono
    fun p₁ p₂ related => Prod.ext related.1 related.2

/-- The two-phase World program with a mode-P run-phase adversary is coupled with itself: client results agree on the creation, the post output, the environment state and the run-phase ledger up to raw-receive plaintexts. -/
theorem laterProgram_couple (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (reveal : E → R) (first : OracleComp (ModeSpec .P) X)
    (second : X → R → OracleComp PostSpec Out) :
    Coupled WorldRel ResultRel (PqxdhRecordLiftLater.program env crypto codec serverKid bounds .P reveal first second)
      (PqxdhRecordLiftLater.program env crypto codec serverKid bounds .P reveal first second) := by
  unfold PqxdhRecordLiftLater.program
  refine (worldProgram_couple env crypto codec serverKid bounds first).bind fun r₁ r₂ related => ?_
  rcases r₁ with _ | ⟨created₁, ⟨output₁, ledger₁⟩, state₁⟩ <;>
    rcases r₂ with _ | ⟨created₂, ⟨output₂, ledger₂⟩, state₂⟩ <;> simp only [ResultRel] at related
  · exact .pure _ _ trivial
  · obtain ⟨createdSame, outputSame, ledgers, stateSame⟩ := related
    subst createdSame outputSame stateSame
    refine (post_couple env _ state₁).bind fun p₁ p₂ same => ?_
    subst same
    exact .pure _ _ ⟨rfl, rfl, ledgers, rfl⟩

/-- **Later world coupling.** In the later random-ciphertext CTX world, two plaintext replacements that agree on lengths give, with the same coins, client results that agree up to raw-receive plaintexts, the same control state and private states that agree up to recorded seal plaintexts. -/
theorem laterCtxRun_couple (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes)
    (lengths : ∀ m, (replace₁ m).length = (replace₂ m).length) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Std.U64) (bounds : FreshBounds) (reveal : E → R) (first : OracleComp (ModeSpec .P) X)
    (second : X → R → OracleComp PostSpec Out) :
    Coupled EqRel (fun p₁ p₂ => (ResultRel p₁.1.1 p₂.1.1 ∧ p₁.1.2 = p₂.1.2) ∧ PrivRel p₁.2 p₂.2)
      (laterCtxRun setup codec route env serverKid bounds .P reveal first second (fun _ => .random) replace₁)
      (laterCtxRun setup codec route env serverKid bounds .P reveal first second (fun _ => .random) replace₂) :=
  Coupled.simulateQ_run _ _ PrivRel (interpreter_couple replace₁ replace₂ lengths setup codec)
    (schedule_couple _ route (laterProgram_couple env setup.source.crypto codec serverKid bounds reveal first second) _)
    _ _ ⟨rfl, fun _ => rfl⟩

/-- Later hiding for any two plaintext replacements that agree on lengths. -/
theorem later_hiding_replace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (env : Environment n E)
    (reveal : E → R) (first : OracleComp (ModeSpec .P) X) (second : X → R → OracleComp PostSpec Out)
    (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes) (lengths : ∀ m, (replace₁ m).length = (replace₂ m).length) :
    (fun result => hidingView (ctxView result)) <$>
        laterCtxRun setup codec route env serverKid bounds .P reveal first second (fun _ => .random) replace₁ =
      (fun result => hidingView (ctxView result)) <$>
        laterCtxRun setup codec route env serverKid bounds .P reveal first second (fun _ => .random) replace₂ :=
  (laterCtxRun_couple replace₁ replace₂ lengths setup codec route env serverKid bounds reveal first second).map_eq _ _
    fun p₁ p₂ related => hidingView_rel p₁ p₂ related

/-- **Later `idealRecords_hiding` (R6), delivered.** `LaterHidingStatement` as defined: in mode P, with the generic post phase, replacing every hidden seal plaintext by one of equal length leaves the law of the hiding projection of `laterIdealRecords` unchanged. No contract. -/
theorem later_idealRecords_hiding (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (n : Nat) :
    LaterHidingStatement setup codec route serverKid bounds n := by
  intro E X Out R env reveal first second replace lengths
  exact later_hiding_replace setup codec route serverKid bounds env reveal first second replace id lengths

end BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.postEmbed_couple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.postEmbed_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.post_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.post_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.laterProgram_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.laterProgram_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.laterCtxRun_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.laterCtxRun_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.later_hiding_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.later_hiding_replace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.later_idealRecords_hiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding.later_idealRecords_hiding
