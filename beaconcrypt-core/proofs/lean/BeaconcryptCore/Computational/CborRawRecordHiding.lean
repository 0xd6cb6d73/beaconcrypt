-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldClient
import BeaconcryptCore.Computational.PqxdhRecordLiftHiding
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds

/-! The public CBOR cursor filter remains below the secrecy ledger. Under the actual World reply relation, every forwarded or refused request preserves equal public cursors: raw replies may differ in plaintext but retain success, while installation replies agree. Consequently the complete cursor-filtered adaptive program inherits the existing random-record hiding coupling without changing test/fresh sampling or ledger updates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordHiding
open PqxdhRecordLiftInterface
open PqxdhRecordLiftHiding (Coupled WorldRel ResultRel PrivRel EqRel ServiceRel)
open PqxdhRecordLiftIdeal
variable {n : Nat}

private theorem worldRel_refl (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query) :
    WorldRel query reply reply := by
  rcases query with created | effect | (send | raw) | ⟨owner, send | raw⟩ <;> rfl

/-- Public cursors depend on actual send operands and equal installation replies, while raw-receive plaintexts cannot change them. -/
theorem next_eq (query : (WorldSpec n).Domain) (first second : (WorldSpec n).Range query)
    (related : WorldRel query first second) (shell : CborRecordWorldClient.Shell) :
    CborRecordWorldClient.next query first shell = CborRecordWorldClient.next query second shell := by
  rcases query with created | effect | (send | raw) | ⟨owner, send | raw⟩
  · rfl
  · change first = second at related
    cases related
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Refusals stutter in both worlds and forwards retain equal public shells, with the original World reply relation. -/
theorem handler_couple (query : (WorldSpec n).Domain) (shell : CborRecordWorldClient.Shell) :
    Coupled WorldRel (fun first second => WorldRel query first.1 second.1 ∧ first.2 = second.2)
      ((CborRecordWorldClient.handler query).run shell) ((CborRecordWorldClient.handler query).run shell) := by
  cases refused : CborRecordWorldClient.refusal query shell with
  | some reply =>
    simp only [CborRecordWorldClient.handler, StateT.run, refused]
    exact .pure _ _ ⟨worldRel_refl query reply, rfl⟩
  | none =>
    simp only [CborRecordWorldClient.handler, StateT.run, refused, CborRecordWorldClient.forward]
    exact (Coupled.query (Rr := WorldRel) query).map fun first second related =>
      ⟨related, next_eq query first second related shell⟩

/-- The cursor filter preserves arbitrary coupled adaptive World continuations without moving above their private ledger work. -/
theorem client_couple {First Second : Type} {related : First → Second → Prop}
    {first : OracleComp (WorldSpec n) First} {second : OracleComp (WorldSpec n) Second}
    (coupled : Coupled WorldRel related first second)
    (shell : CborRecordWorldClient.Shell := CborRecordWorldClient.initial) :
    Coupled WorldRel related (CborRecordWorldClient.client first shell) (CborRecordWorldClient.client second shell) := by
  unfold CborRecordWorldClient.client
  exact (Coupled.simulateQ_run _ _ Eq
    (fun query left _ equal => equal ▸ handler_couple query left) coupled shell shell rfl).map
      fun _ _ result => result.1

/-- The complete mode-P secrecy program retains its actual test/fresh draws, ledger and public cursor admission. -/
theorem worldProgram_couple {E X Reader Response : Type} (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec .P) X) :
    Coupled WorldRel ResultRel
      (CborRecordWorldClient.client (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds .P adversary))
      (CborRecordWorldClient.client (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds .P adversary)) :=
  client_couple (PqxdhRecordLiftHiding.worldProgram_couple env crypto codec serverKid bounds adversary)

/-- The actual random-record interpreter couples both cursor-filtered programs with equal control and related complete private state. -/
theorem ctxRun_couple {ι : Type} {base : OracleSpec ι} {KemSK Reader Response E X : Type}
    (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes) (lengths : ∀ plaintext, (replace₁ plaintext).length = (replace₂ plaintext).length)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec .P) X) :
    Coupled EqRel (fun first second => (ResultRel first.1.1 second.1.1 ∧ first.1.2 = second.1.2) ∧ PrivRel first.2 second.2)
      (PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) replace₁ setup codec route
        (CborRecordWorldClient.client (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds .P adversary)))
      (PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) replace₂ setup codec route
        (CborRecordWorldClient.client (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds .P adversary))) :=
  Coupled.simulateQ_run _ _ PrivRel (PqxdhRecordLiftHiding.interpreter_couple replace₁ replace₂ lengths setup codec)
    (PqxdhRecordLiftHiding.schedule_couple _ route
      (worldProgram_couple env setup.source.crypto codec serverKid bounds adversary) _) _ _ ⟨rfl, fun _ => rfl⟩

/-- Length-preserving plaintext replacement leaves the complete hiding observation of the actual CBOR cursor-filtered random-record world unchanged. -/
theorem hiding_replace {ι : Type} {base : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec .P) X)
    (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes) (lengths : ∀ plaintext, (replace₁ plaintext).length = (replace₂ plaintext).length) :
    (fun result => hidingView (ctxView result)) <$>
        PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) replace₁ setup codec route
          (CborRecordWorldClient.client (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds .P adversary)) =
      (fun result => hidingView (ctxView result)) <$>
        PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) replace₂ setup codec route
          (CborRecordWorldClient.client (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds .P adversary)) :=
  (ctxRun_couple replace₁ replace₂ lengths setup codec route env serverKid bounds adversary).map_eq _ _
    fun first second related => PqxdhRecordLiftHiding.hidingView_rel first second related

end BeaconcryptCore.Computational.CborRawRecordHiding

/-- info: 'BeaconcryptCore.Computational.CborRawRecordHiding.next_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordHiding.next_eq

/-- info: 'BeaconcryptCore.Computational.CborRawRecordHiding.handler_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordHiding.handler_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordHiding.client_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordHiding.client_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordHiding.worldProgram_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordHiding.worldProgram_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordHiding.ctxRun_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordHiding.ctxRun_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordHiding.hiding_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordHiding.hiding_replace
