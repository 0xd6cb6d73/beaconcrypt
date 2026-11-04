-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate
import BeaconcryptCore.Computational.CborRawRecordHiding
/-! An open World client retains a stateful public capacity service beneath the secrecy ledger. The service receives only the produced ciphertext length and its own environment state. It executes after the private send, so refusal retains advanced private kernels and attempted-frame histories while the ledger sees no send. Public service coins use the World coin route in this comparison client; exact external-coin/native accounting is a separate operational interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface
open PqxdhRecordLiftInterface
open PqxdhRecordLiftHiding (Coupled WorldRel SpecRel EqRel ResultRel eqRel_eq)
open PqxdhDeploymentInterface (Spec Mode ModeSpec FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {E Failure A X Reader Response : Type}

/-- Only ordinary uniform requests are introduced by a closed public platform computation. -/
def closed (work : StateT E ProbComp A) : StateT E (OracleComp (WorldSpec n)) A :=
  fun before => simulateQ coinLift (work.run before)

def post (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : Spec.Domain) (reply : Spec.Range query) : StateT E (OracleComp (WorldSpec n)) (Spec.Range query) :=
  match query with
  | .inr (.serverSend _ _) => closed (RegistrationNativePlatformOrdinaryGate.gate reserve
      (fun value => value.ciphertext.length) reply)
  | .inr (.beaconSend _ _) => closed (RegistrationNativePlatformOrdinaryGate.gate reserve
      (fun value => value.ciphertext.length) reply)
  | _ => pure reply

/-- Private execution precedes the public gate; the surrounding ledger consumes this final optional reply. -/
def native (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) :
    QueryImpl Spec (StateT E (OracleComp (WorldSpec n))) := fun query => do
  let reply ← PqxdhRecordLiftInterface.native env query
  post reserve query reply

noncomputable def program (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) : OracleComp (WorldSpec n)
      (PqxdhRecordLiftLaterWorlds.Outcome E X) := do
  let born ← simulateQ coinLift env.start
  match born with
  | none => pure none
  | some (created, initial) => do
      let _ ← (WorldSpec n).query (.inl created)
      let result ← (simulateQ (native env reserve)
        (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
          (PqxdhDeploymentInterface.asModeO mode adversary))).run initial
      pure (some (PqxdhRegistrationJointServerBirth.encode created, result))

/-- A reserve computation may keep an arbitrary retry tape and history. Its equal public inputs give an exact syntactic coupling. -/
theorem closed_couple (work : StateT E ProbComp A) (before : E) :
    Coupled WorldRel Eq ((closed (n := n) work).run before) ((closed (n := n) work).run before) :=
  Coupled.simulateQ (Rr := EqRel) _ _
    (fun query => Coupled.query (Rr := WorldRel) (.inr (.inl (.inl query))))
    (Coupled.refl _ eqRel_eq fun _ => rfl)

/-- Related send replies have identical public lengths; receive success relations pass unchanged through the identity branches. -/
theorem post_couple (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : Spec.Domain) (first second : Spec.Range query) (related : SpecRel query first second) (before : E) :
    Coupled WorldRel (fun left right => SpecRel query left.1 right.1 ∧ left.2 = right.2)
      ((post (n := n) reserve query first).run before) ((post (n := n) reserve query second).run before) := by
  rcases query with coin | command
  · exact .pure _ _ ⟨related, rfl⟩
  · cases command
    case serverSend keyId plaintext =>
      cases related
      exact (closed_couple _ before).mono fun _ _ equal => equal ▸ ⟨rfl, rfl⟩
    case beaconSend owner plaintext =>
      cases related
      exact (closed_couple _ before).mono fun _ _ equal => equal ▸ ⟨rfl, rfl⟩
    all_goals exact .pure _ _ ⟨related, rfl⟩

/-- The actual terminal service preserves the native reply relation and the complete shared public state, without a fixed reservation outcome. -/
theorem native_couple (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : Spec.Domain) (before : E) :
    Coupled WorldRel (fun left right => SpecRel query left.1 right.1 ∧ left.2 = right.2)
      ((native env reserve query).run before) ((native env reserve query).run before) := by
  simp only [native, StateT.run_bind]
  refine (PqxdhRecordLiftHiding.native_couple env query before).bind ?_
  rintro ⟨first, left⟩ ⟨second, right⟩ ⟨reply, state⟩
  dsimp only at state
  subst right
  exact post_couple reserve query first second reply left

/-- The full mode-P ledger, including test and fresh sampling, remains coupled around stateful post-send allocation. -/
theorem world_couple (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) :
    Coupled WorldRel ResultRel (program env reserve crypto codec serverKid bounds .P adversary)
      (program env reserve crypto codec serverKid bounds .P adversary) := by
  unfold program
  refine (Coupled.simulateQ (Rr := EqRel) _ _ (fun query => Coupled.query (Rr := WorldRel) (.inr (.inl (.inl query))))
    (Coupled.refl env.start eqRel_eq (Ro := Eq) fun _ => rfl)).bind fun born _ same => ?_
  cases same
  rcases born with _ | ⟨created, initial⟩
  · exact .pure _ _ trivial
  · refine (Coupled.query (Rr := WorldRel) (.inl created)).bind fun _ _ _ => ?_
    refine (Coupled.simulateQ_run _ _ Eq (fun query left _ same => same ▸ native_couple env reserve query left)
      (PqxdhRecordLiftHiding.wrap_couple crypto codec serverKid bounds adversary) initial initial rfl).bind
        fun first second related => ?_
    exact .pure _ _ ⟨rfl, related.1.1, related.1.2, related.2⟩

/-- The same gated client is used under every real, random, replay and chain policy. -/
noncomputable def client (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :=
  CborRecordWorldClient.client (program env reserve crypto codec serverKid bounds mode adversary)

/-- The actual common-state capacity gate commutes with length-preserving hidden-plaintext replacement in the random-record world. -/
theorem ctx_couple {ι KemSK : Type} {base : OracleSpec ι}
    (replaceFirst replaceSecond : Pqxdh.Bytes → Pqxdh.Bytes)
    (lengths : ∀ plaintext, (replaceFirst plaintext).length = (replaceSecond plaintext).length)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKid : U64) (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) :
    Coupled EqRel (fun first second =>
      (ResultRel first.1.1 second.1.1 ∧ first.1.2 = second.1.2) ∧ PqxdhRecordLiftHiding.PrivRel first.2 second.2)
      (PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) replaceFirst setup codec route
        (client env reserve setup.source.crypto codec serverKid bounds .P adversary))
      (PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) replaceSecond setup codec route
        (client env reserve setup.source.crypto codec serverKid bounds .P adversary)) :=
  Coupled.simulateQ_run _ _ PqxdhRecordLiftHiding.PrivRel
    (PqxdhRecordLiftHiding.interpreter_couple replaceFirst replaceSecond lengths setup codec)
    (PqxdhRecordLiftHiding.schedule_couple _ route
      (CborRawRecordHiding.client_couple (world_couple env reserve setup.source.crypto codec serverKid bounds adversary)) _)
    _ _ ⟨rfl, fun _ => rfl⟩

/-- The full hiding observation, including the platform retry state, has exactly the same distribution after hidden plaintext replacement. -/
theorem hiding_replace {ι KemSK : Type} {base : OracleSpec ι}
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKid : U64) (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X)
    (replaceFirst replaceSecond : Pqxdh.Bytes → Pqxdh.Bytes)
    (lengths : ∀ plaintext, (replaceFirst plaintext).length = (replaceSecond plaintext).length) :
    (fun result => PqxdhRecordLiftIdeal.hidingView (PqxdhRecordLiftIdeal.ctxView result)) <$>
      PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) replaceFirst setup codec route
        (client env reserve setup.source.crypto codec serverKid bounds .P adversary) =
    (fun result => PqxdhRecordLiftIdeal.hidingView (PqxdhRecordLiftIdeal.ctxView result)) <$>
      PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) replaceSecond setup codec route
        (client env reserve setup.source.crypto codec serverKid bounds .P adversary) :=
  (ctx_couple replaceFirst replaceSecond lengths setup codec route env reserve serverKid bounds adversary).map_eq _ _
    fun first second related => PqxdhRecordLiftHiding.hidingView_rel first second related

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.closed_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.closed_couple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.post_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.post_couple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.native_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.native_couple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.world_couple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.ctx_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.ctx_couple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.hiding_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface.hiding_replace
