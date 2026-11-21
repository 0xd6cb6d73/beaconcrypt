-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenPublication
import BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthOrder
import BeaconcryptCore.Computational.RegistrationNativeKemOpenLedger
import BeaconcryptCore.Computational.RegistrationNativeKemPublicationTrace

/-! Original raw publication history under the candidate provider records genuine reserved PQ fields and actual created indices. Later private births extend availability; no final target, ciphertext freshness or unchanged accepted-packet condition is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenBirth (borns)
open RegistrationNativeInterface (Entry)
open RegistrationNativeKemPublicationTrace (publication)
open PqxdhKemIndCca
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def Holds (wire : Wire) (pairs : List (MlKem768PublicKey × KemSK))
    (current : State n mlSource KemSK) (transcript : List Entry) : Prop :=
  ∀ entry ∈ transcript, ∀ index raw, publication entry = some (index, raw) →
    ∃ pair packet, pairs[index]? = some pair ∧ index < borns current ∧
      RegistrationNativeWire.readInit wire raw = some packet ∧ RegistrationNativeKemTarget.PacketKey packet pair.1

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool) (parsed : Nat)
local notation "step" => RegistrationNativeKemOpenLedger.step (n := n) setup checks wire route representation created credential selected pairs publicKey real parsed

/-- The actual complete original ledger step preserves every earlier genuine publication and proves the new raw bundle's native signed PQ payload. -/
theorem step_holds (readback : RegistrationNativeWire.InitReadBack wire) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (beforeLedger afterLedger : RegistrationNativeLedger.State)
    (before after : State n mlSource KemSK) (priorRoster : RegistrationNativeKemOpenRoster.Holds pairs before)
    (prior : Holds wire pairs before beforeLedger.transcript) (value : RegistrationNativeInterface.FullSpec.Range query)
    (supported : (some (value, afterLedger), after) ∈ support (((step bounds query beforeLedger).run).run before)) :
    RegistrationNativeKemOpenRoster.Holds pairs after ∧ Holds wire pairs after afterLedger.transcript := by
  have roster := RegistrationNativeKemOpenRosterRun.raw_work_holds setup checks wire route representation created credential
    selected pairs publicKey real parsed _ before after priorRoster (value, afterLedger) supported
  have growth := RegistrationNativeKemOpenBirthOrder.raw_work_mono setup checks wire route representation created credential
    selected pairs publicKey real parsed _ before after (value, afterLedger) supported
  refine ⟨roster, ?_⟩
  have old : Holds wire pairs after beforeLedger.transcript := by
    intro entry member index raw published
    obtain ⟨pair, packet, pairAt, active, decoded, key⟩ := prior entry member index raw published
    exact ⟨pair, packet, pairAt, active.trans_le growth, decoded, key⟩
  rw [RegistrationNativeKemOpenLedger.step_trace setup checks wire route representation created credential
    selected pairs publicKey real parsed bounds query beforeLedger afterLedger before after value supported]
  intro entry member index raw published
  rcases List.mem_append.mp member with earlier | newest
  · exact old entry earlier index raw published
  · have sameEntry : entry = ⟨query, value⟩ := by simpa only [List.mem_singleton] using newest
    subst entry
    cases query with
    | inr secrecy => cases published
    | inl query =>
        rw [RegistrationNativeKemOpenLedger.core_run, support_map] at supported
        obtain ⟨⟨reply, reached⟩, called, returned⟩ := supported
        cases reply with
        | none =>
            have impossible := congrArg Prod.fst returned
            simp only [Option.map_none, reduceCtorEq] at impossible
        | some reply =>
            have valueEq := congrArg (fun result => result.1.map Prod.fst) returned
            simp only [Option.map_some, Option.some.injEq] at valueEq
            change reply = value at valueEq
            subst value
            have stateEq := congrArg Prod.snd returned
            change reached = after at stateEq
            subst after
            cases query with
            | inl coin => cases published
            | inr command =>
                cases command with
                | bundle owner =>
                    cases reply with
                    | none => cases published
                    | some bytes =>
                        change some (owner, bytes) = some (index, raw) at published
                        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj published)
                        obtain ⟨pair, packet, pairAt, active, decoded, key⟩ :=
                          RegistrationNativeKemOpenPublication.bundle_key setup checks wire route representation created credential
                            selected pairs publicKey real parsed readback owner bytes before reached priorRoster called
                        exact ⟨pair, packet, pairAt, active.trans_le growth, decoded, key⟩
                | _ => cases published

end BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationTrace.step_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationTrace.step_holds
