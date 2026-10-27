-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication

/-! Pure response representations commute with the original Phase-2 source program. The interface equations retain every optional callback and its complete monadic state; they assert no cryptographic property. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborResponseRepresentation
open PqxdhBeaconPhase2Preparation (Bytes Inputs Prepared)
variable {I D K X Response Response' : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def inputs (represent : Response → Response') (value : Inputs Response) : Inputs Response' :=
  ⟨represent value.response, value.ciphertext, value.ephemeral, value.finishInputs⟩

def prepared (represent : Response → Response') (value : Prepared Response) : Prepared Response' :=
  ⟨represent value.response, value.ciphertext, value.ephemeral, value.candidate⟩

structure PreparationCalls (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response') m)
    (oldRaw newRaw : Bytes) : Prop where
  decode : next (.decode newRaw) = Option.map represent <$> prior (.decode oldRaw)
  ciphertext : ∀ response, next (.ciphertext (represent response)) = prior (.ciphertext response)
  ephemeral : ∀ response, next (.ephemeral (represent response)) = prior (.ephemeral response)
  serverIdentity : ∀ response, next (.serverIdentity (represent response)) = prior (.serverIdentity response)
  publicConversion : ∀ point, next (.publicConversion point) = prior (.publicConversion point)
  privateConversion : ∀ identity, next (.privateConversion identity) = prior (.privateConversion identity)
  decapsulate : ∀ value key, next (.decapsulate value key) = prior (.decapsulate value key)
  dhPair : ∀ pair point, next (.dhPair pair point) = prior (.dhPair pair point)
  dhIdentity : ∀ identity point, next (.dhIdentity identity point) = prior (.dhIdentity identity point)
  assignedId : ∀ response, next (.assignedId (represent response)) = prior (.assignedId response)
  eraseShared : ∀ shared, next (.eraseShared shared) = prior (.eraseShared shared)

theorem collect (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response') m)
    (oldRaw newRaw : Bytes) (calls : PreparationCalls represent prior next oldRaw newRaw)
    (identity : I) (prekey oneTime : D) (kem : K) :
    simulateQ next (PqxdhBeaconPhase2Preparation.collect identity prekey oneTime kem newRaw) =
      Option.map (inputs represent) <$>
        simulateQ prior (PqxdhBeaconPhase2Preparation.collect identity prekey oneTime kem oldRaw) := by
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, OptionT.run_monadLift, Option.elimM, simulateQ_bind, simulateQ_spec_query,
    calls.decode, map_bind, bind_map_left]
  apply bind_congr
  rintro (_ | response)
  all_goals repeat' (
    simp only [Option.map_none, Option.map_some, Option.elim_none, Option.elim_some,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_pure, map_bind,
      calls.ciphertext, calls.ephemeral, calls.serverIdentity, calls.publicConversion,
      calls.privateConversion, calls.decapsulate, calls.dhPair, calls.dhIdentity,
      calls.assignedId, inputs]
    first | rfl | (apply bind_congr; intro reply; cases reply))
  all_goals simp only [Option.map_none, Option.map_some, Option.elim_none, Option.elim_some,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_pure, map_bind, calls.assignedId, inputs]

theorem afterInputs (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response') m)
    (oldRaw newRaw : Bytes) (calls : PreparationCalls represent prior next oldRaw newRaw)
    (control : pqxdh.BeaconInitSent) (value : Inputs Response) :
    simulateQ next (PqxdhBeaconPhase2Preparation.afterInputs control (inputs represent value)) =
      Option.map (prepared represent) <$>
        simulateQ prior (PqxdhBeaconPhase2Preparation.afterInputs control value) := by
  simp only [PqxdhBeaconPhase2Preparation.afterInputs, inputs, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, calls.eraseShared, map_bind]
  cases PqxdhBeaconPhase2Preparation.normalPrepare control value.finishInputs <;> simp [prepared]

theorem prepare (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response') m)
    (oldRaw newRaw : Bytes) (calls : PreparationCalls represent prior next oldRaw newRaw)
    (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D) (kem : K) :
    simulateQ next (PqxdhBeaconPhase2Preparation.prepare control identity prekey oneTime kem newRaw) =
      Option.map (prepared represent) <$>
        simulateQ prior (PqxdhBeaconPhase2Preparation.prepare control identity prekey oneTime kem oldRaw) := by
  simp only [PqxdhBeaconPhase2Preparation.prepare, simulateQ_bind,
    collect represent prior next oldRaw newRaw calls, map_bind, bind_map_left]
  apply bind_congr
  rintro (_ | value)
  all_goals simp only [Option.map_none, Option.map_some, simulateQ_pure, map_pure,
    afterInputs represent prior next oldRaw newRaw calls]

structure TailCalls (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response') m) : Prop where
  primitive : ∀ query, next (.inl query) = prior (.inl query)
  root : ∀ input, next (.inr (.root input)) = prior (.inr (.root input))
  initial : ∀ request, next (.inr (.initial request)) = prior (.inr (.initial request))
  application : ∀ response, next (.inr (.application (represent response))) = prior (.inr (.application response))

theorem raw_calls (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response') m)
    (calls : TailCalls represent prior next) :
    next ∘ₛ PqxdhBeaconPhase2Publication.rawLift =
      prior ∘ₛ PqxdhBeaconPhase2Publication.rawLift := by
  funext query
  simp only [QueryImpl.compose, PqxdhBeaconPhase2Publication.rawLift,
    simulateQ_spec_query, calls.primitive]

theorem afterRoot (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response') m)
    (calls : TailCalls represent prior next) (decode : RawCtxReceive.FrameDecoder)
    (value : Prepared Response) (root : PqxdhBeaconPhase2Preparation.Word32) :
    simulateQ next (PqxdhBeaconPhase2Publication.afterRoot decode (prepared represent value) root) =
      simulateQ prior (PqxdhBeaconPhase2Publication.afterRoot decode value root) := by
  simp only [PqxdhBeaconPhase2Publication.afterRoot, PqxdhBeaconPhase2Publication.initialRun,
    prepared, simulateQ_bind, simulateQ_spec_query, calls.initial, calls.application]
  simp only [simulateQ_pure]
  apply bind_congr
  intro kernel
  apply bind_congr
  rintro (_ | raw)
  all_goals simp only [simulateQ_bind, simulateQ_pure, ← QueryImpl.simulateQ_compose,
    raw_calls represent prior next calls]

theorem tail (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response') m)
    (calls : TailCalls represent prior next) (decode : RawCtxReceive.FrameDecoder)
    (value : Prepared Response) :
    simulateQ next (PqxdhBeaconPhase2Publication.tail decode (prepared represent value)) =
      simulateQ prior (PqxdhBeaconPhase2Publication.tail decode value) := by
  simp only [PqxdhBeaconPhase2Publication.tail, prepared, simulateQ_bind,
    simulateQ_spec_query, calls.root]
  apply bind_congr
  rintro (_ | root)
  · simp only [simulateQ_pure]
  · exact afterRoot represent prior next calls decode value root

/-- The complete source finish preserves its actual optional reply and all interpreted state under response representation. -/
theorem owner (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Publication.FullSpec I D K X Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Publication.FullSpec I D K X Response') m)
    (oldRaw newRaw : Bytes)
    (preCalls : PreparationCalls represent
      (prior ∘ₛ PqxdhBeaconPhase2Publication.preLift) (next ∘ₛ PqxdhBeaconPhase2Publication.preLift) oldRaw newRaw)
    (tailCalls : TailCalls represent
      (prior ∘ₛ PqxdhBeaconPhase2Publication.tailLift) (next ∘ₛ PqxdhBeaconPhase2Publication.tailLift))
    (decode : RawCtxReceive.FrameDecoder) (state : PqxdhBeaconPhase2Preparation.State I D K) :
    simulateQ next (PqxdhBeaconPhase2Publication.owner decode newRaw state) =
      simulateQ prior (PqxdhBeaconPhase2Publication.owner decode oldRaw state) := by
  cases phase : state.beacon.phase <;>
    simp only [PqxdhBeaconPhase2Publication.owner, phase, simulateQ_pure]
  rename_i control prekey oneTime kem
  simp only [simulateQ_bind, ← QueryImpl.simulateQ_compose]
  rw [prepare represent _ _ oldRaw newRaw preCalls control state.beacon.identity prekey oneTime kem]
  simp only [bind_map_left]
  apply bind_congr
  rintro (_ | value)
  all_goals simp only [Option.map_none, Option.map_some, simulateQ_bind, simulateQ_pure,
    ← QueryImpl.simulateQ_compose, tail represent _ _ tailCalls]

/-- Expanding CTX into its actual optional hash and AEAD callbacks preserves the complete response-representation equality. -/
theorem native_owner (represent : Response → Response')
    (prior : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response) m)
    (next : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response') m)
    (oldRaw newRaw : Bytes)
    (preCalls : PreparationCalls represent
      ((prior ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ PqxdhBeaconPhase2Publication.preLift)
      ((next ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ PqxdhBeaconPhase2Publication.preLift) oldRaw newRaw)
    (tailCalls : TailCalls represent
      ((prior ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ PqxdhBeaconPhase2Publication.tailLift)
      ((next ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ PqxdhBeaconPhase2Publication.tailLift))
    (decode : RawCtxReceive.FrameDecoder) (state : PqxdhBeaconPhase2Preparation.State I D K) :
    simulateQ next (PqxdhBeaconPhase2Publication.nativeOwner decode newRaw state) =
      simulateQ prior (PqxdhBeaconPhase2Publication.nativeOwner decode oldRaw state) := by
  simp only [PqxdhBeaconPhase2Publication.nativeOwner, ← QueryImpl.simulateQ_compose]
  exact owner represent _ _ oldRaw newRaw preCalls tailCalls decode state

end BeaconcryptCore.Computational.CborResponseRepresentation

/-- info: 'BeaconcryptCore.Computational.CborResponseRepresentation.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseRepresentation.collect
/-- info: 'BeaconcryptCore.Computational.CborResponseRepresentation.afterInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseRepresentation.afterInputs
/-- info: 'BeaconcryptCore.Computational.CborResponseRepresentation.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseRepresentation.prepare
/-- info: 'BeaconcryptCore.Computational.CborResponseRepresentation.raw_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseRepresentation.raw_calls
/-- info: 'BeaconcryptCore.Computational.CborResponseRepresentation.afterRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseRepresentation.afterRoot
/-- info: 'BeaconcryptCore.Computational.CborResponseRepresentation.tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseRepresentation.tail
/-- info: 'BeaconcryptCore.Computational.CborResponseRepresentation.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseRepresentation.owner
/-- info: 'BeaconcryptCore.Computational.CborResponseRepresentation.native_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborResponseRepresentation.native_owner
