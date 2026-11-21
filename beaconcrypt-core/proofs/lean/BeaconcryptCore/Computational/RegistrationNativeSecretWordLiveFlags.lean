-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterChecked

/-! Actual checked preparation stores only valid descriptor flags. Because its optional input function is fixed throughout an execution, every previously successful descriptor remains prepared through all later checked root, KEM, signing, record and World operations. No preservation callback is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordInterpreter (State Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def Valid (input : Message → Option Key) (before : State n KemSK) : Prop :=
  ∀ message, before.flags message = true → (input message).isSome = true

def Keeps (before after : State n KemSK) : Prop :=
  ∀ message, before.flags message = true → after.flags message = true

/-- The actual combined cold initialization has no prepared descriptor. -/
theorem initial (input : Message → Option Key) (before : RegistrationNativePublicInterpreter.State n KemSK)
    (provider : RegistrationNativeSecretWordKemProvider.State KemSK) :
    Valid input (RegistrationNativeSecretWordInterpreter.initial before provider) := by
  intro message impossible
  cases impossible

/-- Every supported actual checked preparation returns its own queried name and stores that precise live receipt. -/
theorem prepare_receipt (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (message reference : Message) (before after : State n KemSK)
    (supported : (some reference, after) ∈ support
      ((handlerChecked setup wire route sign input inside provider (.inl (.inl message))).run before)) :
    reference = message ∧ after.flags reference = true ∧ (input reference).isSome = true := by
  simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.roots, StateT.run,
    RegistrationNativeSecretWordServiceChecked.checked, RegistrationNativeSecretWordService.handler, map_pure, mem_support_pure_iff] at supported
  cases formed : input message with
  | none => simp only [formed, Option.map_none] at supported; cases supported
  | some key =>
      simp only [formed, Option.map_some, Option.isSome_some] at supported
      cases supported
      simp only [Function.update_self, Option.isSome_some, formed, and_true]

private def IsPrepare : (Spec n KemSK).Domain → Prop
  | .inl (.inl _) => True
  | _ => False

private theorem unchanged (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (query : (Spec n KemSK).Domain) (before : State n KemSK) (free : ¬ IsPrepare query)
    (result : (Spec n KemSK).Range query × State n KemSK)
    (supported : result ∈ support ((handlerChecked setup wire route sign input inside provider query).run before)) :
    result.2.flags = before.flags := by
  rcases query with (message | (message | common) | kem) | record
  · exact False.elim (free trivial)
  · simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.roots, StateT.run,
      RegistrationNativeSecretWordServiceChecked.checked] at supported
    cases formed : input message with
    | none =>
        simp only [formed, map_pure, support_pure] at supported
        subst result
        rfl
    | some key =>
        simp only [formed, Functor.map_map, support_map] at supported
        obtain ⟨output, _possible, equal⟩ := supported
        cases equal
        rfl
  · simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.handler,
      RegistrationNativeSecretWordInterpreter.ordinary, StateT.run, support_map] at supported
    obtain ⟨output, _possible, equal⟩ := supported
    cases equal
    rfl
  · simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.handler,
      RegistrationNativeSecretWordInterpreter.routed, StateT.run, support_map] at supported
    obtain ⟨output, _possible, equal⟩ := supported
    cases equal
    rfl
  · simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.handler,
      RegistrationNativeSecretWordInterpreter.ordinary, StateT.run, support_map] at supported
    obtain ⟨output, _possible, equal⟩ := supported
    cases equal
    rfl

/-- Every actual checked callback preserves all earlier live receipts and stores only descriptors whose fixed optional input is valid. -/
theorem query_receipts (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (query : (Spec n KemSK).Domain) (before : State n KemSK) (valid : Valid input before)
    (result : (Spec n KemSK).Range query × State n KemSK)
    (supported : result ∈ support ((handlerChecked setup wire route sign input inside provider query).run before)) :
    Valid input result.2 ∧ Keeps before result.2 := by
  by_cases preparing : IsPrepare query
  · rcases query with (message | (message | common) | kem) | record
    all_goals try cases preparing
    simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.roots, StateT.run,
      RegistrationNativeSecretWordServiceChecked.checked, RegistrationNativeSecretWordService.handler,
      map_pure, support_pure] at supported
    subst result
    constructor
    · intro other active
      by_cases same : other = message
      · subst other
        simpa only [Function.update_self] using active
      · apply valid other
        simpa only [Function.update_of_ne same] using active
    · intro other stored
      by_cases same : other = message
      · subst other
        simpa only [Function.update_self] using valid message stored
      · simpa only [Function.update_of_ne same] using stored
  · have kept := unchanged setup wire route sign input inside provider query before preparing result supported
    constructor
    · intro message active
      exact valid message (kept ▸ active)
    · intro message stored
      exact kept.symm ▸ stored

/-- Every supported complete adaptive checked program retains valid flags and all previously prepared descriptors. -/
theorem program_receipts (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK) (valid : Valid input before)
    (result : Value × State n KemSK)
    (supported : result ∈ support ((simulateQ (handlerChecked setup wire route sign input inside provider) work).run before)) :
    Valid input result.2 ∧ Keeps before result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure] at supported
      subst result
      exact ⟨valid, fun _ stored => stored⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, stepped, later⟩ := supported
      have first := query_receipts setup wire route sign input inside provider query before valid middle stepped
      have last := ih middle.1 middle.2 first.1 later
      exact ⟨last.1, fun message stored => last.2 message (first.2 message stored)⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags.prepare_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags.prepare_receipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags.query_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags.query_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags.program_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags.program_receipts
