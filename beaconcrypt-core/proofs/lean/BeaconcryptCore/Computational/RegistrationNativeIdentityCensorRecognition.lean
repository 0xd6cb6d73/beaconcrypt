-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal
import BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicCtx

/-! The selected-callback compiler's explicit hash/scan requests yield certified signature witnesses. Its symbolic ROM is executed inside the ordinary joint-Ed adversary, using actual public uniform queries and retaining alias hits. Freshness is derived by the adaptive censor from the actual ordinary signing history. This is the primitive bill for the executable selected-callback client; native causal-event/source coverage is not assumed here and remains to be composed. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRecognition
open RegistrationNativeIdentityCensorCompiler (Spec)
open RegistrationNativeIdentityAdaptiveHashCapture (Candidate)
open PqxdhJointIdentity (PublicIdentity)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Auxiliary Value : Type}

abbrev Cache := RegistrationNativeIdentitySymbolicCtx.Cache
abbrev Ordinary := RegistrationNativeIdentityAdaptiveCensor.Spec
abbrev Primitive := PqxdhJointIdentity.AdversarySpec

def certifyScan (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity)
    (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes) : Option (Candidate primitives identity) :=
  match found : RegistrationNativeIdentityRecognitionJournal.scan primitives.verify identity.ed25519 message inputs with
  | none => none
  | some signature => some ⟨message, signature,
      RegistrationNativeIdentityRecognitionJournal.valid _ _ _ _ _ found⟩

/-- Both retroactive prefix scans and subsequent public hash submissions return the actual valid signature bytes. -/
def recognize (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) :
    Spec.Domain → Option (Candidate primitives identity)
  | .inl (.inr (message, inputs)) => certifyScan primitives identity message inputs
  | .inr ⟨some message, some input⟩ =>
      (RegistrationNativeIdentityAdaptiveHashCapture.certify primitives identity message input).map
        (fun signature => ⟨message, signature⟩)
  | _ => none

def capture (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) (work : OracleComp Spec Value) :
    OracleComp Spec (Option (Candidate primitives identity)) :=
  (fun result => match result with | .inl candidate => some candidate | .inr _ => none) <$>
    RegistrationNativeIdentityRecognitionCapture.capture (recognize primitives identity) work

/-- The source protocol router may keep independent-key state. The challenged seed is not an input to this compiler. -/
noncomputable def handler (protocol : QueryImpl PqxdhJointPhase1Reports.ProtocolSpec (StateT Auxiliary (OracleComp Primitive))) :
    QueryImpl Spec (StateT Cache (StateT Auxiliary (OracleComp Ordinary)))
  | .inl (.inl (.inl query)) => StateT.lift (fun before =>
      simulateQ RegistrationNativeIdentityAdaptiveCensor.ordinary ((protocol query).run before))
  | .inl (.inl (.inr message)) => StateT.lift (StateT.lift (Ordinary.query (.inr message)))
  | .inl (.inr _) => pure ()
  | .inr described => fun before => simulateQ
      (fun query => StateT.lift (Ordinary.query (.inl (.inl query)) : OracleComp Ordinary _))
      ((RegistrationNativeIdentitySymbolicRom.counted RegistrationNativeIdentitySymbolicCtx.sampler described.input).run before)

noncomputable def close (protocol : QueryImpl PqxdhJointPhase1Reports.ProtocolSpec (StateT Auxiliary (OracleComp Primitive)))
    (work : OracleComp Spec Value) (cache : Cache) (before : Auxiliary) : OracleComp Ordinary Value :=
  (fun result => result.1.1) <$> ((simulateQ (handler protocol) work).run cache).run before

def selected (policy : RegistrationNativeIdentityAdaptiveCensor.Policy) {primitives : PqxdhJointIdentity.Primitives}
    {identity : PublicIdentity} (candidate : Option (Candidate primitives identity)) : Bool :=
  candidate.any (fun chosen => policy.target == some chosen.1)

private theorem selected_valid (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity)
    (policy : RegistrationNativeIdentityAdaptiveCensor.Policy) (candidate : Option (Candidate primitives identity))
    (held : selected policy candidate = true) :
    RegistrationNativeIdentityAdaptiveCensor.recognized primitives identity
      (candidate.map (fun chosen => chosen.2.val)) policy = true := by
  cases returned : candidate with
  | none => simp only [selected, returned, Option.any_none, Bool.false_eq_true] at held
  | some chosen =>
      have target : policy.target = some chosen.1 := by
        simpa only [selected, returned, Option.any_some, beq_iff_eq] using held
      simp only [RegistrationNativeIdentityAdaptiveCensor.recognized, Option.map_some,
        target, Option.any_some, chosen.2.property]

noncomputable def work (primitives : PqxdhJointIdentity.Primitives)
    (protocol : PublicIdentity → QueryImpl PqxdhJointPhase1Reports.ProtocolSpec (StateT Auxiliary (OracleComp Primitive)))
    (client : (identity : PublicIdentity) → OracleComp Spec (Option (Candidate primitives identity)))
    (cache : Cache) (before : Auxiliary) (identity : PublicIdentity) : OracleComp Ordinary (Option Ed25519Signature) :=
  (fun candidate => candidate.map (fun chosen => chosen.2.val)) <$> close (protocol identity) (client identity) cache before

noncomputable def game (primitives : PqxdhJointIdentity.Primitives) (placeholder : Ed25519Signature)
    (protocol : PublicIdentity → QueryImpl PqxdhJointPhase1Reports.ProtocolSpec (StateT Auxiliary (OracleComp Primitive)))
    (client : (identity : PublicIdentity) → OracleComp Spec (Option (Candidate primitives identity)))
    (cache : Cache) (before : Auxiliary) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let result ← RegistrationNativeIdentityAdaptiveCensor.execute primitives seed placeholder
    (close (protocol (primitives.publicKeys seed)) (client (primitives.publicKeys seed)) cache before) {} []
  pure (selected result.1.2 result.1.1)

/-- Every selected recognized target has one ordinary joint weak-EUF bill, including recognition in an earlier known-input prefix. The actual omitted-sign history supplies freshness. -/
theorem bound (primitives : PqxdhJointIdentity.Primitives) (placeholder : Ed25519Signature)
    (fallback : PqxdhJointIdentity.Forgery)
    (protocol : PublicIdentity → QueryImpl PqxdhJointPhase1Reports.ProtocolSpec (StateT Auxiliary (OracleComp Primitive)))
    (client : (identity : PublicIdentity) → OracleComp Spec (Option (Candidate primitives identity)))
    (cache : Cache) (before : Auxiliary) :
    Pr{let accepted ← game primitives placeholder protocol client cache before}[accepted = true] ≤
      PqxdhJointIdentity.advantage primitives
        (RegistrationNativeIdentityAdaptiveCensor.reduction placeholder fallback (work primitives protocol client cache before)) := by
  apply le_trans (b := Pr{let accepted ← (RegistrationNativeIdentityAdaptiveCensor.observed primitives placeholder (work primitives protocol client cache before))}[accepted = true])
  · unfold game RegistrationNativeIdentityAdaptiveCensor.observed work
    simp only [RegistrationNativeIdentityAdaptiveCensor.execute, simulateQ_map, StateT.run_map, bind_map_left]
    apply prEvent_bind_mono_of_forall_le_of_support
    intro seed _
    apply prEvent_bind_mono_of_forall_le_of_support
    intro result _
    by_cases held : selected result.1.2 result.1.1 = true
    · have verified := selected_valid primitives (primitives.publicKeys seed) result.1.2 result.1.1 held
      simp only [prEvent_pure, held, verified, ite_true]
      exact le_rfl
    · simp only [prEvent_pure, held, Bool.false_eq_true, ite_false]
      exact zero_le
  · exact RegistrationNativeIdentityAdaptiveCensor.recognition_bound primitives placeholder fallback _

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRecognition
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRecognition.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRecognition.bound
