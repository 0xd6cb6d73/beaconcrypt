-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRecognition
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient

/-! The template-indexed executable marker interpreter retains every public hash framing as a distinct alias-preserving symbolic key. Its ROM is simulated using ordinary public uniform queries; recognition and final submitted-field witnesses have one explicit ordinary joint weak-EUF bill. Physical source realization and native causal coverage remain separate exact joins. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition
open RegistrationNativeIdentityAdaptiveHashCapture (Candidate)
open PqxdhJointIdentity (PublicIdentity)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Auxiliary Value : Type}

abbrev Key := Pqxdh.Bytes ⊕ (Pqxdh.Bytes × Pqxdh.Bytes)
structure HashInput where
  message : Option Pqxdh.Bytes
  input : Key
abbrev HashSpec := HashInput →ₒ (CtxRomAuth.CtxDigest × Nat)
abbrev Spec := ((PqxdhJointPhase1Reports.ProtocolSpec + RegistrationNativeIdentityCensorCompiler.SelectSpec) +
  RegistrationNativeIdentityCensorCompiler.ScanSpec) + HashSpec
abbrev Cache := (Key →ₒ CtxRomAuth.CtxDigest).QueryCache

/-- Every actual hidden template retains its complete public framing. Omitted replies use only the known placeholder; no canonical signature or selected seed is captured. -/
def erase (placeholder : Ed25519Signature) : QueryImpl RegistrationNativeIdentityCensorOperational.Spec (OracleComp Spec)
  | .inl (.inl query) => Spec.query (.inl query)
  | .inl (.inr described) => Spec.query (.inr ⟨described.message, .inl (described.input.getD [])⟩)
  | .inr (.omitted _ _) => pure (some placeholder)
  | .inr (.template _ message leading trailing) => Spec.query (.inr ⟨message, .inr (leading, trailing)⟩)
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
  | .inr ⟨some message, .inl input⟩ =>
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

/-- The fixed public before-accept packet client is executable with template-indexed hashes and a known placeholder only. -/
def packetProgram {S : Type} (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (rawWork : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : S) (knownInputs : List Pqxdh.Bytes) :
    OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found) :=
  simulateQ (erase placeholder) (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults rawWork
    ((before, ({knownInputs := knownInputs} : RegistrationNativeIdentityCensorCompiler.Mode)), 0))

/-- A recognized public address or the original submitted packet supplies the candidate; the client never receives the hidden canonical bytes. -/
def packetClient {S : Type} (primitives : PqxdhJointIdentity.Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (rawWork : PublicIdentity → OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : S) (knownInputs : List Pqxdh.Bytes)
    (identity : PublicIdentity) : OracleComp Spec (Option (Candidate primitives identity)) :=
  (fun captured => match captured with
    | .inl recognized => some recognized
    | .inr returned => RegistrationNativeIdentityCensorPacketClient.candidate primitives identity returned) <$>
    RegistrationNativeIdentityRecognitionCapture.capture (recognize primitives identity)
      (packetProgram selected bundle accept placeholder frontend defaults (rawWork identity) before knownInputs)

/-- This is the explicit ordinary joint weak-EUF bill for the fixed public template-indexed before-accept client. No original causal-event inclusion or physical-ROM equality is assumed. -/
theorem before_accept_bound {S : Type} (primitives : PqxdhJointIdentity.Primitives)
    (selected bundle accept : Nat) (placeholder : Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (rawWork : PublicIdentity → OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (initial : S) (knownInputs : List Pqxdh.Bytes)
    (protocol : PublicIdentity → QueryImpl PqxdhJointPhase1Reports.ProtocolSpec (StateT Auxiliary (OracleComp Primitive)))
    (cache : Cache) (before : Auxiliary) :
    Pr{let accepted ← (game primitives placeholder protocol
      (packetClient primitives selected bundle accept placeholder frontend defaults rawWork initial knownInputs) cache before)}[accepted = true] ≤
      PqxdhJointIdentity.advantage primitives
        (RegistrationNativeIdentityAdaptiveCensor.reduction placeholder fallback
          (work primitives protocol (packetClient primitives selected bundle accept placeholder frontend defaults rawWork initial knownInputs) cache before)) :=
  bound primitives placeholder fallback protocol
    (packetClient primitives selected bundle accept placeholder frontend defaults rawWork initial knownInputs) cache before

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition.before_accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition.before_accept_bound
