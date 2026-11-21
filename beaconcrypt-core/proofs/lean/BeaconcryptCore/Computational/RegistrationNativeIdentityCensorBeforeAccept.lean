-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction

/-! The reduction stops before its fixed public accept ordinal and observes the submitted packet as an upper bound on successful authentication. Earlier parsed failures and all attempted bundles retain the unchanged source callback semantics. No private bad-accept selector or challenged seed is a constructor argument. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBeforeAccept
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPublicClient (ClientState Stop)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityAdaptiveHashCapture (Candidate)
open PqxdhJointIdentity (PublicIdentity Forgery)
variable {S Value Auxiliary : Type}
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Spec := RegistrationNativeIdentityCensorOperational.Spec

def step (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) :
    QueryImpl TypedSpec (StateT (ClientState S) (OracleComp Spec))
  | .inr (.accept packet), before =>
      if before.2 = accept then pure (defaults (.inr (.accept packet)), before)
      else (RegistrationNativeIdentityCensorPublicClient.step selected bundle placeholder frontend (.inr (.accept packet))).run before
  | query, before => (RegistrationNativeIdentityCensorPublicClient.step selected bundle placeholder frontend query).run before

def freeze (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) :
    QueryImpl TypedSpec (StateT (ClientState S × Option Stop) (OracleComp Spec)) :=
  RegistrationNativeMldsaStop.freeze (step selected bundle accept placeholder frontend defaults)
    (RegistrationNativeIdentityCensorPublicClient.observe accept) defaults

/-- The selected public accept position submits no callback or hash query. Its current packet and exact preceding snapshot are retained. -/
theorem before_accept (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (packet : beaconcrypt_core.registration.InitPacket) (before : ClientState S) (chosen : before.2 = accept) :
    (freeze selected bundle accept placeholder frontend defaults (.inr (.accept packet))).run (before, none) =
      pure (defaults (.inr (.accept packet)), (before, some (.attempted packet (defaults (.inr (.accept packet)))))) := by
  simp only [freeze, RegistrationNativeMldsaStop.freeze, RegistrationNativeMldsaStop.monitor, StateT.run,
    step, chosen, ite_true, pure_bind, RegistrationNativeIdentityCensorPublicClient.observe, Option.orElse_none]

def program (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec Value)
    (initial : S) (knownInputs : List Pqxdh.Bytes) :
    OracleComp RegistrationNativeIdentityCensorCompiler.Spec
      (Value × (RegistrationNativeIdentityCensorPublicClient.ClientState S × Option RegistrationNativeIdentityCensorPublicClient.Stop)) :=
  simulateQ (RegistrationNativeIdentityCensorOperational.erase placeholder)
    ((simulateQ (freeze selected bundle accept placeholder frontend defaults) work).run
      (((initial, ({knownInputs := knownInputs} : Mode)), 0), none))

/-- Either an earlier recognized public input or the actual retained accept packet supplies the concrete field signature; the reduction never needs the canonical private reply. -/
def client (primitives : PqxdhJointIdentity.Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : PublicIdentity → OracleComp TypedSpec Value)
    (initial : S) (knownInputs : List Pqxdh.Bytes) (identity : PublicIdentity) :
    OracleComp RegistrationNativeIdentityCensorCompiler.Spec (Option (Candidate primitives identity)) :=
  (fun captured => match captured with
    | .inl recognized => some recognized
    | .inr returned => RegistrationNativeIdentityCensorStoppedReduction.result primitives identity returned) <$>
      RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityCensorRecognition.recognize primitives identity)
        (program selected bundle accept placeholder frontend defaults (work identity) initial knownInputs)

/-- One ordinary joint Ed/static-DH weak-EUF advantage bounds the selected valid-field event of this explicit stopped typed client, including public hash recognition before the fixed accept. -/
theorem bound (primitives : PqxdhJointIdentity.Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (fallback : Forgery)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : PublicIdentity → OracleComp TypedSpec Value)
    (initial : S) (knownInputs : List Pqxdh.Bytes)
    (protocol : PublicIdentity → QueryImpl PqxdhJointPhase1Reports.ProtocolSpec
      (StateT Auxiliary (OracleComp PqxdhJointIdentity.AdversarySpec)))
    (cache : RegistrationNativeIdentityCensorRecognition.Cache) (before : Auxiliary) :
    Pr{let accepted ← (RegistrationNativeIdentityCensorRecognition.game primitives placeholder protocol
      (client primitives selected bundle accept placeholder frontend defaults work initial knownInputs) cache before)}[accepted = true] ≤
      PqxdhJointIdentity.advantage primitives
        (RegistrationNativeIdentityAdaptiveCensor.reduction placeholder fallback
          (RegistrationNativeIdentityCensorRecognition.work primitives protocol
            (client primitives selected bundle accept placeholder frontend defaults work initial knownInputs) cache before)) :=
  RegistrationNativeIdentityCensorRecognition.bound primitives placeholder fallback protocol
    (client primitives selected bundle accept placeholder frontend defaults work initial knownInputs) cache before

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBeforeAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBeforeAccept.before_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBeforeAccept.before_accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBeforeAccept.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBeforeAccept.bound
