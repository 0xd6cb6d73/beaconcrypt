import BeaconcryptCore.Computational.PqxdhInitialResponseService

/-!
The current authenticated post-root scheduler forwards its exact private Beacon initializer request to the common64-byte service. The root request, all preparation callbacks, actual optional opening, sequence-one/binding checks, whole Beacon installation and complete identity/shared state retain their original order and interfaces. The actual source specialization changes no public HKDF or other callback.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialServicePost
open PqxdhInitialResponseService PqxdhPhase2SourceAux PqxdhJointKdfGame PqxdhKemIndCca
open PqxdhPhase1AcceptanceOracle
open PqxdhJointIdentity PqxdhEd25519EufCma PqxdhPrivateKemSource PqxdhChallengeSecretRouting
variable {ι M P I D K X Response A : Type} {baseSpec : OracleSpec ι} {S B : Nat}

abbrev RunSpec (baseSpec : OracleSpec ι) := PqxdhInitialResponseService.Spec (LocalPostSpec baseSpec)

noncomputable def handles
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhPhase2PostScheduler.SharedSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (SharedState A × BareState count) (OracleComp (RunSpec baseSpec)))
  | .inr (.inr (.initial request)) => fun state => do
      let response ← initial request
      pure (response, state)
  | query => fun state => simulateQ original
      ((PqxdhPhase2PostScheduler.handles attachedVerify primitives count fixed localImpl challenge query).run state)

/-- The current target Beacon callback consumes the exact real64 initializer response at its original private position, preserving both complete private states. -/
theorem handles_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext)
    (query : (PqxdhPhase2PostScheduler.SharedSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)).Domain)
    (state : SharedState A × BareState count) :
    simulateQ (source fixed) ((handles attachedVerify primitives count fixed localImpl challenge query).run state) =
      (PqxdhPhase2PostScheduler.handles (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl challenge query).run state := by
  cases query with
  | inl query => exact original_program fixed _
  | inr query =>
    cases query with
    | inl query => exact original_program fixed _
    | inr query =>
      cases query with
      | root request => exact original_program fixed _
      | application request => exact original_program fixed _
      | initial request =>
        simp [handles, StateT.run, initial, source, OracleSpec.query, PqxdhPhase2PostScheduler.handles,
          QueryImpl.compose, PqxdhPhase2SharedKemHandles.full, PqxdhBeaconPhase2Routed.handles,
          PqxdhBeaconPhase2Routed.sharedAux]
        have exactInitial := PqxdhPhase2SourceAux.initial_complete (baseSpec := baseSpec)
          attachedVerify primitives count fixed localImpl request state
        simp only [StateT.run] at exactInitial
        rw [exactInitial]
        rfl

/-- The entire opaque Beacon owner program keeps its original result and complete shared/identity state through the initializer service. -/
theorem handles_program {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext)
    (work : OracleComp (PqxdhPhase2PostScheduler.SharedSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)) Result)
    (state : SharedState A × BareState count) :
    simulateQ (source fixed) ((simulateQ (handles attachedVerify primitives count fixed localImpl challenge) work).run state) =
      (simulateQ (PqxdhPhase2PostScheduler.handles (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl challenge) work).run state :=
  simulateQ_StateT_compose _ _ _ (handles_source attachedVerify primitives count fixed localImpl challenge) work state

noncomputable def finish
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhPhase2LiveFinish.FinishSpec B)
      (StateT (PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
        (OracleComp (RunSpec baseSpec)))
  | .finish index raw => fun before => PqxdhPhase2PostScheduler.installed index before <$>
      (simulateQ (handles attachedVerify primitives count fixed localImpl challenge)
        (PqxdhBeaconPhase2Shared.owner decode raw (before.1.roles.1.2 index))).run
          (before.1.primitive, before.2)

set_option backward.isDefEq.respectTransparency false in
/-- Beacon post-root initialization, raw opening, sequence/binding admission and whole-owner installation occur in the exact original order with every private field retained. -/
theorem finish_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    simulateQ (source fixed) ((finish attachedVerify primitives count fixed localImpl challenge decode query).run state) =
      (PqxdhPhase2PostScheduler.targetFinish (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl challenge decode query).run state := by
  cases query with
  | finish index raw =>
      simpa only [finish, PqxdhPhase2PostScheduler.targetFinish, StateT.run, simulateQ_map] using
        congrArg (Functor.map (PqxdhPhase2PostScheduler.installed index state))
          (handles_program attachedVerify primitives count fixed localImpl challenge
            (PqxdhBeaconPhase2Shared.owner decode raw (state.1.roles.1.2 index)) (state.1.primitive, state.2))

noncomputable def target
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhPhase2SourceScheduler.Spec baseSpec S B)
      (StateT (PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
        (OracleComp (RunSpec baseSpec)))
  | .inl query => fun state => simulateQ original
      ((PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge
        (.inl query)).run state)
  | .inr query => finish attachedVerify primitives count fixed localImpl challenge decode query

/-- All original record/public/reveal and selector calls remain unchanged; only actual Beacon completion exposes its private initializer callback. -/
theorem target_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext)
    (query : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    simulateQ (source fixed) ((target attachedVerify primitives count fixed localImpl writer sender route decode challenge query).run state) =
      (PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge query).run state := by
  cases query with
  | inl query => exact original_program fixed _
  | inr query => exact finish_source attachedVerify primitives count fixed localImpl challenge decode query state

/-- The entire original adaptive post-root schedule preserves complete live, identity and shared state under the common initializer source interpretation. -/
theorem target_program {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext)
    (work : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    simulateQ (source fixed) ((simulateQ (target attachedVerify primitives count fixed localImpl writer sender route decode challenge) work).run state) =
      (simulateQ (PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge) work).run state :=
  simulateQ_StateT_compose _ _ _ (target_source attachedVerify primitives count fixed localImpl writer sender route decode challenge) work state

/-- On the same explicitly good KEM sample used by the authenticated-root source bridge, the complete actual native Beacon finish equals the new initializer-service interpretation. -/
theorem finish_native {KemSK : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (shared : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some shared)) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    (PqxdhPhase2PostScheduler.nativeFinish attachedVerify primitives count fixed localImpl baseImpl kem secret decode query).run state =
      simulateQ (PqxdhPhase2PostScheduler.interpretation fixed baseImpl kem secret challenge)
        (simulateQ (source fixed) ((finish attachedVerify primitives count fixed localImpl challenge decode query).run state)) := by
  rw [finish_source, PqxdhPhase2PostScheduler.interpretation, QueryImpl.simulateQ_compose]
  exact PqxdhPhase2PostScheduler.finish_actual attachedVerify primitives count fixed localImpl baseImpl kem secret
    challenge shared agreement decode query state

end BeaconcryptCore.Computational.PqxdhInitialServicePost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServicePost.handles_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServicePost.handles_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServicePost.handles_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServicePost.handles_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServicePost.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServicePost.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServicePost.target_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServicePost.target_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServicePost.target_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServicePost.target_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServicePost.finish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServicePost.finish_native
