import BeaconcryptCore.Computational.PqxdhPhase2NativeSource

/-!
The actual postchallenge auxiliary callbacks use their original local coins, shared CTX cache and complete joint identity state even when the public decapsulation interface blocks the challenge. Native Phase2 then agrees with the existing opaque shared-secret owner under one explicit per-key decapsulation program equality. The selected secret key appears only in the native interpretation; neither the auxiliary compiler nor the shared owner receives it. This operational equality does not assert zero KEM correctness error or a completed generated scheduler.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2PostSource
open PqxdhPhase2SourceAux PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhStatefulPhase1EufCma PqxdhInitializerSecrecy PqxdhChallengeSecretRouting
open PqxdhRootTableInitialization (rootArray)
variable {ι I D K X Response A KemSK : Type} {baseSpec : OracleSpec ι}

/-- The original blocked public postchallenge interpreter still forwards every actual local coin. -/
noncomputable def interpretation (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) : QueryImpl (MlKemCCAOracleSpec baseSpec) ProbComp :=
  kemAmbientImpl baseImpl ∘ₛ publicImpl kem secret challenge

/-- Blocking the public challenge ciphertext does not change any explicitly lifted local computation. -/
theorem coins {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (work : ProbComp Result) :
    simulateQ (interpretation baseImpl kem secret challenge) (ccaCoins work) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [ccaCoins, simulateQ_bind, simulateQ_spec_query]
      change ((unifSpec.query query : ProbComp _) >>= fun reply =>
        simulateQ (interpretation baseImpl kem secret challenge) (ccaCoins (next reply))) = _
      simp only [ih]

/-- The complete optional auxiliary result and both private poststates are the original source execution. -/
theorem auxiliary_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (query : (Spec I D K X Response).Domain)
    (state : SharedState A × BareState count) :
    simulateQ (interpretation baseImpl kem secret challenge)
      ((borrowedAux attachedVerify primitives count source localImpl query).run state) =
      (directAux attachedVerify primitives count source localImpl query).run state := by
  rw [borrowed_step, coins]

/-- The same arbitrary auxiliary client evaluates to its original adaptive source computation under the blocked interface. -/
theorem auxiliary_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (client : OracleComp (Spec I D K X Response) Result)
    (state : SharedState A × BareState count) :
    simulateQ (interpretation baseImpl kem secret challenge)
      ((simulateQ (borrowedAux attachedVerify primitives count source localImpl) client).run state) =
      (simulateQ (directAux attachedVerify primitives count source localImpl) client).run state := by
  rw [borrowed_complete, coins]

/-- Every actual native callback preserves its original result and full state after evaluating the blocked auxiliary interface. -/
theorem native_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (Option K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response).Domain)
    (state : SharedState A × BareState count) :
    simulateQ (kemAmbientImpl baseImpl)
      ((PqxdhBeaconPhase2Routed.native source kem secret challenge
        (borrowedAux attachedVerify primitives count source localImpl) query).run state) =
      (PqxdhPhase2NativeSource.native source baseImpl kem secret
        (directAux attachedVerify primitives count source localImpl) query).run state := by
  rcases query with (query | (query | query)) <;> cases query
  all_goals
    try
      exact (QueryImpl.simulateQ_compose _ _ _).symm.trans
        (auxiliary_step attachedVerify primitives count source localImpl baseImpl kem secret challenge _ state)
  case inl.decapsulate value key =>
    cases key with
    | none =>
        rw [show PqxdhBeaconPhase2Routed.native source kem secret challenge
          (borrowedAux attachedVerify primitives count source localImpl)
            (.inl (.decapsulate value none)) =
          liftM (Option.map rootArray <$>
            kem.decaps secret (PqxdhPhase2InputBytes.ciphertext value)) by rfl]
        rw [show PqxdhPhase2NativeSource.native source baseImpl kem secret
          (directAux attachedVerify primitives count source localImpl)
            (.inl (.decapsulate value none)) =
          liftM (Option.map rootArray <$> simulateQ (kemAmbientImpl baseImpl)
            (kem.decaps secret (PqxdhPhase2InputBytes.ciphertext value))) by rfl]
        simp only [StateT.run_monadLift, monadLift_self, bind_pure_comp, simulateQ_map]
    | some prior =>
        exact (QueryImpl.simulateQ_compose _ _ _).symm.trans
          (auxiliary_step attachedVerify primitives count source localImpl baseImpl kem secret challenge _ state)
  all_goals exact simulateQ_pure (kemAmbientImpl baseImpl) _

/-- Evaluating the actual routed native interface yields the same direct source handler. -/
theorem native_interpretation
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) :
    (kemAmbientImpl baseImpl).mapStateTBase
      (PqxdhBeaconPhase2Routed.native source kem secret challenge
        (borrowedAux attachedVerify primitives count source localImpl)) =
      PqxdhPhase2NativeSource.native source baseImpl kem secret
        (directAux attachedVerify primitives count source localImpl) := by
  exact funext (fun query => funext (fun state =>
    native_step attachedVerify primitives count source localImpl baseImpl kem secret challenge query state))

/-- Arbitrary adaptive native execution retains its complete result, source cache and identity history under the same postchallenge evaluation. -/
theorem native_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext)
    (client : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (Option K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response) Result)
    (state : SharedState A × BareState count) :
    simulateQ (kemAmbientImpl baseImpl)
      ((simulateQ (PqxdhBeaconPhase2Routed.native source kem secret challenge
        (borrowedAux attachedVerify primitives count source localImpl)) client).run state) =
      (simulateQ (PqxdhPhase2NativeSource.native source baseImpl kem secret
        (directAux attachedVerify primitives count source localImpl)) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, native_interpretation]

/-- On the explicit good decapsulation program equality, the actual native finish is the existing routed shared owner with the same complete private result. -/
theorem owner_actual
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State (PqxdhGeneratedBeaconState.IdentityHandle I) D (Option K))
    (state : SharedState A × BareState count) :
    (simulateQ (PqxdhPhase2NativeSource.native source baseImpl kem secret
      (directAux attachedVerify primitives count source localImpl))
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run state =
      simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (actualImpl source kem secret challenge)
          ((simulateQ (PqxdhBeaconPhase2Routed.handles source challenge
            (borrowedAux attachedVerify primitives count source localImpl))
            (PqxdhBeaconPhase2Shared.owner decode raw owner)).run state)) := by
  exact (native_complete attachedVerify primitives count source localImpl baseImpl kem secret challenge
    (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner) state).symm.trans
      (congrArg (simulateQ (kemAmbientImpl baseImpl))
        (PqxdhBeaconPhase2Routed.owner_actual source kem secret challenge supplied agreement
          (borrowedAux attachedVerify primitives count source localImpl) decode raw owner state))

/-- Every later private continuation receives the same optional reply, complete native owner, source cache and joint identity history. -/
theorem owner_continuation {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State (PqxdhGeneratedBeaconState.IdentityHandle I) D (Option K))
    (state : SharedState A × BareState count)
    (next : ((Option PqxdhBeaconPhase2Preparation.Bytes ×
      PqxdhBeaconPhase2Preparation.State (PqxdhGeneratedBeaconState.IdentityHandle I) D (Option K)) ×
      (SharedState A × BareState count)) → OracleComp (LocalPostSpec baseSpec) Result) :
    ((simulateQ (PqxdhPhase2NativeSource.native source baseImpl kem secret
      (directAux attachedVerify primitives count source localImpl))
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run state >>= fun result =>
        simulateQ (kemAmbientImpl baseImpl) (simulateQ (actualImpl source kem secret challenge) (next result))) =
      simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (actualImpl source kem secret challenge)
          ((simulateQ (PqxdhBeaconPhase2Routed.handles source challenge
            (borrowedAux attachedVerify primitives count source localImpl))
            (PqxdhBeaconPhase2Shared.owner decode raw owner)).run state >>= next)) := by
  rw [owner_actual attachedVerify primitives count source localImpl baseImpl kem secret challenge supplied agreement,
    simulateQ_bind, simulateQ_bind]

end BeaconcryptCore.Computational.PqxdhPhase2PostSource

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSource.coins' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSource.coins

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSource.auxiliary_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSource.auxiliary_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSource.auxiliary_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSource.auxiliary_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSource.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSource.native_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSource.native_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSource.native_interpretation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSource.native_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSource.native_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSource.owner_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSource.owner_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSource.owner_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSource.owner_continuation
