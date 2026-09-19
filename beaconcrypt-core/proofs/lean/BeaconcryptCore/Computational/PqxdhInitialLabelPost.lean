import BeaconcryptCore.Computational.PqxdhInitialFusedCompiler

/-!
The actual adaptive post-registration schedule compiles through the response-only initializer service. Ordinary record/reveal/public queries remain their original computations; every attempted Beacon finish uses the concrete fused compiler and complete original installation. The selected root is absent from the executable scheduler arguments and remains only in the separately interpreted private service.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialLabelPost
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhPhase2SourceAux
open PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Every original public-channel computation has zero private-root queries, including all caller-chosen public decapsulation attempts and sampling. -/
theorem public_no_root (work : OracleComp (MlKemCCAOracleSpec baseSpec) Result) :
    (PqxdhPhase2PostScheduler.publicWork work).IsQueryBoundP (IsPrivateRoot (baseSpec := baseSpec)) 0 := by
  apply RawCtxSourceOpen.simulate_bound PqxdhBeaconPhase2Routed.publicLift (fun _ => False)
    (IsPrivateRoot (baseSpec := baseSpec)) work 0 (isQueryBoundP_false _ _)
  intro request
  exact (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec)
    (p := IsPrivateRoot (baseSpec := baseSpec)) (.inl request) 0).mpr (by simp [IsPrivateRoot])

noncomputable def finish
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhPhase2LiveFinish.FinishSpec B)
      (StateT (PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
        (OracleComp PqxdhInitialLabelCompiler.Spec))
  | .finish index raw => fun before => PqxdhPhase2PostScheduler.installed index before <$>
      (simulateQ (PqxdhInitialFusedCompiler.compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
        (PqxdhInitialFusedOwner.owner decode raw (before.1.roles.1.2 index))).run (before.1.primitive, before.2)

set_option backward.isDefEq.respectTransparency false in
/-- Every attempted original Beacon finish preserves its complete live-role/shared/private installation under the response-only service, including failed and inactive attempts. -/
theorem finish_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((finish attachedVerify primitives count fixed localImpl baseImpl kem secret challenge decode query).run state) =
      simulateQ (rootPost fixed baseImpl kem secret challenge)
        ((PqxdhPhase2PostScheduler.targetFinish attachedVerify primitives count fixed localImpl challenge decode query).run state) := by
  cases query with
  | finish index raw =>
      simpa only [finish, PqxdhPhase2PostScheduler.targetFinish, StateT.run, simulateQ_map] using
        congrArg (Functor.map (PqxdhPhase2PostScheduler.installed index state))
          (PqxdhInitialFusedCompiler.owner_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
            decode raw (state.1.roles.1.2 index) (state.1.primitive, state.2))

noncomputable def target
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhPhase2SourceScheduler.Spec baseSpec S B)
      (StateT (PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
        (OracleComp PqxdhInitialLabelCompiler.Spec))
  | .inl query => fun state => PqxdhInitialLabelCompiler.coins
      (simulateQ (PqxdhInitialRootFreeCallbacks.publicOnly baseImpl kem secret challenge)
        ((PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge (.inl query)).run state))
  | .inr query => finish attachedVerify primitives count fixed localImpl baseImpl kem secret challenge decode query

set_option backward.isDefEq.respectTransparency false in
/-- Each ordinary original post request runs its unchanged source/public computation; the derived zero private-root count removes any need for a root-cache argument. -/
theorem public_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhProtocolSelector.Spec baseSpec S B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((target attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge (.inl query)).run state) =
      simulateQ (rootPost fixed baseImpl kem secret challenge)
        ((PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge (.inl query)).run state) := by
  rw [target, StateT.run, PqxdhInitialLabelCompiler.coins_source]
  apply (PqxdhInitialRootFreeCallbacks.root_free fixed baseImpl kem secret challenge _ _).symm
  cases query <;> exact public_no_root _

/-- All source/public traffic and attempted Beacon completions preserve their exact optional replies and complete scheduler state under the same initializer interface. -/
theorem step_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((target attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge query).run state) =
      simulateQ (rootPost fixed baseImpl kem secret challenge)
        ((PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge query).run state) := by
  cases query with
  | inl query => exact public_source attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge query state
  | inr query => exact finish_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge decode query state

/-- The entire original adaptive post-root schedule, including all public replies and complete role/private poststate, is the source interpretation of one response-only initializer client. -/
theorem program_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((simulateQ (target attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge) client).run state) =
      simulateQ (rootPost fixed baseImpl kem secret challenge)
        ((simulateQ (PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge) client).run state) := by
  let actual : QueryImpl (PqxdhPhase2SourceScheduler.Spec baseSpec S B)
      (StateT (PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) (OracleComp RootSpec)) :=
    fun query before => simulateQ (rootPost fixed baseImpl kem secret challenge)
      ((PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge query).run before)
  exact (simulateQ_StateT_compose _ _ actual
    (step_source attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge) client state).trans
      (simulateQ_StateT_compose
        (PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge)
        (rootPost fixed baseImpl kem secret challenge) actual (fun _ _ => rfl) client state).symm

end BeaconcryptCore.Computational.PqxdhInitialLabelPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelPost.public_no_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelPost.public_no_root

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelPost.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelPost.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelPost.public_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelPost.public_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelPost.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelPost.step_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelPost.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelPost.program_source
