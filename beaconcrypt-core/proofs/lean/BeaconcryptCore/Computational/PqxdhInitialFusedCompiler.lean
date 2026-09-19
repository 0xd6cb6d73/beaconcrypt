import BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks
import BeaconcryptCore.Computational.PqxdhInitialLabelCompiler

/-!
The complete actual Beacon owner compiles to a response-only initializer interface. Every non-root callback runs as its checked original cache-free computation, and the single fused private request carries its actual four-DH coordinate or known local root. No selected raw root is a compiler argument. Native interpretation retains the full original owner state, private identity/shared state and source callback order.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialFusedCompiler
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhPhase2SourceAux
open PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState (IdentityHandle KemHandle)
open PqxdhPhase2JointIdentity (Converted)
variable {ι I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι}

abbrev Spec (I D K X Response : Type) := PqxdhInitialFusedOwner.Spec
  (IdentityHandle I) D (KemHandle K) (X ⊕ Converted) Response PqxdhPhase2DecapsulationRouting.Shared

noncomputable def compiler
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (Spec I D K X Response) (StateT (SharedState A × BareState count) (OracleComp PqxdhInitialLabelCompiler.Spec))
  | .inl query => fun state => PqxdhInitialLabelCompiler.coins
      ((PqxdhInitialRootFreeCallbacks.interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inl query)).run state)
  | .inr (.inl query) => fun state => PqxdhInitialLabelCompiler.coins
      ((PqxdhInitialRootFreeCallbacks.interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr query)).run state)
  | .inr (.inr secrets) => fun state => do
      let response ← PqxdhInitialLabelCompiler.Spec.query (.inr (PqxdhInitialRootLabelBridge.request fixed secrets))
      pure (some response, state)

noncomputable def native
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (Spec I D K X Response) (StateT (SharedState A × BareState count) (OracleComp RootSpec)) :=
  fun query state => simulateQ (rootPost fixed baseImpl kem secret challenge)
    ((simulateQ (PqxdhPhase2PostScheduler.handles attachedVerify primitives count fixed localImpl challenge)
      (PqxdhInitialFusedOwner.native query)).run state)

/-- The actual non-root preparation callback is preserved by the response-only compiler with every private state field retained. -/
theorem preparation_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhBeaconPhase2Shared.Spec (IdentityHandle I) D (KemHandle K) (X ⊕ Converted) Response PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (state : SharedState A × BareState count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inl query)).run state) =
        (native attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inl query)).run state := by
  rw [compiler, StateT.run, PqxdhInitialLabelCompiler.coins_source]
  exact (PqxdhInitialRootFreeCallbacks.callback_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inl query) state).symm

set_option backward.isDefEq.respectTransparency false in
/-- Original raw-record work and application extraction retain their exact replies and shared/private effects under the initializer compiler. -/
theorem data_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhInitialFusedBeacon.DataSpec Response).Domain) (state : SharedState A × BareState count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr (.inl query))).run state) =
        (native attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr (.inl query))).run state := by
  rw [compiler, StateT.run, PqxdhInitialLabelCompiler.coins_source]
  have same := (PqxdhInitialRootFreeCallbacks.callback_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr query) state).symm
  cases query <;> simpa only [native, PqxdhInitialFusedOwner.native, PqxdhInitialFusedBeacon.native,
    simulateQ_spec_query, PqxdhBeaconPhase2Shared.tailLift, PqxdhInitialRootFreeCallbacks.work,
    PqxdhInitialRootFreeCallbacks.original, StateT.run] using same

set_option backward.isDefEq.respectTransparency false in
/-- The actual fused root/initializer request retains the original root then initializer effects and the complete unchanged shared/private state. -/
theorem private_native
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : SharedState A × BareState count) :
    (native attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr (.inr secrets))).run state =
      (fun reply => (reply, state)) <$> PqxdhInitialRootLabelBridge.rootThenInitial fixed baseImpl kem secret challenge secrets := by
  have rootStep :
      (PqxdhPhase2PostScheduler.handles (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl challenge
        (.inr (.inr (.root secrets)))).run state =
      (fun reply => (reply, state)) <$> PqxdhPhase2InputBytes.rootCall fixed challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4 := by
    simp only [PqxdhPhase2PostScheduler.handles, QueryImpl.compose,
      PqxdhPhase2SharedKemHandles.full, simulateQ_spec_query, PqxdhBeaconPhase2Routed.handles]
    rfl
  unfold native
  simp only [PqxdhInitialFusedOwner.native, PqxdhInitialFusedBeacon.native,
    simulateQ_bind, simulateQ_spec_query, PqxdhBeaconPhase2Shared.tailLift, StateT.run_bind]
  change (do
    let result ← simulateQ (rootPost fixed baseImpl kem secret challenge)
      ((PqxdhPhase2PostScheduler.handles attachedVerify primitives count fixed localImpl challenge (.inr (.inr (.root secrets)))).run state)
    _) = _
  rw [rootStep]
  simp only [simulateQ_map, bind_map_left, PqxdhInitialRootLabelBridge.rootThenInitial, map_bind, map_pure]
  apply bind_congr
  intro root
  cases root with
  | none => simp [simulateQ_pure]
  | some root =>
      change simulateQ (rootPost fixed baseImpl kem secret challenge)
        ((fun pair : beaconcrypt_core.pqxdh.concrete.InitialRatchetKdfResponse × (SharedState A × BareState count) =>
          (some pair.1, pair.2)) <$> simulateQ PqxdhBeaconPhase2Routed.publicLift
            ((borrowedAux attachedVerify primitives count fixed localImpl
              (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request)).run state)) = _
      rw [PqxdhPhase2SourceAux.initial_complete]
      simp only [simulateQ_pure, map_pure, Option.map_some]


set_option backward.isDefEq.respectTransparency false in
/-- The fused private service is compiled using its actual source-derived request and returns only the complete initializer response. -/
theorem private_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (state : SharedState A × BareState count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr (.inr secrets))).run state) =
        (native attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr (.inr secrets))).run state := by
  rw [private_native, PqxdhInitialRootLabelBridge.root_initial_program]
  unfold compiler
  simp only [StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  cases named : PqxdhInitialRootLabelBridge.request fixed secrets with
  | known root => rfl
  | family message =>
      simp only [PqxdhInitialLabelCompiler.source, bind_pure_comp, Functor.map_map]
      rfl

/-- Every actual fused owner callback has the same entire source interpretation under the response-only compiler. -/
theorem step_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (Spec I D K X Response).Domain) (state : SharedState A × BareState count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run state) =
        (native attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run state := by
  cases query with
  | inl query => exact preparation_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query state
  | inr query => cases query with
    | inl query => exact data_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query state
    | inr query => exact private_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query state

/-- Every complete adaptive fused owner program preserves its original result and full shared/private state under the response-only compiler. -/
theorem program_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (Spec I D K X Response) Result) (state : SharedState A × BareState count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((simulateQ (compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge) client).run state) =
        (simulateQ (native attachedVerify primitives count fixed localImpl baseImpl kem secret challenge) client).run state :=
  simulateQ_StateT_compose _ _ _ (step_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge) client state

/-- The compiler's native complete continuation is the literal original callback interpreter, preserving all source order and optional failure branches. -/
theorem native_program
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (Spec I D K X Response) Result) (state : SharedState A × BareState count) :
    (simulateQ (native attachedVerify primitives count fixed localImpl baseImpl kem secret challenge) client).run state =
      simulateQ (rootPost fixed baseImpl kem secret challenge)
        ((simulateQ (PqxdhPhase2PostScheduler.handles attachedVerify primitives count fixed localImpl challenge)
          (simulateQ PqxdhInitialFusedOwner.native client)).run state) := by
  rw [← QueryImpl.simulateQ_compose]
  exact (simulateQ_StateT_compose
    (PqxdhPhase2PostScheduler.handles attachedVerify primitives count fixed localImpl challenge ∘ₛ PqxdhInitialFusedOwner.native)
    (rootPost fixed baseImpl kem secret challenge)
    (native attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
    (fun _ _ => rfl) client state).symm

/-- The original complete current Beacon owner is the source interpretation of this response-only compiler, with all phase gates, raw receive, binding checks and whole publication preserved. -/
theorem owner_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (KemHandle K))
    (state : SharedState A × BareState count) :
    simulateQ (PqxdhInitialLabelCompiler.source fixed)
      ((simulateQ (compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
        (PqxdhInitialFusedOwner.owner decode raw owner)).run state) =
      simulateQ (rootPost fixed baseImpl kem secret challenge)
        ((simulateQ (PqxdhPhase2PostScheduler.handles attachedVerify primitives count fixed localImpl challenge)
          (PqxdhBeaconPhase2Shared.owner decode raw owner)).run state) := by
  rw [program_source, native_program, PqxdhInitialFusedOwner.owner_native]

end BeaconcryptCore.Computational.PqxdhInitialFusedCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.preparation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.preparation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.data_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.data_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.private_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.private_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.private_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.private_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.step_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.native_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedCompiler.owner_source
