import BeaconcryptCore.Computational.PqxdhInitialRootLabelService

/-!
The actual fused Beacon service names the selected-key root by its complete four DH coordinates, and names a locally recovered-key root by the actual fixed-source value. Its response is exactly the original root callback followed by the real initializer callback, in that order. The root-family label is private protocol metadata; it is not an assumed injective encoding of root values.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge
open PqxdhInitialRootLabelService PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand
open PqxdhCorrelatedExpandHybrid PqxdhPhase2DecapsulationRouting PqxdhBeaconPhase2Shared
open PqxdhInitialRatchetComplementarity PqxdhChallengeSecretRouting
variable {ι KemSK : Type} {baseSpec : OracleSpec ι}

noncomputable def request (fixed : FixedHkdfSha512NoSaltSource) (secrets : Secrets Shared) : Request :=
  let known := PqxdhPhase2InputBytes.coordinates secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4
  match secrets.shared with
  | .challenge => .family (PqxdhCorrelatedExtractFamily.coordinates known)
  | .known shared => .known (PqxdhHiddenRoot.productionHiddenRoot fixed known shared)

noncomputable def rootThenInitial (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (secrets : Secrets Shared) : OracleComp RootSpec (Option Response) := do
  let root ← simulateQ (PqxdhCorrelatedExpand.rootPost fixed baseImpl kem secret challenge)
    (PqxdhPhase2InputBytes.rootCall fixed challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4)
  pure (root.map (fun value => RawCtxSourceHkdf.initialResponse fixed.crypto (beaconPending value).request))

/-- The actual Beacon request uses exactly the same typed64-byte initializer interface as the response-only service, for every supplied computational root. -/
theorem initial_request (fixed : FixedHkdfSha512NoSaltSource) (root : PqxdhSecretInputKdf.RootOutput) :
    RawCtxSourceHkdf.initialResponse fixed.crypto
      (beaconPending (PqxdhRootTableInitialization.rootArray root)).request = realInitial fixed root := rfl

/-- The original root and initializer sequence is a cached family-coordinate request on the selected shared-secret handle and real local computation on every already recovered handle. -/
theorem root_initial_program (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (secrets : Secrets Shared) :
    rootThenInitial fixed baseImpl kem secret challenge secrets =
      match request fixed secrets with
      | .known root => pure (some (realInitial fixed root))
      | .family message => (some ∘ realInitial fixed) <$> (RootSpec.query (.inr message) : OracleComp RootSpec _) := by
  cases shared : secrets.shared with
  | known value =>
      simp [rootThenInitial, PqxdhPhase2InputBytes.rootCall, derive, shared, request, initial_request]
  | challenge =>
      simp [rootThenInitial, PqxdhPhase2InputBytes.rootCall, derive, shared, request,
        PqxdhCorrelatedExpand.rootPost, OracleSpec.query, initial_request]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete original root-cache effect of the actual Beacon sequence is precisely the response-only service at its source-derived private request. -/
theorem root_initial_source (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (secrets : Secrets Shared) (cache : RootOracle.QueryCache) :
    (simulateQ uniformImpl (rootThenInitial fixed baseImpl kem secret challenge secrets)).run cache =
      Prod.map some id <$> (PqxdhInitialRootLabelService.native fixed (request fixed secrets)).run cache := by
  rw [root_initial_program]
  cases named : request fixed secrets with
  | known root => rfl
  | family message =>
      simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map]
      change (fun pair => (some (realInitial fixed pair.1), pair.2)) <$>
        (uniformImpl (.inr message)).run cache = _
      simp only [PqxdhInitialRootLabelService.native, StateT.run, bind_pure_comp, Functor.map_map]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual source-derived Beacon service admits selected-coordinate response substitution under private cache reconstruction. Its executable labelled side receives no selected root. -/
theorem labelled_source (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (secrets : Secrets Shared)
    (selected : PqxdhCorrelatedExtractFamily.Message) (root : PqxdhSecretInputKdf.RootOutput) (cache : RootOracle.QueryCache) :
    Prod.map some (completeCache selected root) <$>
      (labelled fixed selected (realInitial fixed root) (request fixed secrets)).run cache =
        (simulateQ uniformImpl (rootThenInitial fixed baseImpl kem secret challenge secrets)).run
          (completeCache selected root cache) := by
  rw [root_initial_source]
  have same := congrArg (Functor.map (Prod.map some id)) (native_step fixed selected root (request fixed secrets) cache)
  have functions : (fun pair : Response × RootOracle.QueryCache => Prod.map some id (Prod.map id (completeCache selected root) pair)) =
      (Prod.map some (completeCache selected root) : Response × RootOracle.QueryCache → Option Response × RootOracle.QueryCache) := by
    funext pair
    rfl
  rw [Functor.map_map, functions] at same
  exact same

end BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge.initial_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge.initial_request

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge.root_initial_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge.root_initial_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge.root_initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge.root_initial_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge.labelled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge.labelled_source
