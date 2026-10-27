import BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared
import BeaconcryptCore.Computational.PqxdhPhase2InputBytes

/-!
Concrete private Phase2 dispatch combines the original decapsulation point and retained root coordinates in the existing CCA/private-root interface. A missing prior-key payload denotes the selected key, whose secret is an argument only of the native source interpreter. Every locally owned prior key remains a private payload. Other source callbacks retain their complete original replies and CCA/base effects.

This specializes root processing to the existing total fixed-source HKDF contract on legal inputs. Logical shared-secret wiping has no primitive-oracle result or effect; physical erasure remains external. The generic optional native adapter remains available separately. Codec, joint-identity and local-key callbacks still require their actual source instantiation, with explicit query costs; they are not new security assumptions or free ambient work.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext)
open PqxdhKemIndCca PqxdhJointKdfGame PqxdhInitializerSecrecy
open PqxdhChallengeSecretRouting PqxdhPhase2DecapsulationRouting
open PqxdhRootTableInitialization (rootArray)

/-- Source callbacks other than selected-key decapsulation and private root processing. No challenge-secret bytes are an argument. -/
inductive AuxQuery (I D K X Response : Type) where
  | decode : Bytes → AuxQuery I D K X Response
  | ciphertext : Response → AuxQuery I D K X Response
  | ephemeral : Response → AuxQuery I D K X Response
  | serverIdentity : Response → AuxQuery I D K X Response
  | publicConversion : Word32 → AuxQuery I D K X Response
  | privateConversion : I → AuxQuery I D K X Response
  | dhPair : D → Word32 → AuxQuery I D K X Response
  | dhIdentity : X → Word32 → AuxQuery I D K X Response
  | assignedId : Response → AuxQuery I D K X Response
  | localDecapsulation : Ciphertext → K → AuxQuery I D K X Response
  | initial : ratchet.SymmetricRatchetKdfRequest → AuxQuery I D K X Response
  | application : Response → AuxQuery I D K X Response
  | raw : RawCtxSourceOpen.NativeSpec.Domain → AuxQuery I D K X Response

abbrev AuxSpec (I D K X Response : Type) : OracleSpec (AuxQuery I D K X Response)
  | .decode _ => Option Response
  | .ciphertext _ => Option Ciphertext
  | .ephemeral _ | .serverIdentity _ | .publicConversion _ => Option Word32
  | .privateConversion _ => Option X
  | .dhPair _ _ | .dhIdentity _ _ | .localDecapsulation _ _ => Option Word32
  | .assignedId _ => Std.U64
  | .initial _ => pqxdh.concrete.InitialRatchetKdfResponse
  | .application _ => Option Bytes
  | .raw query => RawCtxSourceOpen.NativeSpec.Range query

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK I D K X Response Auxiliary : Type}

/-- Auxiliary work has no private-root capability; its original public CCA/base requests are forwarded. -/
def publicLift : QueryImpl (MlKemCCAOracleSpec baseSpec) (OracleComp (LocalPostSpec baseSpec)) :=
  fun query => liftM ((LocalPostSpec baseSpec).query (.inl query))

noncomputable def nativeAux
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (unifSpec + baseSpec))) :=
  fun query auxiliary => simulateQ (publicImpl kem secret challenge) ((aux query).run auxiliary)

def sharedAux
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (LocalPostSpec baseSpec))) :=
  fun query auxiliary => simulateQ publicLift ((aux query).run auxiliary)

/-- The actual source interpreter owns the selected KEM secret; other callbacks retain their original complete effect programs. -/
noncomputable def native
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D (Option K) X Response)
      (StateT Auxiliary (OracleComp (unifSpec + baseSpec)))
  | .inl (.decode raw) => nativeAux kem secret challenge aux (.decode raw)
  | .inl (.ciphertext response) => nativeAux kem secret challenge aux (.ciphertext response)
  | .inl (.ephemeral response) => nativeAux kem secret challenge aux (.ephemeral response)
  | .inl (.serverIdentity response) => nativeAux kem secret challenge aux (.serverIdentity response)
  | .inl (.publicConversion value) => nativeAux kem secret challenge aux (.publicConversion value)
  | .inl (.privateConversion identity) => nativeAux kem secret challenge aux (.privateConversion identity)
  | .inl (.decapsulate value none) =>
      liftM (Option.map rootArray <$> kem.decaps secret (PqxdhPhase2InputBytes.ciphertext value))
  | .inl (.decapsulate value (some prior)) => nativeAux kem secret challenge aux (.localDecapsulation value prior)
  | .inl (.dhPair pair value) => nativeAux kem secret challenge aux (.dhPair pair value)
  | .inl (.dhIdentity identity value) => nativeAux kem secret challenge aux (.dhIdentity identity value)
  | .inl (.assignedId response) => nativeAux kem secret challenge aux (.assignedId response)
  | .inl (.eraseShared _) => pure ()
  | .inr (.inl query) => nativeAux kem secret challenge aux (.raw query)
  | .inr (.inr (.root input)) => pure (some (RawCtxSourceHkdf.rootResponse source.crypto input))
  | .inr (.inr (.initial request)) => nativeAux kem secret challenge aux (.initial request)
  | .inr (.inr (.application response)) => nativeAux kem secret challenge aux (.application response)

/-- The private reduction program knows only the public challenge ciphertext, actual private handles and original source callbacks. -/
noncomputable def handles
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    QueryImpl (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared)
      (StateT Auxiliary (OracleComp (LocalPostSpec baseSpec)))
  | .inl (.decode raw) => sharedAux aux (.decode raw)
  | .inl (.ciphertext response) => sharedAux aux (.ciphertext response)
  | .inl (.ephemeral response) => sharedAux aux (.ephemeral response)
  | .inl (.serverIdentity response) => sharedAux aux (.serverIdentity response)
  | .inl (.publicConversion value) => sharedAux aux (.publicConversion value)
  | .inl (.privateConversion identity) => sharedAux aux (.privateConversion identity)
  | .inl (.decapsulate value none) => liftM (PqxdhPhase2InputBytes.decapCall (baseSpec := baseSpec) challenge value)
  | .inl (.decapsulate value (some prior)) =>
      Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) <$>
        sharedAux aux (.localDecapsulation value prior)
  | .inl (.dhPair pair value) => sharedAux aux (.dhPair pair value)
  | .inl (.dhIdentity identity value) => sharedAux aux (.dhIdentity identity value)
  | .inl (.assignedId response) => sharedAux aux (.assignedId response)
  | .inl (.eraseShared _) => pure ()
  | .inr (.inl query) => sharedAux aux (.raw query)
  | .inr (.inr (.root secrets)) =>
      liftM (PqxdhPhase2InputBytes.rootCall (baseSpec := baseSpec) source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4)
  | .inr (.inr (.initial request)) => sharedAux aux (.initial request)
  | .inr (.inr (.application response)) => sharedAux aux (.application response)

/-- Forwarding the public interface preserves its complete original callback program. -/
theorem publicLift_actual
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    actualImpl source kem secret challenge ∘ₛ publicLift = publicImpl kem secret challenge := by
  funext query
  exact simulateQ_spec_query (actualImpl source kem secret challenge) (.inl query)

/-- The entire auxiliary reply and its private poststate pass unchanged through public forwarding. -/
theorem sharedAux_actual
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (query : (AuxSpec I D K X Response).Domain) (auxiliary : Auxiliary) :
    simulateQ (actualImpl source kem secret challenge) ((sharedAux aux query).run auxiliary) =
      (nativeAux kem secret challenge aux query).run auxiliary := by
  exact (QueryImpl.simulateQ_compose _ _ _).symm.trans
    (congrArg (fun impl => simulateQ impl ((aux query).run auxiliary))
      (publicLift_actual source kem secret challenge))

/-- Interpreting opaque callbacks retains the whole private auxiliary poststate. -/
noncomputable def actualHandles
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    QueryImpl (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared)
      (StateT Auxiliary (OracleComp (unifSpec + baseSpec))) :=
  fun query auxiliary => simulateQ (actualImpl source kem secret challenge)
    ((handles source challenge aux query).run auxiliary)

set_option backward.isDefEq.respectTransparency false in
/-- Every preparation callback is realized with the original optional reply and private state. -/
theorem preparation_calls
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    PqxdhBeaconPhase2Shared.Calls (fun shared => rootArray (materialize supplied shared))
      (fun query => native source kem secret challenge aux (.inl query))
      (fun query => actualHandles source kem secret challenge aux (.inl query)) := by
  constructor <;> intros <;> funext auxiliary
  all_goals first | exact (sharedAux_actual source kem secret challenge aux _ auxiliary).symm | skip
  case eraseShared => exact (simulateQ_pure (actualImpl source kem secret challenge) ((), auxiliary)).symm
  case decapsulate value key =>
    cases key with
    | none =>
        change (native source kem secret challenge aux (.inl (.decapsulate value none))).run auxiliary =
          ((Option.map (fun shared => rootArray (materialize supplied shared)) <$>
            actualHandles source kem secret challenge aux (.inl (.decapsulate value none))).run auxiliary)
        rw [StateT.run_map]
        unfold native actualHandles handles
        simpa only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift,
          StateT.run, StateT.map, StateT.run_map, bind_pure_comp, simulateQ_map, Functor.map_map,
          Function.comp_def, PqxdhBeaconPhase2Publication.NativeSpec,
          PqxdhBeaconPhase2Preparation.Spec, OracleSpec.add_apply_inl] using
          congrArg (Functor.map (fun reply => (reply, auxiliary)))
            (PqxdhPhase2InputBytes.decapCall_native source kem secret challenge supplied agreement value).symm
    | some prior =>
        change (native source kem secret challenge aux (.inl (.decapsulate value (some prior)))).run auxiliary =
          ((Option.map (fun shared => rootArray (materialize supplied shared)) <$>
            actualHandles source kem secret challenge aux
              (.inl (.decapsulate value (some prior)))).run auxiliary)
        rw [StateT.run_map]
        rw [show native source kem secret challenge aux (.inl (.decapsulate value (some prior))) =
          nativeAux kem secret challenge aux (.localDecapsulation value prior) by rfl]
        have handled :
            (handles source challenge aux (.inl (.decapsulate value (some prior)))).run auxiliary =
              (fun pair =>
                (Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) pair.1, pair.2)) <$>
                (sharedAux aux (.localDecapsulation value prior)).run auxiliary := by
          rw [show handles source challenge aux (.inl (.decapsulate value (some prior))) =
            Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) <$>
              sharedAux aux (.localDecapsulation value prior) by rfl]
          exact StateT.run_map _ _ _
        have actual :
            (actualHandles source kem secret challenge aux
              (.inl (.decapsulate value (some prior)))).run auxiliary =
              simulateQ (actualImpl source kem secret challenge)
                ((handles source challenge aux (.inl (.decapsulate value (some prior)))).run auxiliary) := rfl
        rw [actual, handled, simulateQ_map,
          sharedAux_actual source kem secret challenge aux (.localDecapsulation value prior) auxiliary]
        simp only [Functor.map_map, Option.map_map, Function.comp_def, materialize,
          PqxdhPhase2InputBytes.word_roundtrip]
        rw [show (fun pair : Option Word32 × Auxiliary =>
          (Option.map (fun value => value) pair.1, pair.2)) = id by
            funext pair
            change (Option.map id pair.1, pair.2) = pair
            rw [Option.map_id_apply]]
        exact (id_map _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Root processing uses the source-derived 192 bytes and returns the same native result with its full auxiliary state. -/
theorem tail_calls
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    PqxdhBeaconPhase2Shared.TailCalls (fun shared => rootArray (materialize supplied shared))
      (fun query => native source kem secret challenge aux (.inr query))
      (fun query => actualHandles source kem secret challenge aux (.inr query)) := by
  constructor <;> intros <;> funext auxiliary
  all_goals first | exact (sharedAux_actual source kem secret challenge aux _ auxiliary).symm | skip
  case root secrets input built =>
    change (native source kem secret challenge aux (.inr (.inr (.root input)))).run auxiliary =
      (actualHandles source kem secret challenge aux (.inr (.inr (.root secrets)))).run auxiliary
    have sourceRun :
        (native source kem secret challenge aux (.inr (.inr (.root input)))).run auxiliary =
          pure (some (RawCtxSourceHkdf.rootResponse source.crypto input), auxiliary) := by
      rw [show native source kem secret challenge aux (.inr (.inr (.root input))) =
        pure (some (RawCtxSourceHkdf.rootResponse source.crypto input)) by rfl]
      rfl
    have handled :
        (handles source challenge aux (.inr (.inr (.root secrets)))).run auxiliary =
          (fun reply => (reply, auxiliary)) <$>
            PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4 := by
      rw [show handles source challenge aux (.inr (.inr (.root secrets))) =
        liftM (PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4) by rfl]
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift,
        StateT.run, bind_pure_comp]
    have actual :
        (actualHandles source kem secret challenge aux (.inr (.inr (.root secrets)))).run auxiliary =
          simulateQ (actualImpl source kem secret challenge)
            ((handles source challenge aux (.inr (.inr (.root secrets)))).run auxiliary) := rfl
    rw [sourceRun, actual, handled, simulateQ_map,
      PqxdhPhase2InputBytes.rootCall_native source kem secret challenge supplied agreement
      secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4 input built, map_pure]

/-- The concrete source and reduction interpreters discharge every opaque-owner callback obligation. -/
theorem full_calls
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    PqxdhBeaconPhase2Shared.FullCalls (fun shared => rootArray (materialize supplied shared))
      (native source kem secret challenge aux) (actualHandles source kem secret challenge aux) :=
  ⟨preparation_calls source kem secret challenge supplied agreement aux,
    tail_calls source kem secret challenge supplied agreement aux⟩

/-- One complete native Phase2 attempt equals its private CCA/root program with exactly the original final owner and auxiliary state. -/
theorem owner_actual
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    (simulateQ (native source kem secret challenge aux)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary =
        simulateQ (actualImpl source kem secret challenge)
          ((simulateQ (handles source challenge aux)
            (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary) := by
  rw [PqxdhBeaconPhase2Shared.owner_realization _ _ _
    (full_calls source kem secret challenge supplied agreement aux)]
  exact (simulateQ_StateT_compose (handles source challenge aux) (actualImpl source kem secret challenge)
    (actualHandles source kem secret challenge aux) (fun _ _ => rfl) _ auxiliary).symm

/-- Every continued private experiment retains its full optional result, owner, auxiliary state and subsequent effects. -/
theorem owner_continuation {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary)
    (next : ((Option Bytes × PqxdhBeaconPhase2Preparation.State I D (Option K)) × Auxiliary) →
      OracleComp (LocalPostSpec baseSpec) Result) :
    ((simulateQ (native source kem secret challenge aux)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary >>=
        fun result => simulateQ (actualImpl source kem secret challenge) (next result)) =
      simulateQ (actualImpl source kem secret challenge)
        ((simulateQ (handles source challenge aux) (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary >>= next) := by
  rw [owner_actual source kem secret challenge supplied agreement aux, simulateQ_bind]

/-- The same Phase2 execution is simulated through the ordinary postchallenge CCA interface, with the challenge blocked on its public decapsulation channel. -/
theorem owner_reduction
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    (simulateQ (native source kem secret challenge aux)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary =
        simulateQ (publicImpl kem secret challenge)
          (simulateQ (route source challenge supplied)
            ((simulateQ (handles source challenge aux)
              (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary)) := by
  rw [owner_actual source kem secret challenge supplied agreement aux,
    route_complete source kem secret challenge supplied agreement]

/-- Existing functional decapsulation and recipient correctness at the actual generated support discharge the complete source equation. -/
theorem owner_supported
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem
      (runtimeOfImpl (kemAmbientImpl baseImpl)))
    {pk : MlKem768PublicKey} {secret : KemSK}
    (generated : (pk, secret) ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen))
    {challenge : MlKem768Ciphertext} {supplied : MlKemSharedSecret}
    (encapsulated : (challenge, supplied) ∈ support (simulateQ (kemAmbientImpl baseImpl) (kem.encaps pk)))
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    (simulateQ (native source kem secret challenge aux)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary =
        simulateQ (actualImpl source kem secret challenge)
          ((simulateQ (handles source challenge aux)
            (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary) :=
  owner_actual source kem secret challenge supplied
    (honest_decapsulation_program baseImpl kem functional correct generated encapsulated)
      aux decode raw state auxiliary

end BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.publicLift_actual' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.publicLift_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.sharedAux_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.sharedAux_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.preparation_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.preparation_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.tail_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.tail_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.full_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.full_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.owner_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.owner_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.owner_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.owner_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.owner_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.owner_reduction

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.owner_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed.owner_supported
