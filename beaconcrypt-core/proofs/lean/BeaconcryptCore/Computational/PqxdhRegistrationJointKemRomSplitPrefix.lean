import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplitTools

/-!
# The table cache at the cut (item 2, stage S1c, prefix accounting)

This module bounds the keys of the shared Extract table's cache at the cut of the KEM-ideal branch by the table requests of the source program before the cut, and keeps the rest of the source budget for the continuation after the cut (the plan's cut-split of `certified`).

- Every native step of the source backend adds at most one key to the table cache, and only on a native table request: a raw accept (its root read), a public HMAC (on the zero-key 192-byte slice) or the Beacon tail's root callback (`impl_grows`).
- Every source request makes at most one native table request, and only if it is a table request of the source (`TableKind`: raw accept, Beacon finish, public HMAC); a Beacon finish makes at most one root request (`client_bound`).
- Along the scan to the selected raw accept, the number of keys at the cut plus one (the selected accept) plus the remaining table budget of the suspended continuation is at most the table budget of the whole source program (`commands_cut`, through `PqxdhRegistrationJointKemRomSplit.scan_potential` on the composition of the client and the native backend).
- The same holds for every active prechallenge context reached by the KEM-ideal branch (`opaqueScan_fits`, `sourcePreOpaque_fits`, `sharedStart_fits`).
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)
open PqxdhServerAuthNative (NativeGame NativeState)

/-! ### Keys added by native steps -/

section Native

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The number of keys of the table cache of a native state. -/
noncomputable def keyCount (state : NativeState KemSK) : ℕ∞ := (cacheKeys state.1.cache).encard

/-- A native program adds at most `k` keys to the table cache. -/
def GrowsN {α : Type} (work : NativeGame KemSK α) (k : ℕ) : Prop :=
  ∀ state, ∀ result ∈ support (work.run state), keyCount result.2 ≤ keyCount state + k

/-- A program on the exposed encapsulation interface adds at most `k` keys to the table cache. -/
def Grows {α : Type} (work : PqxdhRegistrationJointKemEncapsulation.Client KemSK α) (k : ℕ) : Prop :=
  ∀ state, ∀ result ∈ support (work.run state), keyCount result.2 ≤ keyCount state + k

theorem growsN_pure {α : Type} (value : α) : GrowsN (pure value : NativeGame KemSK α) 0 := by
  intro state result reached
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
  subst reached
  simp

theorem growsN_bind {α β : Type} {work : NativeGame KemSK α} {next : α → NativeGame KemSK β} {a b : ℕ}
    (first : GrowsN work a) (rest : ∀ value, GrowsN (next value) b) : GrowsN (work >>= next) (a + b) := by
  intro state result reached
  simp only [StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨middle, now, later⟩ := reached
  calc keyCount result.2 ≤ keyCount middle.2 + b := rest middle.1 middle.2 result later
    _ ≤ keyCount state + a + b := add_le_add (first state middle now) le_rfl
    _ = keyCount state + ((a + b : ℕ) : ℕ∞) := by rw [add_assoc, Nat.cast_add]

theorem growsN_mono {α : Type} {work : NativeGame KemSK α} {a b : ℕ} (grows : GrowsN work a) (le : a ≤ b) :
    GrowsN work b :=
  fun state result reached => (grows state result reached).trans (add_le_add le_rfl (by exact_mod_cast le))

/-- A native program that keeps the family state adds no key. -/
theorem growsN_family {α : Type} (work : NativeGame KemSK α)
    (same : ∀ state, ∀ result ∈ support (work.run state), result.2.1 = state.1) : GrowsN work 0 := by
  intro state result reached
  simp [keyCount, same state result reached]

theorem growsN_local {α : Type} (step : GameState KemSK → α × GameState KemSK) :
    GrowsN (PqxdhServerAuthNative.localState step) 0 :=
  growsN_family _ fun state result reached => by
    simp only [PqxdhServerAuthNative.localState, StateT.run, support_pure, Set.mem_singleton_iff] at reached
    rw [reached]

theorem growsN_coins {α : Type} (work : ProbComp α) : GrowsN (PqxdhServerAuthNative.nativeCoins (KemSK := KemSK) work) 0 :=
  growsN_family _ fun state result reached => by
    simp only [PqxdhServerAuthNative.nativeCoins, StateT.run, support_map, Set.mem_image] at reached
    obtain ⟨_, _, rfl⟩ := reached
    rfl

theorem growsN_ctx {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    GrowsN (PqxdhServerAuthNative.nativeCtx (KemSK := KemSK) work) 0 :=
  growsN_family _ fun state result reached => by
    simp only [PqxdhServerAuthNative.nativeCtx, StateT.run, support_map, Set.mem_image] at reached
    obtain ⟨_, _, rfl⟩ := reached
    rfl

theorem growsN_hash (bytes : Pqxdh.Bytes) : GrowsN (PqxdhServerAuthNative.nativeHash (KemSK := KemSK) bytes) 0 :=
  growsN_family _ fun state result reached => by
    simp only [PqxdhServerAuthNative.nativeHash, StateT.run, support_map, Set.mem_image] at reached
    obtain ⟨_, _, rfl⟩ := reached
    rfl

theorem growsN_romRootBytes (hmac : PqxdhSecretInputKdf.HmacSha512) (point : PqxdhJointDhExtractFamily.Message)
    (bytes : Pqxdh.Bytes) :
    GrowsN (PqxdhServerAuthNative.romRootBytes (A := GameState KemSK) hmac point bytes) 1 := by
  intro state result reached
  simp only [PqxdhServerAuthNative.romRootBytes, StateT.run, support_map, Set.mem_image] at reached
  obtain ⟨read, inner, rfl⟩ := reached
  exact randomOracle_encard bytes state.1.cache read inner

theorem growsN_sourceRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    GrowsN (PqxdhServerAuthNative.sourceRoot (KemSK := KemSK) hmac input) 1 := by
  intro state result reached
  simp only [PqxdhServerAuthNative.sourceRoot, StateT.run, support_map, Set.mem_image] at reached
  obtain ⟨read, inner, rfl⟩ := reached
  exact randomOracle_encard _ state.1.cache read inner

theorem growsN_hmac (setup : Setup baseSpec KemSK) (key : HmacBlock) (message : Pqxdh.Bytes) :
    GrowsN (PqxdhRegistrationJointPublicShared.hmac setup key message) 1 := by
  have family : GrowsN (fun state : NativeState KemSK => (fun result => (result.1, (result.2, state.2))) <$>
      (PqxdhRegistrationJointPublicShared.publicFamily setup.hmac key message).run state.1 :
        NativeGame KemSK HmacBlock) 1 := by
    intro state result reached
    simp only [StateT.run, support_map, Set.mem_image] at reached
    obtain ⟨inner, member, rfl⟩ := reached
    by_cases slice : key = PqxdhSecretInputKdf.zeroSalt ∧ message.length = 192
    · simp only [PqxdhRegistrationJointPublicShared.publicFamily, slice, and_self, ite_true, StateT.run,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨read, readReached, rfl⟩ := member
      exact randomOracle_encard message state.1.cache read readReached
    · simp only [PqxdhRegistrationJointPublicShared.publicFamily, slice, ite_false, StateT.run, support_pure,
        Set.mem_singleton_iff] at member
      subst member
      simp [keyCount]
  unfold PqxdhRegistrationJointPublicShared.hmac
  dsimp only
  split
  · show GrowsN _ (0 + 1)
    exact growsN_bind (growsN_local _) fun _ => family
  · exact family

theorem growsN_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) :
    GrowsN (PqxdhServerAuthNative.nativeBuild setup codec checks session payload) 0 := by
  unfold PqxdhServerAuthNative.nativeBuild
  refine growsN_bind (a := 0) (b := 0) (growsN_local _) fun state => ?_
  split
  · exact growsN_pure none
  · exact growsN_bind (a := 0) (b := 0) (growsN_coins _) fun _ =>
      growsN_bind (a := 0) (b := 0) (growsN_local _) fun _ => growsN_pure _

theorem growsN_loggedRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32)
    (original : beaconcrypt_core.pqxdh.PendingServerRegistration) :
    GrowsN (PqxdhServerAuthNative.loggedRoot (KemSK := KemSK) hmac index input original) 1 :=
  growsN_bind (a := 1) (b := 0) (growsN_romRootBytes _ _ _) fun _ =>
    growsN_bind (a := 0) (b := 0) (growsN_local _) fun _ => growsN_pure _

theorem growsN_client (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    GrowsN (PqxdhServerAuthNative.nativeClient (KemSK := KemSK) hmac index control binding input) 1 := by
  unfold PqxdhServerAuthNative.nativeClient
  split
  · exact growsN_mono (growsN_pure _) (Nat.zero_le _)
  · exact growsN_mono (growsN_pure _) (Nat.zero_le _)
  · exact growsN_mono (growsN_pure _) (Nat.zero_le _)
  · exact growsN_bind (a := 1) (b := 0) (growsN_loggedRoot _ _ _ _) fun _ =>
      growsN_bind (a := 0) (b := 0) (growsN_local _) fun _ => growsN_pure _

theorem growsN_acceptTail (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity) (before : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    GrowsN (PqxdhRegistrationJointServerAccept.tail setup publicIdentity before collected) 1 := by
  unfold PqxdhRegistrationJointServerAccept.tail
  refine growsN_bind (a := 0) (b := 1) (growsN_local _) fun _ => ?_
  rcases collected with ⟨_ | input, consumed⟩
  · exact growsN_mono (growsN_pure none) (Nat.zero_le _)
  · refine growsN_bind (a := 1) (b := 0) (growsN_client _ _ _ _ _) fun returned => ?_
    split
    · exact growsN_bind (a := 0) (b := 0) (growsN_local _) fun _ => growsN_pure _
    · exact growsN_pure none

/-- A native program run on the exposed encapsulation interface adds the same keys. -/
theorem grows_lift {α : Type} {work : NativeGame KemSK α} {k : ℕ} (grows : GrowsN work k) :
    Grows (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native work)) k := by
  intro state result reached
  rw [PqxdhRegistrationJointKemPostSkeleton.lift_native_run] at reached
  exact grows state result (PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ reached)

end Native

/-! ### Native table requests of the source backend -/

section Backend

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The native requests that read the shared table: the raw accept, the public HMAC and the Beacon tail's root callback. -/
def NativeKind : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain → Prop
  | .inl (.inr (.inr (.root _))) => True
  | .inr (.accept _) => True
  | .inr (.hmac _ _) => True
  | _ => False

instance : DecidablePred (NativeKind (KemSK := KemSK) (Response := Response))
  | .inl (.inl _) => inferInstanceAs (Decidable False)
  | .inl (.inr (.inl _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.inr (.root _))) => inferInstanceAs (Decidable True)
  | .inl (.inr (.inr (.initial _))) => inferInstanceAs (Decidable False)
  | .inl (.inr (.inr (.application _))) => inferInstanceAs (Decidable False)
  | .inr (.accept _) => inferInstanceAs (Decidable True)
  | .inr (.build _ _) => inferInstanceAs (Decidable False)
  | .inr (.hmac _ _) => inferInstanceAs (Decidable True)
  | .inr (.hash _) => inferInstanceAs (Decidable False)
  | .inr (.reveal _) => inferInstanceAs (Decidable False)

theorem grows_mono {α : Type} {work : PqxdhRegistrationJointKemEncapsulation.Client KemSK α} {a b : ℕ}
    (grows : Grows work a) (le : a ≤ b) : Grows work b :=
  fun state result reached => (grows state result reached).trans (add_le_add le_rfl (by exact_mod_cast le))

/-- Every native step of the source backend adds at most one key, and only on a native table request. -/
theorem impl_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) :
    Grows (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity query)
      (if NativeKind query then 1 else 0) := by
  rcases query with (pool | tail) | shared
  · intro state result reached
    change result ∈ support (simulateQ PqxdhRegistrationJointKemEncapsulation.forward
      ((fun answer => (answer, state)) <$>
        ((PqxdhLiveKemBirth.Spec KemSK).query pool : OracleComp (PqxdhLiveKemBirth.Spec KemSK) _))) at reached
    rw [simulateQ_map, support_map] at reached
    obtain ⟨_, _, rfl⟩ := reached
    simp
  · rcases tail with raw | (input | request | response)
    · exact grows_lift (growsN_ctx _)
    · exact grows_lift (growsN_sourceRoot _ _)
    · exact grows_lift (growsN_ctx _)
    · exact grows_lift (growsN_ctx _)
  · cases shared with
    | accept raw =>
        intro state result reached
        simp only [PqxdhRegistrationJointKemEncapsulation.impl, PqxdhRegistrationJointKemEncapsulation.accept,
          StateT.run_bind, mem_support_bind_iff] at reached
        obtain ⟨before, beforeReached, collected, collectedReached, later⟩ := reached
        rw [PqxdhRegistrationJointKemPostSkeleton.lift_native_run] at beforeReached
        have beforeState := PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ beforeReached
        simp only [PqxdhServerAuthNative.nativeGet, PqxdhServerAuthNative.localState, StateT.run, support_pure,
          Set.mem_singleton_iff] at beforeState
        change collected ∈ support ((fun result => (result, before.2)) <$> _) at collectedReached
        rw [support_map] at collectedReached
        obtain ⟨_, _, rfl⟩ := collectedReached
        rw [beforeState] at later
        simpa [NativeKind] using grows_lift (growsN_acceptTail setup publicIdentity _ _) state result later
    | build session payload => exact grows_lift (growsN_build setup codec checks session payload)
    | hmac key message => exact grows_lift (growsN_hmac setup key message)
    | hash bytes => exact grows_lift (growsN_hash bytes)
    | reveal keyId => exact grows_lift (growsN_local _)

end Backend

/-! ### Native table requests of a source request -/

section Client

open PqxdhBeaconPhase2Publication (TailSpec FullSpec NativeSpec NativeTailSpec)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A simulation whose every step makes no targeted request makes none. -/
theorem simulate_free {κ κ' α : Type} {spec : OracleSpec κ} {spec' : OracleSpec κ'}
    (handler : QueryImpl spec (OracleComp spec')) (q : κ' → Prop) [DecidablePred q]
    (step : ∀ query, (handler query).IsQueryBoundP q 0) (work : OracleComp spec α) :
    (simulateQ handler work).IsQueryBoundP q 0 :=
  IsQueryBoundP.simulateQ_of_step (p := fun _ => False)
    (PqxdhRegistrationJointBeaconOpaqueFinishRouter.free_false work) (fun _ absurd => absurd.elim)
    (fun query _ => step query)

/-- A single request that is not targeted. -/
theorem query_free {κ : Type} {spec : OracleSpec κ} (q : κ → Prop) [DecidablePred q] (query : κ)
    (free : ¬ q query) : (liftM (spec.query query) : OracleComp spec _).IsQueryBoundP q 0 :=
  (isQueryBoundP_query_iff q query 0).mpr fun target => absurd target free

/-- A single request. -/
theorem query_one {κ : Type} {spec : OracleSpec κ} (q : κ → Prop) [DecidablePred q] (query : κ) :
    (liftM (spec.query query) : OracleComp spec _).IsQueryBoundP q 1 :=
  (isQueryBoundP_query_iff q query 1).mpr fun _ => Nat.one_pos

/-- The Beacon tail's root request. -/
def rootTail : (TailSpec Response).Domain → Bool
  | .inr (.root _) => true
  | _ => false

/-- The Beacon tail's root request in the owner's interface. -/
def rootFull {I D K X : Type} : (FullSpec I D K X Response).Domain → Bool
  | .inr (.inr (.root _)) => true
  | _ => false

/-- The Beacon tail's root request in the native owner's interface. -/
def rootNative {I D K X : Type} : (NativeSpec I D K X Response).Domain → Bool
  | .inr (.inr (.root _)) => true
  | _ => false

/-- The Beacon tail's root request in the compiled finish's interface. -/
def rootFinish : (PqxdhRegistrationJointFinishCompiler.Spec KemSK Response).Domain → Bool
  | .inr (.inr (.root _)) => true
  | _ => false

/-- The continuation after the root makes no root request. -/
theorem afterRoot_rootless (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (root : PqxdhBeaconPhase2Preparation.Word32) :
    (PqxdhBeaconPhase2Publication.afterRoot decode prepared root).IsQueryBoundP (fun query => rootTail query = true) 0 := by
  unfold PqxdhBeaconPhase2Publication.afterRoot PqxdhBeaconPhase2Publication.initialRun
  simp only [bind_assoc, pure_bind]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [rootTail]), fun response => ?_⟩
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [rootTail]), fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some raw =>
      simp only [rootTail, Bool.false_eq_true, ite_false]
      refine isQueryBoundP_bind (n := 0) (m := 0)
        (simulate_free _ _ (fun query => ?_) _) (fun _ _ => trivial)
      exact query_free _ _ (by simp)

/-- The native Beacon tail makes at most one root request. -/
theorem tail_root (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) :
    (PqxdhBeaconPhase2Publication.tail decode prepared).IsQueryBoundP (fun query => rootTail query = true) 1 := by
  unfold PqxdhBeaconPhase2Publication.tail
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr Nat.one_pos, fun reply => ?_⟩
  cases reply with
  | none => trivial
  | some root => exact afterRoot_rootless decode prepared root

/-- The native Beacon owner makes at most one root request. -/
theorem owner_root {I D K X : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    (PqxdhBeaconPhase2Publication.owner (X := X) (Response := Response) decode raw state).IsQueryBoundP
      (fun query => rootFull query = true) 1 := by
  unfold PqxdhBeaconPhase2Publication.owner
  split
  · refine isQueryBoundP_bind (n := 0) (m := 1)
      (simulate_free PqxdhBeaconPhase2Publication.preLift _ (fun query => query_free _ _ (by simp [rootFull])) _)
      fun prepared _ => ?_
    cases prepared with
    | none => trivial
    | some prepared =>
        refine isQueryBoundP_bind (n := 1) (m := 0) ?_ (fun _ _ => trivial)
        refine IsQueryBoundP.simulateQ_of_step (tail_root decode prepared) (fun query root => ?_) (fun query root => ?_)
        · exact query_one _ _
        · refine query_free _ _ ?_
          rcases query with query | query
          · simp [rootFull]
          · cases query <;> simp_all [rootFull, rootTail]
  · trivial

theorem simulate_one_root {I D K X : Type} (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    (PqxdhBeaconPhase2Publication.nativeAdapter (I := I) (D := D) (K := K) (X := X) (Response := Response)
      (.inr (.inr (.root input)))).IsQueryBoundP (fun query => rootNative query = true) 1 := by
  simp only [PqxdhBeaconPhase2Publication.nativeAdapter, PqxdhBeaconPhase2Publication.nativeTailAdapter,
    PqxdhBeaconPhase2Publication.nativeTailLift, simulateQ_spec_query]
  exact query_one _ _

theorem simulate_initial {I D K X : Type} (request : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest) :
    (PqxdhBeaconPhase2Publication.nativeAdapter (I := I) (D := D) (K := K) (X := X) (Response := Response)
      (.inr (.inr (.initial request)))).IsQueryBoundP (fun query => rootNative query = true) 0 := by
  simp only [PqxdhBeaconPhase2Publication.nativeAdapter, PqxdhBeaconPhase2Publication.nativeTailAdapter,
    PqxdhBeaconPhase2Publication.nativeTailLift, simulateQ_spec_query]
  exact query_free _ _ (by simp [rootNative])

theorem simulate_application {I D K X : Type} (response : Response) :
    (PqxdhBeaconPhase2Publication.nativeAdapter (I := I) (D := D) (K := K) (X := X) (Response := Response)
      (.inr (.inr (.application response)))).IsQueryBoundP (fun query => rootNative query = true) 0 := by
  simp only [PqxdhBeaconPhase2Publication.nativeAdapter, PqxdhBeaconPhase2Publication.nativeTailAdapter,
    PqxdhBeaconPhase2Publication.nativeTailLift, simulateQ_spec_query]
  exact query_free _ _ (by simp [rootNative])

/-- The expanded native Beacon owner makes at most one root request. -/
theorem nativeOwner_root {I D K X : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    (PqxdhBeaconPhase2Publication.nativeOwner (X := X) (Response := Response) decode raw state).IsQueryBoundP
      (fun query => rootNative query = true) 1 := by
  refine IsQueryBoundP.simulateQ_of_step (owner_root decode raw state) (fun query root => ?_) (fun query root => ?_)
  · rcases query with query | (query | (input | request | response))
    · simp [rootFull] at root
    · simp [rootFull] at root
    · exact simulate_one_root input
    · simp [rootFull] at root
    · simp [rootFull] at root
  · rcases query with query | (query | (input | request | response))
    · exact query_free _ _ (by simp [rootNative])
    · simp only [PqxdhBeaconPhase2Publication.nativeAdapter, PqxdhBeaconPhase2Publication.nativeTailAdapter]
      rw [← QueryImpl.simulateQ_compose]
      refine simulate_free _ (fun query => rootNative query = true) (fun query => ?_) _
      simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeRawLift,
        PqxdhBeaconPhase2Publication.nativeTailLift, simulateQ_spec_query]
      exact query_free _ _ (by simp [rootNative])
    · simp [rootFull] at root
    · exact simulate_initial request
    · exact simulate_application response

/-- The compiled native Beacon owner makes at most one root request. -/
theorem compiled_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationJointBundle.Owner) :
    (simulateQ (PqxdhRegistrationJointFinishCompiler.compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).IsQueryBoundP
        (fun query => rootFinish (KemSK := KemSK) (Response := Response) query = true) 1 := by
  refine IsQueryBoundP.simulateQ_of_step (nativeOwner_root codec.frameRead raw owner) (fun query root => ?_)
    (fun query root => ?_)
  · rcases query with query | query
    · simp [rootNative] at root
    · exact query_one _ _
  · rcases query with query | query
    · simp only [PqxdhRegistrationJointFinishCompiler.compiler]
      exact simulate_free PqxdhRegistrationJointFinishCompiler.poolLift _
        (fun query => query_free _ _ (by simp [rootFinish])) _
    · refine query_free _ _ ?_
      rcases query with query | query
      · simp [rootFinish]
      · cases query <;> simp_all [rootNative, rootFinish]

/-- A program on the private pool makes no native table request. -/
theorem pool_free {α : Type} (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) :
    (simulateQ (PqxdhRegistrationJointServiceSchedule.poolLift (Response := Response)) work).IsQueryBoundP
      (NativeKind (KemSK := KemSK) (Response := Response)) 0 :=
  simulate_free PqxdhRegistrationJointServiceSchedule.poolLift _ (fun query => query_free _ _ (by simp [NativeKind])) _

/-- A source Beacon finish makes at most one native table request: its root request. -/
theorem finish_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (raw : Pqxdh.Bytes) (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    ((PqxdhRegistrationJointServiceSchedule.finish setup codec address raw).run owners).IsQueryBoundP
      (NativeKind (KemSK := KemSK) (Response := Response)) 1 := by
  simp only [PqxdhRegistrationJointServiceSchedule.finish, StateT.run]
  split
  · trivial
  · rw [isQueryBoundP_map_iff]
    refine IsQueryBoundP.simulateQ_of_step (compiled_root setup codec raw _) (fun query root => ?_)
      (fun query root => ?_)
    · exact query_one _ _
    · refine query_free _ _ ?_
      rcases query with query | (query | query)
      · simp [NativeKind]
      · simp [NativeKind]
      · cases query <;> simp_all [rootFinish, NativeKind]

/-- Every source request makes at most one native table request, and only if it is a table request of the source. -/
theorem client_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run owners).IsQueryBoundP
      (NativeKind (KemSK := KemSK) (Response := Response)) (if TableKind query then 1 else 0) := by
  rcases query with (coin | request) | read
  · simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
      StateT.run_lift, TableKind]
    exact query_free _ _ (by simp [NativeKind])
  · cases request with
    | create pin keyId =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          PqxdhRegistrationJointServiceSchedule.create, StateT.run, TableKind]
        exact isQueryBoundP_bind (n := 0) (m := 0) (pool_free _) fun _ _ => trivial
    | bundle address =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          PqxdhRegistrationJointServiceSchedule.bundle, StateT.run, TableKind]
        split
        · trivial
        · rw [isQueryBoundP_map_iff]
          exact pool_free _
    | accept raw =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          StateT.run_lift, TableKind]
        exact query_one _ _
    | build session payload =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          StateT.run_lift, TableKind]
        exact query_free _ _ (by simp [NativeKind])
    | finish address raw => exact finish_bound setup codec address raw owners
    | hmac key message =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          StateT.run_lift, TableKind]
        exact query_one _ _
    | hash bytes =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          StateT.run_lift, TableKind]
        exact query_free _ _ (by simp [NativeKind])
    | reveal keyId =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          StateT.run_lift, TableKind]
        exact query_free _ _ (by simp [NativeKind])
  · simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointLiveRead.clientStep, StateT.run,
      TableKind]
    split
    · trivial
    · rw [isQueryBoundP_map_iff]
      exact pool_free _

end Client

/-! ### The table cache at the cut of the source program -/

section Composite

variable {ιE ιM ιI O S α : Type} {E : OracleSpec ιE} {M : OracleSpec ιM} {I : OracleSpec ιI}

/-- Two stateful layers as one handler on the product state. -/
def compose (client : QueryImpl E (StateT O (OracleComp M))) (impl : QueryImpl M (StateT S (OracleComp I))) :
    QueryImpl E (StateT (O × S) (OracleComp I)) :=
  fun query => StateT.mk fun state => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ impl ((client query).run state.1)).run state.2

theorem compose_run (client : QueryImpl E (StateT O (OracleComp M))) (impl : QueryImpl M (StateT S (OracleComp I)))
    (work : OracleComp E α) (owners : O) (state : S) :
    (simulateQ (compose client impl) work).run (owners, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ impl ((simulateQ client work).run owners)).run state := by
  induction work using OracleComp.inductionOn generalizing owners state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      change ((fun result => (result.1.1, (result.1.2, result.2))) <$>
          (simulateQ impl ((client query).run owners)).run state) >>= _ = _
      rw [bind_map_left]
      exact bind_congr fun result => ih result.1.1 result.1.2 result.2

end Composite

section Cut

open PqxdhRegistrationJointKemCommands (SourceSpec)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-- The cut-split for the source program interpreted by the source client and native backend: at a reached cut, the keys of the table cache have grown by at most `c`, the selected accept and the `c` table requests before it fit the table budget, and the suspended continuation keeps the rest of it. -/
theorem commands_cut (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (SourceSpec KemSK) X) (n : ℕ)
    (bounded : work.IsQueryBoundP (TableKind (KemSK := KemSK)) n) (index : Nat)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK) :
    ∀ reached ∈ support (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks identityIndex publicIdentity
        (PqxdhRegistrationJointAcceptCut.scan work index) owners state), ∀ raw next,
      reached.1.1 = .pending raw next → ∃ c : ℕ, keyCount reached.2 ≤ keyCount state + c ∧ c + 1 ≤ n ∧
        ∀ reply, (next reply).IsQueryBoundP (TableKind (KemSK := KemSK)) (n - c - 1) := by
  intro reached member raw next pending
  have composed := compose_run (PqxdhRegistrationJointRevealSchedule.client setup codec)
    (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity)
    (PqxdhRegistrationJointAcceptCut.scan work index) owners state
  have lifted : (reached.1.1, (reached.1.2, reached.2)) ∈ support ((simulateQ (compose
      (PqxdhRegistrationJointRevealSchedule.client setup codec)
      (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity))
        (PqxdhRegistrationJointAcceptCut.scan work index)).run (owners, state)) := by
    rw [composed, support_map]
    exact ⟨reached, member, rfl⟩
  have step : ∀ query (current : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × NativeState KemSK),
      ∀ result ∈ support ((compose (PqxdhRegistrationJointRevealSchedule.client setup codec)
        (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity) query).run current),
      keyCount result.2.2 ≤ keyCount current.2 + ((if TableKind query then 1 else 0 : ℕ) : ℕ∞) := by
    intro query current result reachedStep
    rw [compose, StateT.run_mk, support_map] at reachedStep
    obtain ⟨inner, innerReached, rfl⟩ := reachedStep
    exact potential_run (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity)
      keyCount NativeKind (fun native nativeState nativeResult nativeReached =>
        impl_grows setup codec checks identityIndex publicIdentity native nativeState nativeResult nativeReached)
      _ _ (client_bound setup codec query current.1) current.2 inner innerReached
  exact scan_potential _ (fun current => keyCount current.2) step work n bounded index (owners, state) _ lifted raw next
    pending

end Cut

/-! ### The table cache at the cut of the KEM-ideal branch -/

section Start

open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRawOpaque (OpaqueCut OpaqueContext opaqueScan sourcePreOpaque)
open PqxdhRegistrationJointKemPostSkeleton (cacheOf sharedStart)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- An optional stateful interpretation only removes results of a program. -/
theorem support_option {κ κ' J α : Type} {spec : OracleSpec κ} {spec' : OracleSpec κ'}
    (handler : QueryImpl spec (OptionT (StateT J (OracleComp spec')))) (work : OracleComp spec α) (state : J)
    (value : α) (after : J) (reached : (some value, after) ∈ support (((simulateQ handler work).run).run state)) :
    value ∈ support work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at reached
      rw [reached.1]
      simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        mem_support_bind_iff] at reached
      obtain ⟨⟨reply, middle⟩, _, rest⟩ := reached
      cases reply with
      | none => simp at rest
      | some reply =>
          exact (mem_support_bind_iff _ _ _).mpr ⟨reply, mem_support_query query reply, ih reply middle rest⟩

/-- The table-cache keys of an active opaque cut fit the table budget together with the remaining budget of its continuation. -/
def FitsCut (n : ℕ) : OpaqueCut Reader KemSK X R → Prop
  | .complete _ => True
  | .pending _ _ _ _ native _ next => ∃ c : ℕ, (cacheKeys native.1.cache).encard ≤ c ∧ c + 1 ≤ n ∧
      ∀ reply, (next reply).IsQueryBoundP (TableKind (KemSK := KemSK)) (n - c - 1)

/-- Every cut reached by the explicit opaque scan from an empty table fits the table budget. -/
theorem opaqueScan_fits (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (n : ℕ) (bounded : work.IsQueryBoundP (TableKind (KemSK := KemSK)) n)
    (index : Nat) (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK)
    (empty : keyCount state = 0) :
    ∀ cut ∈ support (opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity observe work index
      owners state), FitsCut n cut := by
  intro cut reached
  rw [opaqueScan, mem_support_bind_iff] at reached
  obtain ⟨found, foundReached, reached⟩ := reached
  have commandsReached := PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ foundReached
  rcases scanCut : found.1.1 with result | ⟨raw, next⟩
  · rw [scanCut] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    rw [reached]
    trivial
  · rw [scanCut] at reached
    dsimp only at reached
    rcases verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with _ | value
    · rw [verified] at reached
      obtain ⟨_, rfl⟩ := PqxdhRegistrationJointKemRawOpaque.rejectRun_complete setup codec checks identityIndex
        publicIdentity observe raw next _ _ _ cut reached
      trivial
    · rw [verified] at reached
      dsimp only at reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨⟨_ | ephemeral, consumed⟩, _, reached⟩ := reached
      · obtain ⟨_, rfl⟩ := PqxdhRegistrationJointKemRawOpaque.rejectRun_complete setup codec checks identityIndex
          publicIdentity observe raw next _ _ _ cut reached
        trivial
      · simp only [support_pure, Set.mem_singleton_iff] at reached
        subst reached
        obtain ⟨c, growth, room, remaining⟩ := commands_cut setup codec checks identityIndex publicIdentity work n
          bounded index owners state found commandsReached raw next scanCut
        rw [empty, zero_add] at growth
        exact ⟨c, growth, room, remaining⟩

/-- Fit of the table cache of an active prechallenge context. -/
def Fits {count : Nat} (n : ℕ) : OpaqueContext Reader KemSK A X count → Prop
  | .ready _ _ (some cut) _ _ => FitsCut n cut
  | _ => True

theorem initial_keys (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) :
    keyCount (PqxdhRegistrationJointInitializedAccept.initial (KemSK := KemSK) created) = 0 := by
  simp [keyCount, PqxdhRegistrationJointInitializedAccept.initial, PqxdhJointDhExtractFamily.empty, cacheKeys_empty]

/-- Every prechallenge context of the KEM-ideal branch fits the table budget. -/
theorem sourcePreOpaque_fits (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) (n : ℕ)
    (bounded : work.IsQueryBoundP (TableKind (KemSK := KemSK)) n) :
    ∀ context ∈ support (sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index chosen), Fits n context := by
  intro context reached
  rw [sourcePreOpaque, mem_support_bind_iff] at reached
  obtain ⟨born, _, reached⟩ := reached
  rcases bornCase : born.1 with _ | created
  · rw [bornCase] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    rw [reached]
    trivial
  · rw [bornCase] at reached
    dsimp only at reached
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨others, _, result, resultReached, rfl⟩ := reached
    rcases cutCase : result.1 with _ | cut
    · simp only [Fits]
    · simp only [Fits]
      have scanReached := support_option _ _ _ cut result.2 (by rw [← cutCase]; exact resultReached)
      exact opaqueScan_fits setup codec checks _ _ _ work n bounded index [] _ (initial_keys created) cut scanReached

/-- Every outcome of G1's prefix for the KEM-ideal branch has a fitting active context, and its table cache is the cache of that context. -/
theorem sharedStart_fits (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (n : ℕ)
    (bounded : work.IsQueryBoundP (TableKind (KemSK := KemSK)) n) :
    ∀ start ∈ support (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index), start.1 = cacheOf start.2.2.1 ∧ Fits n start.2.2.1 := by
  intro start reached
  simp only [sharedStart, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨chosen, _, context, contextReached, encapsulated, _, rfl⟩ := reached
  exact ⟨rfl, sourcePreOpaque_fits setup codec checks ensureInit supplied decision work runtime count selected index
    chosen n bounded context contextReached⟩

end Start

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_family

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_local

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_ctx

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_romRootBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_romRootBytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_sourceRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_sourceRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_hmac

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_build

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_loggedRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_loggedRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_client

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_acceptTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.growsN_acceptTail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.grows_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.grows_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.grows_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.grows_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.impl_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.impl_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.simulate_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.simulate_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.query_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.query_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.query_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.query_one

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.afterRoot_rootless' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.afterRoot_rootless

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.tail_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.tail_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.owner_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.owner_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.simulate_one_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.simulate_one_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.simulate_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.simulate_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.simulate_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.simulate_application

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.nativeOwner_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.nativeOwner_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.compiled_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.compiled_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.pool_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.pool_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.finish_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.client_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.compose_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.compose_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.commands_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.commands_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.support_option' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.support_option

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.opaqueScan_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.opaqueScan_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.initial_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.initial_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.sourcePreOpaque_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.sourcePreOpaque_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.sharedStart_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.sharedStart_fits
