import BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree

/-!
# The opaque Beacon finish of the observer-free KEM-ideal branch (item 2, stage S0b)

This module continues the hybrid of the item 2 plan after stage S0a (`PqxdhRegistrationJointKemObserverFree`). In the observer-free branch `freeBranch`, a Beacon finish decapsulates through the private KEM pool, and the post-challenge router answers the decapsulation of the challenge ciphertext under the selected KEM creation index with the KEM candidate. The Beacon then copies that value into its 192-byte root input and reads the restricted Extract table at those bytes.

The marked branch `markedBranch` runs every Beacon finish in the opaque-handle form of `PqxdhBeaconPhase2Shared.owner`, with the handle type `PqxdhPhase2DecapsulationRouting.Shared`:

- `markedPreparation`: every preparation callback is the source's, except that the decapsulation reply becomes a handle. On the exact challenge ciphertext under the selected KEM creation index the handle is the challenge marker, and only the presence of the router's reply is used (a missing handle still rejects). Every other decapsulation carries its actual result as a known secret.
- `markedCompiler`: the root request becomes a private request with the DH coordinates and the handle (`RootSpec`). Every other tail callback is the source's.
- `markedImpl`: the source's native backend, and the private root interpreter `markedRoot`, which alone materializes the marker with the candidate, builds the source root input and reads the same table as the source root callback.

The main theorem `opaqueBranch_marked` states that the opaque raw-ordinal branch of theorem T6 equals the marked branch, as programs, for both values of the branch bit. It composes `PqxdhRegistrationJointKemObserverFree.opaqueBranch_free` (stage S0a) with `freeBranch_marked`. The proof marks the router's reply to the selected decapsulation of the challenge: `markPool` overwrites its value by the candidate, which the router absorbs (`router_absorbs`, because its reply is the candidate or a missing-handle rejection); the marking commutes with the encapsulator and the exposed-encapsulation forwarding (`markPool_actual`, `markEnc_hide`) and is pushed into every native handler step (`mark_run`). With the marking in place, the native Beacon owner and the opaque-handle owner satisfy the realization obligations of `PqxdhBeaconPhase2Shared.owner_realization` for the interpretation `interpret candidate` (`marked_calls`), so every client step has the same marked interpretation (`client_marked`), and so does every client program (`layered`).

`router_moves` states where the candidate still lives in the router: the router holding any value, with its reply to the selected decapsulation of the challenge overwritten by the candidate, is the router holding the candidate. The marked Beacon finish discards that reply's value; the remaining step that makes the router's candidate argument dead is a proof that no other post-challenge component requests that decapsulation (deferred, see the guide). These are program equalities; they charge no advantage, and no secret-input KDF context is formed.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemObserverFree

/-! ### Marking the router's reply to the selected decapsulation of the challenge -/

section Marking

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Overwrite the value of an optional private-pool decapsulation reply by `candidate`. -/
def overwrite (candidate : MlKemSharedSecret) (index : Nat) (ciphertext : MlKem768Ciphertext)
    (reply : (PqxdhLiveKemBirth.Spec KemSK).Range (.inr (.inr (.decapsulate index ciphertext)))) :
    (PqxdhLiveKemBirth.Spec KemSK).Range (.inr (.inr (.decapsulate index ciphertext))) :=
  Option.map (fun _ => candidate) reply

/-- Overwrite the value of the reply to the private-pool decapsulation of `challenge` under KEM creation index `selected` by `candidate`; every other request is forwarded unchanged. -/
noncomputable def markPool (selected : Nat) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp (PqxdhLiveKemBirth.Spec KemSK))
  | .inr (.inr (.decapsulate index ciphertext)) =>
      if index = selected ∧ ciphertext = challenge then
        overwrite candidate index ciphertext <$>
          (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.decapsulate index ciphertext)))
      else (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.decapsulate index ciphertext)))
  | .inr (.inr .create) => (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr .create))
  | .inr (.inr (.reveal index)) => (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.reveal index)))
  | .inr (.inl coin) => (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inl coin))
  | .inl query => (PqxdhLiveKemBirth.Spec KemSK).query (.inl query)

/-- The same marking on the exposed encapsulation interface. -/
noncomputable def markEnc (selected : Nat) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK)
      (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK))
  | .inl query => simulateQ PqxdhRegistrationJointKemEncapsulation.forward (markPool selected challenge candidate query)
  | .inr request => (PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query (.inr request)

/-- Marking leaves ambient coins untouched. -/
theorem markPool_coins {α : Type} (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (work : ProbComp α) :
    simulateQ (markPool (KemSK := KemSK) selected challenge candidate) (PqxdhLiveKemBirth.coins work) =
      PqxdhLiveKemBirth.coins work := by
  unfold PqxdhLiveKemBirth.coins
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- Marking commutes with the actual encapsulator. -/
theorem markPool_actual {α : Type} (setup : Setup baseSpec KemSK) (selected : Nat)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) α) :
    simulateQ (markPool selected challenge candidate) (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) work) =
      simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        (simulateQ (markEnc selected challenge candidate) work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  rcases query with query | request
  · simp only [QueryImpl.apply_compose, PqxdhRegistrationJointKemEncapsulation.actual, simulateQ_spec_query,
      markEnc, PqxdhRegistrationJointKemEncapsulation.forward_actual]
  · simp only [QueryImpl.apply_compose, PqxdhRegistrationJointKemEncapsulation.actual, markEnc,
      simulateQ_spec_query, markPool_coins]

/-- Marking commutes with the exposed-encapsulation forwarding of `KemAcceptKemCut.hide`. -/
theorem markEnc_hide {α : Type} (setup : Setup baseSpec KemSK) (selected : Nat)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) α) :
    simulateQ (markEnc selected challenge candidate) (PqxdhRegistrationJointAcceptKemCut.hide setup work) =
      PqxdhRegistrationJointAcceptKemCut.hide setup (simulateQ (markEnc selected challenge candidate) work) := by
  unfold PqxdhRegistrationJointAcceptKemCut.hide
  have forwardMark : markEnc (KemSK := KemSK) selected challenge candidate ∘ₛ
      PqxdhRegistrationJointKemEncapsulation.forward =
      PqxdhRegistrationJointKemEncapsulation.forward ∘ₛ markPool selected challenge candidate := by
    funext query
    simp only [QueryImpl.apply_compose, PqxdhRegistrationJointKemEncapsulation.forward, simulateQ_spec_query, markEnc]
  rw [← QueryImpl.simulateQ_compose, forwardMark, QueryImpl.simulateQ_compose, markPool_actual]

/-- Marking a stateful interpretation is the interpretation by the handler whose every step is marked. -/
theorem mark_run {ι' σ α : Type} {spec' : OracleSpec ι'}
    (mark : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK)
      (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK)))
    (impl : QueryImpl spec' (StateT σ (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK))))
    (work : OracleComp spec' α) (state : σ) :
    simulateQ mark ((simulateQ impl work).run state) =
      (simulateQ (fun query => StateT.mk fun current => simulateQ mark ((impl query).run current)) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk]
      exact bind_congr fun result => ih result.1 result.2

/-- Marking moves the candidate out of the router: the erased post-challenge router holding any value `other`, with its reply to the selected decapsulation of the challenge overwritten by `candidate`, is the router holding `candidate`. Its reply to that request is the held value or a missing-handle rejection, and no other reply or state change depends on the held value. -/
theorem router_moves (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (primitives : Primitives)
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (challenge : MlKem768Ciphertext) (other candidate : MlKemSharedSecret) :
    eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post primitives kem selected reservation challenge other) ∘ₛ
        markPool selected challenge candidate =
      eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post primitives kem selected reservation challenge candidate) := by
  funext query
  rcases query with joint | (coin | (_ | ⟨index, ciphertext⟩ | index))
  · simp only [QueryImpl.apply_compose, markPool, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, markPool, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, markPool, simulateQ_spec_query]
    rfl
  · by_cases target : index = selected ∧ ciphertext = challenge
    · obtain ⟨rfl, rfl⟩ := target
      simp only [QueryImpl.apply_compose, markPool, and_self, ↓reduceIte, simulateQ_map, simulateQ_spec_query]
      apply OptionT.ext
      apply StateT.ext
      intro state
      simp only [OptionT.run_map, StateT.run_map]
      simp only [eraseOptionImpl, OptionT.run_mk,
        PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine, PqxdhDynamicKemRouter.post,
        PqxdhDynamicKemRouter.router, StateT.run, StateT.mk, Functor.map_map]
      cases found : PqxdhDynamicKemRouter.lookup reservation (eraseRouter state.2) index with
      | none =>
          simp [PqxdhDynamicKemRouter.postDecapsulation, found, eraseJoint]
          rfl
      | some pair =>
          simp [PqxdhDynamicKemRouter.postDecapsulation, found, eraseJoint]
          exact ⟨rfl, rfl⟩
    · simp only [QueryImpl.apply_compose, markPool, target, ↓reduceIte, simulateQ_spec_query]
      apply OptionT.ext
      apply StateT.ext
      intro state
      simp only [eraseOptionImpl, OptionT.run_mk,
        PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine, PqxdhDynamicKemRouter.post,
        PqxdhDynamicKemRouter.router, StateT.run, StateT.mk]
      have different : ¬ (index = selected ∧ ciphertext = challenge) := target
      cases found : PqxdhDynamicKemRouter.lookup reservation (eraseRouter state.2) index with
      | none => simp [PqxdhDynamicKemRouter.postDecapsulation, found, eraseJoint]
      | some pair =>
          by_cases same : index = selected
          · have distinct : ciphertext ≠ challenge := fun equal => different ⟨same, equal⟩
            simp [PqxdhDynamicKemRouter.postDecapsulation, same, distinct, eraseJoint]
          · simp [PqxdhDynamicKemRouter.postDecapsulation, found, same, eraseJoint]
  · simp only [QueryImpl.apply_compose, markPool, simulateQ_spec_query]
    rfl

/-- The erased post-challenge router absorbs the marking by its own candidate. -/
theorem router_absorbs (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (primitives : Primitives)
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post primitives kem selected reservation challenge candidate) ∘ₛ
        markPool selected challenge candidate =
      eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post primitives kem selected reservation challenge candidate) :=
  router_moves kem primitives selected reservation challenge candidate candidate

end Marking

/-! ### The marked Beacon finish -/

section Marked

open PqxdhRefinement PqxdhJointGapDh
open PqxdhRegistrationJointBundle (Identity Key)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhServerAuthNative (NativeGame NativeState sourceRoot)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The private handle of a Beacon decapsulation: the challenge marker or a known shared secret. -/
abbrev Shared := PqxdhPhase2DecapsulationRouting.Shared

/-- The DH coordinates and handle of a pending Beacon root. -/
abbrev Secrets := PqxdhBeaconPhase2Shared.Secrets Shared

/-- One private root request per pending Beacon root: its coordinates and handle. -/
abbrev RootSpec : OracleSpec Secrets := fun _ => Option Word32

/-- The source client's interface with the private Beacon root request added. -/
abbrev MarkedSpec (KemSK Response : Type) := PqxdhRegistrationJointServiceSchedule.Spec KemSK Response + RootSpec

/-- The interpretation of a handle, available only to the private root interpreter. -/
def interpret (candidate : MlKemSharedSecret) (shared : Shared) : Word32 :=
  PqxdhRootTableInitialization.rootArray (PqxdhPhase2DecapsulationRouting.materialize candidate shared)

/-- The handle of a decapsulation reply: the challenge marker for the selected key on the exact challenge ciphertext, the known secret otherwise. Only the reply's presence is used for the marker. -/
def toHandle (target : Bool) (index : Nat) (ciphertext : MlKem768Ciphertext)
    (reply : (PqxdhLiveKemBirth.Spec KemSK).Range (.inr (.inr (.decapsulate index ciphertext)))) : Option Shared :=
  if target then Option.map (fun _ => .challenge) reply else Option.map .known reply

/-- The Beacon preparation with an opaque decapsulation handle. Every callback is the source's, except that the decapsulation reply is returned as a handle. -/
noncomputable def markedPreparation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhBeaconPhase2Shared.Spec Identity ScalarBytes Key Nat Response Shared)
      (OracleComp (PqxdhLiveKemBirth.Spec KemSK))
  | .decode raw => pure (codec.read2 raw)
  | .ciphertext response => pure (codec.ciphertext response)
  | .ephemeral response => pure (codec.ephemeral response)
  | .serverIdentity response => pure (codec.serverIdentity response)
  | .publicConversion server => pure ((setup.source.crypto.xpkConv (absBytes server)).bind toWord32)
  | .privateConversion identity => pure (some identity.1)
  | .decapsulate ciphertext key =>
      toHandle (decide (key.2 = selected ∧ PqxdhPhase2InputBytes.ciphertext ciphertext = challenge)) key.2
          (PqxdhPhase2InputBytes.ciphertext ciphertext) <$>
        (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.decapsulate key.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))))
  | .dhPair scalar point => pure ((sourceScalarDh setup.source.crypto scalar
      (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray)
  | .dhIdentity index point =>
      (fun reply => Option.map PqxdhRootTableInitialization.rootArray reply.join) <$>
        (PqxdhLiveKemBirth.Spec KemSK).query (.inl (.inr (.service index (.staticDh (PqxdhPhase2GapDhSource.peer point)))))
  | .assignedId response => pure (codec.assignedId response)
  | .eraseShared _ => pure ()

/-- Forward a private-pool request to the marked interface. -/
def markedPoolLift : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp (MarkedSpec KemSK Response)) :=
  fun query => (MarkedSpec KemSK Response).query (.inl (.inl (.inl query)))

/-- The opaque-handle Beacon owner's callbacks on the marked interface: preparation through the private pool, the private root request with coordinates and handle, and every other tail callback unchanged. -/
noncomputable def markedCompiler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity ScalarBytes Key Nat Response Shared)
      (OracleComp (MarkedSpec KemSK Response))
  | .inl query => simulateQ markedPoolLift (markedPreparation setup codec selected challenge query)
  | .inr (.inl raw) => (MarkedSpec KemSK Response).query (.inl (.inl (.inr (.inl raw))))
  | .inr (.inr (.root secrets)) => (MarkedSpec KemSK Response).query (.inr secrets)
  | .inr (.inr (.initial request)) => (MarkedSpec KemSK Response).query (.inl (.inl (.inr (.inr (.initial request)))))
  | .inr (.inr (.application response)) =>
      (MarkedSpec KemSK Response).query (.inl (.inl (.inr (.inr (.application response)))))

/-- The marked Beacon finish: the opaque-handle owner of `PqxdhBeaconPhase2Shared.owner` in place of the native owner, with the same owner lookup and reinstallation. -/
noncomputable def markedFinish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (address : Nat) (raw : Pqxdh.Bytes) :
    StateT (List EncodedEntry) (OracleComp (MarkedSpec KemSK Response)) (Option Pqxdh.Bytes) := fun owners =>
  match owners[address]? with
  | none => pure (none, owners)
  | some entry =>
    (fun result => (result.1, owners.set address (entry.1, entry.2.1, result.2))) <$>
      simulateQ (markedCompiler setup codec selected challenge)
        (PqxdhBeaconPhase2Shared.owner codec.frameRead raw entry.2.2)

/-- Lift a source client step to the marked interface. -/
def markedLift : QueryImpl (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response)
    (OracleComp (MarkedSpec KemSK Response)) :=
  fun query => (MarkedSpec KemSK Response).query (.inl query)

def liftClient {α : Type} (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α) :
    StateT (List EncodedEntry) (OracleComp (MarkedSpec KemSK Response)) α :=
  fun owners => simulateQ markedLift (work.run owners)

/-- The source client with the marked Beacon finish; every other request is the source's. -/
noncomputable def markedClient (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (StateT (List EncodedEntry) (OracleComp (MarkedSpec KemSK Response)))
  | .inl (.inr (.finish address raw)) => markedFinish setup codec selected challenge address raw
  | query => liftClient (PqxdhRegistrationJointRevealSchedule.client setup codec query)

/-- The private root interpreter: it materializes the handle with `candidate`, builds the source root input and reads the same restricted Extract table as the source root callback. -/
noncomputable def markedRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (secrets : Secrets) : NativeGame KemSK (Option Word32) :=
  match beaconcrypt_core.pqxdh.build_root_key_input (PqxdhBeaconPhase2Shared.concreteSecrets (interpret candidate) secrets) with
  | .ok (.Ok input) => sourceRoot hmac input
  | _ => pure none

/-- The native backend of the marked interface: the source backend, and the private root interpreter. -/
noncomputable def markedImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) :
    QueryImpl (MarkedSpec KemSK Response) (PqxdhRegistrationJointKemEncapsulation.Client KemSK) :=
  PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity +
    (fun secrets => PqxdhRegistrationJointKemEncapsulation.lift (KemSK := KemSK)
      (PqxdhRegistrationJointOpenBackend.native (KemSK := KemSK) (markedRoot setup.hmac candidate secrets)) :
      QueryImpl RootSpec (PqxdhRegistrationJointKemEncapsulation.Client KemSK))

end Marked

/-! ### Realization of the marked Beacon owner -/

section Realization

open PqxdhRefinement PqxdhJointGapDh
open PqxdhRegistrationJointBundle (Identity Key)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhServerAuthNative (NativeGame NativeState sourceRoot eraseObservers)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Mark every step of a stateful handler whose values are programs on the exposed encapsulation interface. -/
noncomputable def markHandler {ι' σ : Type} {spec' : OracleSpec ι'} (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret)
    (impl : QueryImpl spec' (StateT σ (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK)))) :
    QueryImpl spec' (StateT σ (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK))) :=
  fun query => StateT.mk fun current => simulateQ (markEnc selected challenge candidate) ((impl query).run current)

/-- The erased native source backend with every step marked. -/
noncomputable abbrev sourceMarked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) :=
  markHandler selected challenge candidate
    (eraseImpl eraseObservers (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity))

/-- The erased marked backend with every step marked. -/
noncomputable abbrev markedMarked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) :=
  markHandler selected challenge candidate
    (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))

theorem markedMarked_inl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) :
    markedMarked setup codec checks identityIndex publicIdentity selected challenge candidate (.inl query) =
      sourceMarked setup codec checks identityIndex publicIdentity selected challenge candidate query :=
  rfl

theorem sourceMarked_pool (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) :
    sourceMarked (Response := Response) setup codec checks identityIndex publicIdentity selected challenge candidate
        (.inl (.inl query)) =
      StateT.mk fun state => (fun answer => (answer, eraseObservers state)) <$>
        simulateQ PqxdhRegistrationJointKemEncapsulation.forward (markPool selected challenge candidate query) := by
  funext state
  simp [markHandler, eraseImpl, PqxdhRegistrationJointKemEncapsulation.impl, PqxdhRegistrationJointOpenBackend.impl,
    PqxdhRegistrationJointOpenBackend.pool, PqxdhRegistrationJointKemEncapsulation.lift, StateT.run, StateT.mk,
    markEnc, PqxdhRegistrationJointKemEncapsulation.forward, Functor.map_map, simulateQ_map]

/-- The source backend's private-pool steps, as seen by the native Beacon preparation. -/
theorem native_pool_route {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) :
    simulateQ (sourceMarked setup codec checks identityIndex publicIdentity selected challenge candidate ∘ₛ
        PqxdhRegistrationJointServiceSchedule.finishLift)
      (simulateQ (PqxdhRegistrationJointFinishCompiler.poolLift (Response := Response)) work) =
      simulateQ (fun query => sourceMarked (Response := Response) setup codec checks identityIndex publicIdentity
        selected challenge candidate (.inl (.inl query))) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, PqxdhRegistrationJointFinishCompiler.poolLift, simulateQ_spec_query,
    PqxdhRegistrationJointServiceSchedule.finishLift]

/-- The marked backend's private-pool steps, as seen by the marked Beacon preparation. -/
theorem marked_pool_route {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) :
    simulateQ (markedMarked setup codec checks identityIndex publicIdentity selected challenge candidate)
      (simulateQ (markedPoolLift (Response := Response)) work) =
      simulateQ (fun query => sourceMarked (Response := Response) setup codec checks identityIndex publicIdentity
        selected challenge candidate (.inl (.inl query))) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, markedPoolLift, simulateQ_spec_query]
  rfl

/-- The native Beacon owner, compiled and interpreted by the marked source backend, and the opaque-handle owner, compiled and interpreted by the marked backend, satisfy the realization obligations of `PqxdhBeaconPhase2Shared` with the handle interpretation `interpret candidate`. -/
theorem marked_calls (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) :
    PqxdhBeaconPhase2Shared.FullCalls (interpret candidate)
      ((sourceMarked setup codec checks identityIndex publicIdentity selected challenge candidate ∘ₛ
          PqxdhRegistrationJointServiceSchedule.finishLift) ∘ₛ PqxdhRegistrationJointFinishCompiler.compiler setup codec)
      (markedMarked setup codec checks identityIndex publicIdentity selected challenge candidate ∘ₛ
          markedCompiler setup codec selected challenge) := by
  have nativePrep : ∀ query,
      ((sourceMarked setup codec checks identityIndex publicIdentity selected challenge candidate ∘ₛ
          PqxdhRegistrationJointServiceSchedule.finishLift) ∘ₛ PqxdhRegistrationJointFinishCompiler.compiler setup codec)
        (.inl query) =
      simulateQ (fun query => sourceMarked (Response := Response) setup codec checks identityIndex publicIdentity
        selected challenge candidate (.inl (.inl query))) (PqxdhRegistrationJointPreparation.compiler setup codec query) := by
    intro query
    simp only [QueryImpl.apply_compose, PqxdhRegistrationJointFinishCompiler.compiler]
    exact native_pool_route setup codec checks identityIndex publicIdentity selected challenge candidate _
  have markedPrep : ∀ query,
      (markedMarked setup codec checks identityIndex publicIdentity selected challenge candidate ∘ₛ
          markedCompiler setup codec selected challenge) (.inl query) =
      simulateQ (fun query => sourceMarked (Response := Response) setup codec checks identityIndex publicIdentity
        selected challenge candidate (.inl (.inl query))) (markedPreparation setup codec selected challenge query) := by
    intro query
    simp only [QueryImpl.apply_compose, markedCompiler]
    exact marked_pool_route setup codec checks identityIndex publicIdentity selected challenge candidate _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro raw
    rw [nativePrep, markedPrep]
    rfl
  · intro response
    rw [nativePrep, markedPrep]
    rfl
  · intro response
    rw [nativePrep, markedPrep]
    rfl
  · intro response
    rw [nativePrep, markedPrep]
    rfl
  · intro value
    rw [nativePrep, markedPrep]
    rfl
  · intro identity
    rw [nativePrep, markedPrep]
    rfl
  · intro ciphertext key
    rw [nativePrep, markedPrep]
    have decapRoute : simulateQ (fun query => sourceMarked (Response := Response) setup codec checks identityIndex
          publicIdentity selected challenge candidate (.inl (.inl query)))
        (PqxdhRegistrationJointPreparation.compiler setup codec (.decapsulate ciphertext key)) =
        Option.map PqxdhRootTableInitialization.rootArray <$>
          (sourceMarked (Response := Response) setup codec checks identityIndex publicIdentity selected challenge
            candidate (.inl (.inl (.inr (.inr (.decapsulate key.2 (PqxdhPhase2InputBytes.ciphertext ciphertext)))))) :
            StateT (NativeState KemSK) (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK))
              (Option MlKemSharedSecret)) := by
      simp only [PqxdhRegistrationJointPreparation.compiler]
      erw [simulateQ_map, simulateQ_spec_query]
    rw [decapRoute]
    simp only [markedPreparation, simulateQ_map, simulateQ_spec_query, sourceMarked_pool]
    apply StateT.ext
    intro state
    simp only [StateT.run_map, StateT.run_mk]
    by_cases target : key.2 = selected ∧ PqxdhPhase2InputBytes.ciphertext ciphertext = challenge
    · simp only [markPool, target, and_self, ↓reduceIte, simulateQ_map, simulateQ_spec_query, Functor.map_map]
      erw [StateT.run_map, StateT.run_mk, Functor.map_map]
      congr 1
      funext reply
      cases reply <;> rfl
    · simp only [markPool, target, ↓reduceIte, simulateQ_spec_query, Functor.map_map]
      erw [StateT.run_map, StateT.run_mk, Functor.map_map]
      congr 1
      funext reply
      cases reply <;> rfl
  · intro pair value
    rw [nativePrep, markedPrep]
    rfl
  · intro identity value
    rw [nativePrep, markedPrep]
    rfl
  · intro response
    rw [nativePrep, markedPrep]
    rfl
  · intro secrets
    rw [nativePrep, markedPrep]
    rfl
  · intro secrets rootInput built
    funext state
    simp [QueryImpl.apply_compose, PqxdhRegistrationJointFinishCompiler.compiler, markedCompiler,
      PqxdhRegistrationJointServiceSchedule.finishLift, markHandler, eraseImpl, markedImpl,
      markedRoot, built, PqxdhRegistrationJointKemEncapsulation.impl, PqxdhRegistrationJointOpenBackend.impl,
      PqxdhServerAuthNative.sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot, StateT.run, StateT.mk]
  · intro request
    rfl
  · intro response
    rfl
  · intro query
    simp only [QueryImpl.apply_compose, PqxdhRegistrationJointFinishCompiler.compiler, markedCompiler,
      PqxdhRegistrationJointServiceSchedule.finishLift, simulateQ_spec_query]
    rfl

/-- The native Beacon owner and the opaque-handle owner have the same marked interpretation (`PqxdhBeaconPhase2Shared.owner_realization`). -/
theorem owner_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationJointBundle.Owner) :
    simulateQ (sourceMarked setup codec checks identityIndex publicIdentity selected challenge candidate)
        (simulateQ PqxdhRegistrationJointServiceSchedule.finishLift
          (simulateQ (PqxdhRegistrationJointFinishCompiler.compiler setup codec)
            (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner))) =
      simulateQ (markedMarked setup codec checks identityIndex publicIdentity selected challenge candidate)
        (simulateQ (markedCompiler setup codec selected challenge)
          (PqxdhBeaconPhase2Shared.owner codec.frameRead raw owner)) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  exact PqxdhBeaconPhase2Shared.owner_realization (interpret candidate) _ _
    (marked_calls setup codec checks identityIndex publicIdentity selected challenge candidate)
    codec.frameRead raw owner

/-- The source Beacon finish and the marked Beacon finish have the same marked interpretation, for every owner list. -/
theorem finish_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (address : Nat) (raw : Pqxdh.Bytes)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    simulateQ (sourceMarked setup codec checks identityIndex publicIdentity selected challenge candidate)
        ((PqxdhRegistrationJointServiceSchedule.finish setup codec address raw).run owners) =
      simulateQ (markedMarked setup codec checks identityIndex publicIdentity selected challenge candidate)
        ((markedFinish setup codec selected challenge address raw).run owners) := by
  simp only [PqxdhRegistrationJointServiceSchedule.finish, markedFinish, StateT.run]
  cases found : owners[address]? with
  | none => simp
  | some entry =>
      simp only [simulateQ_map]
      rw [owner_marked]

/-- Lifting a source client step to the marked interface does not change its marked interpretation. -/
theorem lift_marked {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    simulateQ (sourceMarked setup codec checks identityIndex publicIdentity selected challenge candidate)
        (work.run owners) =
      simulateQ (markedMarked setup codec checks identityIndex publicIdentity selected challenge candidate)
        ((liftClient work).run owners) := by
  change _ = simulateQ _ (simulateQ markedLift (work.run owners))
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, markedLift, simulateQ_spec_query]
  rfl

/-- Every step of the source client and of the marked client has the same marked interpretation. -/
theorem client_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    simulateQ (sourceMarked setup codec checks identityIndex publicIdentity selected challenge candidate)
        ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run owners) =
      simulateQ (markedMarked setup codec checks identityIndex publicIdentity selected challenge candidate)
        ((markedClient setup codec selected challenge query).run owners) := by
  rcases query with (coin | request) | read
  · exact lift_marked setup codec checks identityIndex publicIdentity selected challenge candidate _ owners
  · cases request with
    | finish address raw =>
        exact finish_marked setup codec checks identityIndex publicIdentity selected challenge candidate address raw owners
    | _ => exact lift_marked setup codec checks identityIndex publicIdentity selected challenge candidate _ owners
  · exact lift_marked setup codec checks identityIndex publicIdentity selected challenge candidate _ owners

end Realization

/-! ### The marked post-challenge phase and branch -/

section Assembly

open PqxdhServerAuthNative (NativeState eraseObservers)
open PqxdhRegistrationJointKemEncapsulation (actual)
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointKemResume (ResultState)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointAcceptKemCut (tagged hide)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemOpaqueResume (liftImpl clientNative forwardClient)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext toContext sourcePreOpaque opaqueBranch)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- Two stateful client layers with the same interpretation of every step have the same interpretation of every program. -/
theorem layered {ι₁ ι₂ ι₃ O α : Type} {specR : OracleSpec ι₁} {spec₁ : OracleSpec ι₂} {spec₂ : OracleSpec ι₃}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (client₁ : QueryImpl specR (StateT O (OracleComp spec₁))) (client₂ : QueryImpl specR (StateT O (OracleComp spec₂)))
    (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (step : ∀ query owners, simulateQ impl₁ ((client₁ query).run owners) = simulateQ impl₂ ((client₂ query).run owners))
    (work : OracleComp specR α) (owners : O) :
    simulateQ impl₁ ((simulateQ client₁ work).run owners) = simulateQ impl₂ ((simulateQ client₂ work).run owners) := by
  induction work using OracleComp.inductionOn generalizing owners with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [step query owners]
      exact bind_congr fun result => ih result.1 result.2

/-- The marked opaque resumption: the observer-free resumption with the marked client and the marked native backend, whose private root interpreter alone holds `candidate`. -/
noncomputable def markedResume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R) := do
  let answer ← (simulateQ (eraseImpl eraseObservers (liftImpl clientNative setup native.2.sessions candidate forwardClient))
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge native.2 consumed)).run (eraseObservers native)
  hide setup ((simulateQ (eraseImpl eraseObservers
      (markedImpl setup codec checks identityIndex publicIdentity candidate))
    ((simulateQ (markedClient setup codec selected ciphertext)
      (tagged observe raw next answer.1)).run owners)).run answer.2)

/-- After marking, the observer-free resumption and the marked resumption are the same program. -/
theorem resume_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    simulateQ (markEnc selected ciphertext candidate)
        (freeResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
          next ciphertext candidate) =
      simulateQ (markEnc selected ciphertext candidate)
        (markedResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
          next selected ciphertext candidate) := by
  unfold freeResume markedResume
  simp only [simulateQ_bind, markEnc_hide]
  refine bind_congr fun answer => ?_
  congr 1
  rw [mark_run, mark_run]
  exact congrArg (fun work => StateT.run work answer.2)
    (layered _ _ _ _ (client_marked setup codec checks identityIndex publicIdentity selected ciphertext candidate) _ owners)

/-- The marked postchallenge step: the observer-free postchallenge step with the marked resumption. -/
noncomputable def markedPost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Bool count) := do
  match transcript.context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners next)) state _ =>
    if value.keys.pqKey = transcript.publicKey then
      let reached ← (((simulateQ (eraseOptionImpl eraseJoint
          (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
            transcript.ciphertext candidate))
        (simulateQ (actual setup) (markedResume setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners next selected.val
          transcript.ciphertext candidate))).run).run (eraseJoint state))
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- The observer-free postchallenge step equals the marked postchallenge step. -/
theorem post_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    freePost setup codec checks decision count selected transcript candidate =
      markedPost setup codec checks decision count selected transcript candidate := by
  obtain ⟨publicKey, ciphertext, context⟩ := transcript
  cases context with
  | failed state => rfl
  | ready created others cut state runtime =>
    cases cut with
    | none => rfl
    | some cut =>
      cases cut with
      | complete outcome => rfl
      | pending raw value ephemeral consumed native owners next =>
        by_cases active : value.keys.pqKey = publicKey
        · simp only [freePost, markedPost, active, ↓reduceIte]
          have absorb : ∀ (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK)
              (Outcome KemSK Bool)),
              simulateQ (eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
                (PqxdhDynamicKemRouter.selectedReservation selected publicKey others) ciphertext candidate))
                (simulateQ (actual setup) work) =
              simulateQ (eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
                (PqxdhDynamicKemRouter.selectedReservation selected publicKey others) ciphertext candidate))
                (simulateQ (actual setup) (simulateQ (markEnc selected.val ciphertext candidate) work)) := by
            intro work
            conv_lhs => rw [← router_absorbs setup.kem setup.joint selected.val
              (PqxdhDynamicKemRouter.selectedReservation selected publicKey others) ciphertext candidate]
            rw [QueryImpl.simulateQ_compose, markPool_actual]
          rw [absorb]
          conv_rhs => rw [absorb]
          rw [resume_marked]
        · simp only [freePost, markedPost, active, ↓reduceIte]

/-- The marked opaque branch: the observer-free branch with the marked postchallenge step. -/
noncomputable def markedBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (markedPost setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- The observer-free branch equals the marked branch. -/
theorem freeBranch_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    freeBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      markedBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real := by
  unfold freeBranch markedBranch
  simp only [post_marked]

/-- Stage S0b. The opaque raw-ordinal branch (theorem T6) equals the marked branch, as programs and for both values of the branch bit. In the marked branch every Beacon finish carries an opaque decapsulation handle: on the exact challenge ciphertext under the selected KEM creation index the handle is the challenge marker, whose value is never read, and every other decapsulation carries its actual result; the Beacon's root request is a private request with the DH coordinates and the handle, answered by the private root interpreter, which alone materializes the marker with the candidate. -/
theorem opaqueBranch_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      markedBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real :=
  (opaqueBranch_free setup codec checks ensureInit supplied decision work runtime count selected index real).trans
    (freeBranch_marked setup codec checks ensureInit supplied decision work runtime count selected index real)

end Assembly

end BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.markPool_coins' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.markPool_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.markPool_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.markPool_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.markEnc_hide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.markEnc_hide

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.mark_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.mark_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.router_moves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.router_moves

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.router_absorbs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.router_absorbs

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.markedMarked_inl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.markedMarked_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.sourceMarked_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.sourceMarked_pool

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.native_pool_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.native_pool_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.marked_pool_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.marked_pool_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.marked_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.marked_calls

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.owner_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.owner_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.finish_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.finish_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.lift_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.lift_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.client_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.client_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.layered' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.layered

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.resume_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.resume_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.post_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.post_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.freeBranch_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.freeBranch_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.opaqueBranch_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish.opaqueBranch_marked
