import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplitPrefix
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCosts

/-!
# The table reads after the cut (item 2, stage S1c, post-challenge accounting)

This module bounds the table reads of the skeleton's post-challenge client of stage S1b (`PqxdhRegistrationJointKemPostSkeleton.sharedClient`) by the remaining table budget of the source continuation after the cut, plus one for the Server's resumption.

- Every native step of the skeleton makes at most one table read (hidden or direct), and only on a table request of the grouped interface: a raw accept, a public HMAC, a Beacon tail root callback or a grouped Beacon finish (`skelImpl_reads`); the Server's resumption interpreter makes at most one, on its private root request (`resumeImpl_reads`).
- Every source request makes at most one table request of the grouped interface, and only if it is a table request of the source (`groupedClient_bound`); the resumption makes at most one root request (`resume_root`).
- The actual encapsulator, the router and the CCA evaluation forward table reads one for one and add none (`fwd_reads`, `fwdOption_reads`).
- Consequently the client makes at most `1 + m` direct reads when the continuation makes at most `m` table requests (`sharedClient_direct`).
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)
open PqxdhRegistrationJointKemPostSkeleton

/-! ### Table reads -/

section Reads

variable {κ V : Type} {A : OracleSpec κ}

/-- A table read, hidden or direct: a request of the right summand. -/
def tableRead? {κ₁ κ₂ : Type} : κ₁ ⊕ κ₂ → Bool
  | .inr _ => true
  | .inl _ => false

/-- A direct table read: a request of the right summand of the right summand. -/
def directRead? {κ₁ κ₂ κ₃ : Type} : κ₁ ⊕ (κ₂ ⊕ κ₃) → Bool
  | .inr (.inr _) => true
  | _ => false

theorem direct_table {κ₁ κ₂ κ₃ : Type} (query : κ₁ ⊕ (κ₂ ⊕ κ₃)) (direct : directRead? query = true) :
    tableRead? query = true := by
  rcases query with query | query
  · simp [directRead?] at direct
  · rfl

/-- A lifted base program makes no table read. -/
theorem liftComp_reads {α : Type} (work : OracleComp A α) :
    (OracleComp.liftComp work (A + TSpec V)).IsQueryBoundP (fun query => tableRead? query = true) 0 := by
  exact IsQueryBoundP.liftComp_subSpec (p := fun _ => False) (fun query => by simp [tableRead?])
    (PqxdhRegistrationJointBeaconOpaqueFinishRouter.free_false work)

/-- Forwarding through a stateless interpreter keeps every table read and adds none. -/
theorem fwd_reads {κ' α : Type} {B : OracleSpec κ'} (layer : QueryImpl A (OracleComp B))
    (work : OracleComp (A + TSpec V) α) (n : ℕ) (bounded : work.IsQueryBoundP (fun query => tableRead? query = true) n) :
    (simulateQ (fwd (T := TSpec V) layer) work).IsQueryBoundP (fun query => tableRead? query = true) n := by
  refine IsQueryBoundP.simulateQ_of_step bounded (fun query read => ?_) (fun query read => ?_)
  · rcases query with query | query
    · simp [tableRead?] at read
    · exact query_one _ _
  · rcases query with query | query
    · exact liftComp_reads _
    · simp [tableRead?] at read

/-- Forwarding through an optional stateful interpreter keeps every table read and adds none. -/
theorem fwdOption_reads {κ' J α : Type} {B : OracleSpec κ'} (layer : QueryImpl A (OptionT (StateT J (OracleComp B))))
    (work : OracleComp (A + TSpec V) α) (n : ℕ) (bounded : work.IsQueryBoundP (fun query => tableRead? query = true) n)
    (state : J) :
    (((simulateQ (fwdOption (T := TSpec V) layer) work).run).run state).IsQueryBoundP
      (fun query => tableRead? query = true) n := by
  refine isQueryBoundP_option_of_step _ work n bounded (fun query current => ?_) state
  rcases query with query | query
  · simp only [tableRead?, Bool.false_eq_true, ite_false]
    exact liftComp_reads _
  · simp only [tableRead?, ite_true]
    rw [fwdOption_inr, isQueryBoundP_map_iff]
    exact query_one _ _

end Reads

/-! ### Table reads of the skeleton's native layer -/

section Native

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- A native-layer program of the skeleton makes at most `k` table reads. -/
def ReadsN {α : Type} (work : NGame KemSK V α) (k : ℕ) : Prop :=
  ∀ state, (work.run state).IsQueryBoundP (fun query => tableRead? query = true) k

/-- A native-layer handler step of the skeleton makes at most `k` table reads. -/
def ReadsC {α : Type} (work : SClient KemSK V α) (k : ℕ) : Prop :=
  ∀ state, (work.run state).IsQueryBoundP (fun query => tableRead? query = true) k

theorem readsN_pure {α : Type} (value : α) : ReadsN (pure value : NGame KemSK V α) 0 :=
  fun _ => trivial

theorem readsN_bind {α β : Type} {work : NGame KemSK V α} {next : α → NGame KemSK V β} {a b : ℕ}
    (first : ReadsN work a) (rest : ∀ value, ReadsN (next value) b) : ReadsN (work >>= next) (a + b) := by
  intro state
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (first state) fun result _ => rest result.1 result.2

theorem readsN_mono {α : Type} {work : NGame KemSK V α} {a b : ℕ} (reads : ReadsN work a) (le : a ≤ b) :
    ReadsN work b :=
  fun state => (reads state).mono le

theorem readsN_map {α β : Type} (f : α → β) {work : NGame KemSK V α} {k : ℕ} (reads : ReadsN work k) :
    ReadsN (f <$> work) k := by
  intro state
  rw [StateT.run_map, isQueryBoundP_map_iff]
  exact reads state

theorem readsN_game {α : Type} (work : StateT (GameState KemSK) ProbComp α) : ReadsN (gameStep (V := V) work) 0 := by
  intro state
  rw [PqxdhRegistrationJointKemPostSkeleton.gameStep_run, isQueryBoundP_map_iff]
  exact liftComp_reads _

theorem readsN_table (point : Pqxdh.Bytes) : ReadsN (tableRead (KemSK := KemSK) (V := V) point) 1 := by
  intro state
  rw [PqxdhRegistrationJointKemPostSkeleton.tableRead_eq, isQueryBoundP_map_iff]
  exact query_one _ _

theorem readsN_value (point : PqxdhCorrelatedExtractFamily.Message) :
    ReadsN (valueRead (KemSK := KemSK) (V := V) point) 1 := by
  intro state
  rw [PqxdhRegistrationJointKemPostSkeleton.valueRead_eq, isQueryBoundP_map_iff]
  exact query_one _ _

theorem readsN_set (game : GameState KemSK) : ReadsN (setGame (V := V) game) 0 := fun _ => trivial

theorem readsN_modify (change : GameState KemSK → GameState KemSK) : ReadsN (modifyGame (V := V) change) 0 :=
  fun _ => trivial

theorem readsN_mark (index : Nat) (value : V) : ReadsN (mark (KemSK := KemSK) index value) 0 := fun _ => trivial

theorem readsN_consume (rid : beaconcrypt_core.pqxdh.RegistrationId) :
    ReadsN (consumeGame (KemSK := KemSK) (V := V) rid) 0 := fun _ => trivial

theorem readsC_liftT {α : Type} {work : NGame KemSK V α} {k : ℕ} (reads : ReadsN work k) : ReadsC (liftT work) k :=
  fun state => fwd_reads _ _ k (reads state)

theorem readsC_forward (query : (Enc KemSK).Domain) :
    ReadsC (fun state => (fun reply => (reply, state)) <$> encLift (V := V) query :
      SClient KemSK V (Enc KemSK |>.Range query)) 0 := by
  intro state
  change ((fun reply => (reply, state)) <$> encLift (V := V) query).IsQueryBoundP _ 0
  rw [isQueryBoundP_map_iff]
  exact query_free _ _ (by simp [tableRead?])

end Native

/-! ### Table reads of each skeleton step -/

section Handlers

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- The table requests of the grouped interface: the raw accept, the public HMAC, the Beacon tail's root callback and the grouped Beacon finish. -/
def groupKind : (GSpec KemSK Response).Domain → Bool
  | .inl (.inl (.inr (.inr (.root _)))) => true
  | .inl (.inr (.accept _)) => true
  | .inl (.inr (.hmac _ _)) => true
  | .inr _ => true
  | _ => false

/-- The private root request of the Server's resumption. -/
def resumeRoot : (PqxdhRegistrationJointKemOpaqueResume.Spec Reader KemSK).Domain → Bool
  | .inr (.inl (.inl _)) => true
  | _ => false

theorem readsN_client (hmac : PqxdhSecretInputKdf.HmacSha512) (control : beaconcrypt_core.pqxdh.ServerState)
    (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    ReadsN (clientStep (KemSK := KemSK) (V := V) hmac control binding input) 1 := by
  unfold clientStep
  split
  · exact readsN_mono (readsN_pure _) (Nat.zero_le _)
  · exact readsN_mono (readsN_pure _) (Nat.zero_le _)
  · exact readsN_mono (readsN_pure _) (Nat.zero_le _)
  · exact readsN_bind (a := 1) (b := 0) (readsN_map _ (readsN_table _)) fun _ =>
      readsN_bind (a := 0) (b := 0) (readsN_consume _) fun _ => readsN_pure _

theorem readsN_acceptTail (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity) (before : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    ReadsN (acceptTail (V := V) setup publicIdentity before collected) 1 := by
  unfold acceptTail
  dsimp only
  refine readsN_bind (a := 0) (b := 1) (readsN_set _) fun _ => ?_
  rcases collected with ⟨_ | input, consumed⟩
  · exact readsN_mono (readsN_pure _) (Nat.zero_le _)
  · refine readsN_bind (a := 1) (b := 0) (readsN_client _ _ _ _) fun returned => ?_
    split
    · exact readsN_bind (a := 0) (b := 0) (readsN_modify _) fun _ => readsN_pure _
    · exact readsN_pure _

theorem readsN_group (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (services : Services V Response) (pending : Pending Response) :
    ReadsN (groupStep (KemSK := KemSK) setup codec services pending) 1 := by
  unfold groupStep
  split
  · split
    · exact readsN_bind (a := 1) (b := 0) (readsN_value _) fun _ => readsN_game _
    · exact readsN_bind (a := 1) (b := 0) (readsN_table _) fun _ => readsN_game _
  · exact readsN_mono (readsN_pure _) (Nat.zero_le _)

theorem readsN_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (services : Services V Response) (session : Nat) (payload : Option Pqxdh.Bytes) :
    ReadsN (buildStep (KemSK := KemSK) setup codec checks services session payload) 0 := by
  intro state
  change (match state.1.pending session with
    | none => pure (none, state)
    | some token => _ : OracleComp (SkelSpec V) _).IsQueryBoundP _ 0
  split
  · trivial
  · exact isQueryBoundP_bind (n := 0) (m := 0) (liftComp_reads _) fun _ _ => trivial

theorem readsN_tail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) :
    ReadsN (tailStep (KemSK := KemSK) (V := V) setup codec query) 1 := by
  rcases query with query | (input | request | response)
  · exact readsN_mono (readsN_game _) (Nat.zero_le _)
  · exact readsN_bind (a := 1) (b := 0) (readsN_table _) fun _ => readsN_pure _
  · exact readsN_mono (readsN_game _) (Nat.zero_le _)
  · exact readsN_mono (readsN_game _) (Nat.zero_le _)

theorem readsN_tail_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain)
    (other : groupKind (KemSK := KemSK) (Response := Response) (.inl (.inl (.inr query))) = false) :
    ReadsN (tailStep (KemSK := KemSK) (V := V) setup codec query) 0 := by
  rcases query with query | (input | request | response)
  · exact readsN_game _
  · simp [groupKind] at other
  · exact readsN_game _
  · exact readsN_game _

/-- Every native step of the skeleton makes at most one table read, and only on a table request of the grouped interface. -/
theorem skelImpl_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (query : (GSpec KemSK Response).Domain) :
    ReadsC (skelImpl setup codec checks identityIndex publicIdentity services query)
      (if groupKind query = true then 1 else 0) := by
  rcases query with ((pool | tail) | shared) | pending
  · exact readsC_forward (.inl pool)
  · by_cases kind : groupKind (KemSK := KemSK) (Response := Response) (.inl (.inl (.inr tail))) = true
    · rw [ite_eq_left kind]
      exact readsC_liftT (readsN_tail setup codec tail)
    · rw [ite_eq_right kind]
      exact readsC_liftT (readsN_tail_free setup codec tail (by simpa using kind))
  · cases shared with
    | accept raw =>
        intro state
        simp only [groupKind, ite_true]
        change ((acceptStep (V := V) setup codec checks identityIndex publicIdentity raw).run state).IsQueryBoundP _ 1
        unfold acceptStep
        rw [StateT.run_bind]
        refine isQueryBoundP_bind (n := 0) (m := 1) trivial fun first _ => ?_
        rw [StateT.run_bind]
        refine isQueryBoundP_bind (n := 0) (m := 1) ?_ fun second _ =>
          readsC_liftT (readsN_acceptTail setup publicIdentity _ _) _
        change ((fun result => (result, first.2)) <$> simulateQ (encLift (V := V)) _).IsQueryBoundP _ 0
        rw [isQueryBoundP_map_iff]
        exact simulate_free (encLift (KemSK := KemSK) (V := V)) _
          (fun query => query_free _ _ (by simp [tableRead?])) _
    | build session payload => exact readsC_liftT (readsN_build setup codec checks services session payload)
    | hmac key message =>
        simp only [groupKind, ite_true]
        refine readsC_liftT ?_
        unfold hmacStep
        split
        · exact readsN_table _
        · exact readsN_mono (readsN_pure _) (Nat.zero_le _)
    | hash bytes => exact readsC_liftT (readsN_game _)
    | reveal keyId => exact readsC_liftT (readsN_game _)
  · simp only [groupKind, ite_true]
    exact readsC_liftT (readsN_group setup codec services pending)

/-- The Server's resumption interpreter makes at most one table read, on its private root request. -/
theorem resumeImpl_reads (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat) (services : Services V Response)
    (query : (PqxdhRegistrationJointKemOpaqueResume.Spec Reader KemSK).Domain) :
    ReadsC (resumeImpl hmac index services query) (if resumeRoot query = true then 1 else 0) := by
  rcases query with query | ((input | aux) | mutation)
  · exact readsC_forward query
  · simp only [resumeRoot, ite_true]
    refine readsC_liftT ?_
    simp only [resumeTail]
    split
    · exact readsN_bind (a := 1) (b := 0) (readsN_value _) fun _ =>
        readsN_bind (a := 0) (b := 0) (readsN_mark _ _) fun _ => readsN_pure _
    · exact readsN_bind (a := 1) (b := 0) (readsN_table _) fun _ => readsN_pure _
  · simp only [resumeRoot, Bool.false_eq_true, ite_false]
    refine readsC_liftT ?_
    cases aux with
    | eraseShared => exact readsN_pure _
    | eraseInput => exact readsN_pure _
    | consume rid => exact readsN_consume rid
  · simp only [resumeRoot, Bool.false_eq_true, ite_false]
    refine readsC_liftT ?_
    cases mutation with
    | install game => exact readsN_set game
    | publish slot token =>
        exact readsN_modify fun current => { current with pending := Function.update current.pending slot (some token) }

end Handlers

/-! ### Table requests of the grouped client and of the resumption -/

section Programs

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem groupKind_native (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) :
    groupKind (KemSK := KemSK) (Response := Response) (.inl query) = true ↔ NativeKind query := by
  rcases query with (pool | ((raw | (input | request | response)))) | shared
  · simp [groupKind, NativeKind]
  · simp [groupKind, NativeKind]
  · simp [groupKind, NativeKind]
  · simp [groupKind, NativeKind]
  · simp [groupKind, NativeKind]
  · cases shared <;> simp [groupKind, NativeKind]

/-- The grouped owner's request of its grouped finish. -/
def ownerGroup : (OwnerSpec Response).Domain → Bool
  | .inr _ => true
  | .inl _ => false

theorem groupedOwner_bound (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointBundle.Owner) :
    (groupedOwner (Response := Response) raw state).IsQueryBoundP (fun query => ownerGroup query = true) 1 := by
  unfold groupedOwner
  split
  · refine isQueryBoundP_bind (n := 0) (m := 1) (simulate_free _ _ (fun query => ?_) _) fun prepared _ => ?_
    · exact query_free _ _ (by simp [ownerGroup])
    cases prepared with
    | none => trivial
    | some prepared => exact isQueryBoundP_bind (n := 1) (m := 0) (query_one _ _) fun _ _ => trivial
  · trivial

/-- Every source request makes at most one table request of the grouped interface, and only if it is a table request of the source. -/
theorem groupedClient_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    ((groupedClient setup codec selected challenge query).run owners).IsQueryBoundP
      (fun query => groupKind (KemSK := KemSK) (Response := Response) query = true)
      (if TableKind query then 1 else 0) := by
  have lifted : ∀ {α : Type} (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α) (k : ℕ),
      (work.run owners).IsQueryBoundP (NativeKind (KemSK := KemSK) (Response := Response)) k →
      ((liftGrouped work).run owners).IsQueryBoundP
        (fun query => groupKind (KemSK := KemSK) (Response := Response) query = true) k := by
    intro _ work k bounded
    refine IsQueryBoundP.simulateQ_of_step bounded (fun query native => query_one _ _)
      (fun query native => query_free _ _ ?_)
    simpa [groupedLift, groupKind_native] using native
  rcases query with (coin | request) | read
  · exact lifted _ _ (client_bound setup codec _ owners)
  · cases request with
    | finish address raw =>
        simp only [groupedClient, groupedFinish, StateT.run, TableKind]
        split
        · trivial
        · rw [isQueryBoundP_map_iff]
          refine IsQueryBoundP.simulateQ_of_step (groupedOwner_bound raw _) (fun query owner => ?_)
            (fun query owner => ?_)
          · rcases query with query | query
            · simp [ownerGroup] at owner
            · exact query_one _ _
          · rcases query with query | query
            · exact simulate_free (groupedPoolLift (KemSK := KemSK) (Response := Response)) _
                (fun query => query_free _ _ (by simp [groupKind])) _
            · simp [ownerGroup] at owner
    | _ => exact lifted _ _ (client_bound setup codec _ owners)
  · exact lifted _ _ (client_bound setup codec _ owners)

/-- The private root request of the opaque client in the opaque tail's interface. -/
def tailRoot : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain → Bool
  | .inl (.inl _) => true
  | _ => false

/-- The Server's resumption makes at most one private root request. -/
theorem resume_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : PqxdhRegistrationJointKemOpaqueSuffix.Token)
    (state : GameState KemSK) (consumed : List Pqxdh.Bytes) :
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw verified ephemeral
      ciphertext token state consumed).IsQueryBoundP (fun query => resumeRoot query = true) 1 := by
  unfold PqxdhRegistrationJointKemOpaqueResume.resume
  refine isQueryBoundP_bind (n := 0) (m := 1) (simulate_free _ _ (fun query => ?_) _) fun collected _ => ?_
  · exact query_free _ _ (by simp [resumeRoot])
  have tailBound : (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId publicIdentity state collected).IsQueryBoundP
      (fun query => tailRoot (Reader := Reader) (KemSK := KemSK) query = true) 1 := by
    unfold PqxdhRegistrationJointKemOpaqueTail.tail
    dsimp only
    refine isQueryBoundP_bind (n := 0) (m := 1) (query_free _ _ (by simp [tailRoot])) fun _ _ => ?_
    split
    · trivial
    · refine isQueryBoundP_bind (n := 1) (m := 0) ?_ fun returned _ => ?_
      · refine IsQueryBoundP.simulateQ_of_step (PqxdhRegistrationJointKemOpaqueCosts.client_root _ _ _)
          (fun query root => query_one _ _) (fun query root => query_free _ _ ?_)
        rcases query with query | query
        · simp [PqxdhRegistrationJointKemOpaqueCosts.IsRoot] at root
        · simp [tailRoot]
      · split
        · exact isQueryBoundP_bind (n := 0) (m := 0) (query_free _ _ (by simp [tailRoot])) fun _ _ => trivial
        · trivial
  refine IsQueryBoundP.simulateQ_of_step tailBound (fun query root => query_one _ _) (fun query root => query_free _ _ ?_)
  rcases query with (query | query) | query
  · simp [tailRoot] at root
  · simp [resumeRoot]
  · simp [resumeRoot]

end Programs

/-! ### Table reads of the post-challenge client -/

section Client

open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R V : Type}

/-- The resumed client of the skeleton makes at most one table read for the Server's resumption and one per table request of the continuation. -/
theorem skelResume_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (game : GameState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat) (ciphertext : MlKem768Ciphertext)
    (services : Services V Response) (m : ℕ)
    (bounded : ∀ reply, (next reply).IsQueryBoundP (TableKind (KemSK := KemSK)) m) :
    (skelResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners next
      selected ciphertext services).IsQueryBoundP (fun query => tableRead? query = true) (1 + m) := by
  unfold skelResume
  refine isQueryBoundP_bind
    (IsQueryBoundP.simulateQ_run_StateT_of_step (resume_root setup codec checks identityIndex publicIdentity raw value
      ephemeral _ _ game consumed) (fun query state => resumeImpl_reads setup.hmac game.sessions services query state) _)
    fun answer _ => ?_
  have tagged : (PqxdhRegistrationJointAcceptKemCut.tagged observe raw next answer.1).IsQueryBoundP
      (TableKind (KemSK := KemSK)) m := by
    unfold PqxdhRegistrationJointAcceptKemCut.tagged
    rw [isQueryBoundP_map_iff]
    exact bounded answer.1
  refine IsQueryBoundP.simulateQ_run_StateT_of_step ?_ (fun query state =>
    skelImpl_reads setup codec checks identityIndex publicIdentity services query state) answer.2
  exact IsQueryBoundP.simulateQ_run_StateT_of_step tagged (fun query current =>
    groupedClient_bound setup codec selected ciphertext query current) owners

/-- The remaining table budget of the continuation of an active prechallenge context. -/
def ContinuationBound {count : Nat} (m : ℕ) : OpaqueContext Reader KemSK A X count → Prop
  | .ready _ _ (some (.pending _ _ _ _ _ _ next)) _ _ => ∀ reply, (next reply).IsQueryBoundP (TableKind (KemSK := KemSK)) m
  | _ => True

/-- The skeleton's post-challenge phase makes at most `1 + m` direct reads. -/
theorem postSkel_direct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (services : Services V Response)
    (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (context : OpaqueContext Reader KemSK A X count) (m : ℕ) (bounded : ContinuationBound m context) :
    (postSkel setup codec checks decision count selected services chosen challenge context).IsQueryBoundP
      (fun query => directRead? query = true) (1 + m) := by
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩),
    state, runtime⟩
  · trivial
  · trivial
  · trivial
  · simp only [postSkel]
    split
    · rw [isQueryBoundP_map_iff]
      refine IsQueryBoundP.of_imp (fun query direct => direct_table query direct) ?_
      refine fwd_reads _ _ _ ?_
      refine fwdOption_reads _ _ _ ?_ _
      refine fwd_reads _ _ _ ?_
      exact skelResume_reads setup codec checks _ _ _ raw value ephemeral consumed native.2 owners next selected.val
        challenge services m bounded
    · trivial

/-- The client of G1's shared world for the KEM-ideal branch makes at most `1 + m` direct reads. -/
theorem sharedClient_direct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (context : (MlKem768PublicKey × KemSK) × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext) (m : ℕ)
    (bounded : ContinuationBound m context.2.1) :
    (sharedClient setup codec checks decision count selected context).IsQueryBoundP
      PqxdhExtractRomHiddenSuffix.IsDirect (1 + m) := by
  refine IsQueryBoundP.simulateQ_of_step (postSkel_direct setup codec checks decision count selected _ context.1
    context.2.2 context.2.1 m bounded) (fun query direct => ?_) (fun query direct => ?_)
  · rcases query with coin | (point | point)
    · simp [directRead?] at direct
    · simp [directRead?] at direct
    · exact query_one _ _
  · rcases query with coin | (point | point)
    · exact query_free _ _ (by simp [PqxdhExtractRomHiddenSuffix.IsDirect])
    · simp only [compileHidden, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, isQueryBoundP_map_iff]
      exact query_free _ _ (by simp [PqxdhExtractRomHiddenSuffix.IsDirect])
    · simp [directRead?] at direct

end Client

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.direct_table' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.direct_table

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.liftComp_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.liftComp_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.fwd_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.fwd_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.fwdOption_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.fwdOption_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_game

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_table

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_set

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_modify

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_mark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_mark

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_consume

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsC_liftT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsC_liftT

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsC_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsC_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_client

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_acceptTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_acceptTail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_group

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_build

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_tail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_tail_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.readsN_tail_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.skelImpl_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.skelImpl_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.resumeImpl_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.resumeImpl_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.groupKind_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.groupKind_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.groupedOwner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.groupedOwner_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.groupedClient_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.groupedClient_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.resume_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.resume_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.skelResume_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.skelResume_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.postSkel_direct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.postSkel_direct

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.sharedClient_direct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.sharedClient_direct
