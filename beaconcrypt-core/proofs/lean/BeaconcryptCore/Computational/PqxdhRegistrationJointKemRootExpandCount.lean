import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpandLocal
import BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds

/-!
# The root count of the root client (item 2, stage S2, root count)

This module bounds the root requests of the root client of stage S2 (`PqxdhRegistrationJointKemRootExpand.rootClient`) by `1 + qFinish`, where `qFinish` is the source budget of Beacon finish requests (kind 5). The count includes repeated requests at the same coordinates, as `PqxdhCorrelatedExpandHybrid.IsRoot` does.

- The root client makes one root request per hidden read of the skeleton client and none otherwise: its coins and its public table make none (`publicLocal`).
- Every native step of the skeleton makes at most one hidden read, and only on a grouped Beacon finish (`skelImpl_hidden`); the Server's resumption interpreter makes at most one, on its private root request (`resumeImpl_hidden`). A raw accept, a public HMAC and a Beacon tail root callback read the public table only.
- Every source request makes at most one grouped Beacon finish, and only if it is a Beacon finish request (`groupedClient_group`).
- The actual encapsulator, the router and the CCA evaluation forward hidden reads one for one and add none (`fwd_hidden`, `fwdOption_hidden`).
- The continuation suspended at the cut inherits every query bound of the source program (`scan_inherit` to `sharedStart_inherit`), so its Beacon finish requests stay within `qFinish` (`certified_finish`).

The bound needs no assumption beyond the source budget `certified` of theorem T5. Stage T (plan section 17) tightens `1 + qFinish` to `2`.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)
open PqxdhRegistrationJointKemPostSkeleton
open PqxdhRegistrationJointKemRomSplit (query_free query_one simulate_free isQueryBoundP_option_of_step
  compose compose_run support_option resumeRoot resume_root)

/-! ### Beacon finish requests of the source -/

section Finish

open PqxdhRegistrationJointRevealSchedule (Spec)

variable {KemSK : Type}

/-- The source's Beacon finish requests. -/
def FinishKind : (Spec KemSK).Domain → Prop
  | .inl (.inr (.finish _ _)) => True
  | _ => False

instance : DecidablePred (FinishKind (KemSK := KemSK))
  | .inl (.inl _) => inferInstanceAs (Decidable False)
  | .inl (.inr (.create _ _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.bundle _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.accept _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.build _ _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.finish _ _)) => inferInstanceAs (Decidable True)
  | .inl (.inr (.hmac _ _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.hash _)) => inferInstanceAs (Decidable False)
  | .inl (.inr (.reveal _)) => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable False)

theorem finish_source (query : (Spec KemSK).Domain) (finish : FinishKind query) :
    PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 5 := by
  rcases query with (coin | request) | read
  · exact finish.elim
  · cases request <;> first
      | exact finish.elim
      | simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind]
  · exact finish.elim

/-- The source budget of kind 5 bounds the Beacon finish requests of the source program. -/
theorem certified_finish {X : Type} (work : OracleComp (Spec KemSK) X)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    work.IsQueryBoundP (FinishKind (KemSK := KemSK)) (budget (.inl 5)) :=
  IsQueryBoundP.of_imp finish_source (certified (.inl 5))

end Finish

/-! ### The continuation at the cut inherits the source's query bounds -/

section Scan

open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (Cut scan)

variable {KemSK Result σ ι' : Type} {spec' : OracleSpec ι'}

/-- One forwarded request of the scan: the continuation of the rest inherits the bound. -/
theorem inherit_forward (P : (Spec KemSK).Domain → Prop) [DecidablePred P]
    (handler : QueryImpl (Spec KemSK) (StateT σ (OracleComp spec')))
    (query : (Spec KemSK).Domain) (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result) (n : ℕ)
    (bounded : (liftM ((Spec KemSK).query query) >>= next : OracleComp (Spec KemSK) Result).IsQueryBoundP P n)
    (index : Nat) (state : σ)
    (ih : ∀ reply (n : ℕ), (next reply).IsQueryBoundP P n → ∀ state,
      ∀ result ∈ support ((simulateQ handler (scan (next reply) index)).run state), ∀ raw rest,
        result.1 = .pending raw rest → ∀ reply, (rest reply).IsQueryBoundP P n) :
    ∀ result ∈ support ((simulateQ handler (liftM ((Spec KemSK).query query) >>= fun reply =>
        scan (next reply) index)).run state), ∀ raw rest,
      result.1 = .pending raw rest → ∀ reply, (rest reply).IsQueryBoundP P n := by
  intro result reached raw rest pending reply
  rw [isQueryBoundP_query_bind_iff] at bounded
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨middle, _, later⟩ := reached
  refine (ih middle.1 _ (bounded.2 middle.1) middle.2 result later raw rest pending reply).mono ?_
  split <;> omega

/-- The continuation suspended by the scan at the selected raw accept inherits every query bound of the program. -/
theorem scan_inherit (P : (Spec KemSK).Domain → Prop) [DecidablePred P]
    (handler : QueryImpl (Spec KemSK) (StateT σ (OracleComp spec')))
    (work : OracleComp (Spec KemSK) Result) (n : ℕ) (bounded : work.IsQueryBoundP P n) (index : Nat) (state : σ) :
    ∀ result ∈ support ((simulateQ handler (scan work index)).run state), ∀ raw next,
      result.1 = .pending raw next → ∀ reply, (next reply).IsQueryBoundP P n := by
  induction work using OracleComp.inductionOn generalizing index n state with
  | pure value =>
      intro result reached raw next pending
      change result ∈ support ((simulateQ handler (pure (Cut.complete value) : OracleComp (Spec KemSK) _)).run state)
        at reached
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      cases pending
  | query_bind query next ih =>
      rcases query with (coin | request) | read
      · exact inherit_forward P handler _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)
      · cases request with
        | accept raw =>
            cases index with
            | zero =>
                intro result reached raw' rest pending reply
                change result ∈ support ((simulateQ handler (pure (Cut.pending raw next) :
                  OracleComp (Spec KemSK) _)).run state) at reached
                simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
                subst reached
                cases pending
                rw [isQueryBoundP_query_bind_iff] at bounded
                refine (bounded.2 reply).mono ?_
                split <;> omega
            | succ index =>
                exact inherit_forward P handler _ next n bounded index state
                  (fun reply n bounded state => ih reply n bounded index state)
        | _ =>
            exact inherit_forward P handler _ next n bounded index state
              (fun reply n bounded state => ih reply n bounded index state)
      · exact inherit_forward P handler _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)

end Scan

section Start

open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRawOpaque (OpaqueCut OpaqueContext opaqueScan sourcePreOpaque)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The continuation at a reached cut of the source program, interpreted by the source client and native backend, inherits every query bound of the program. -/
theorem commands_inherit (P : (SourceSpec KemSK).Domain → Prop) [DecidablePred P]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (SourceSpec KemSK) X) (n : ℕ)
    (bounded : work.IsQueryBoundP P n) (index : Nat)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ reached ∈ support (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks identityIndex publicIdentity
        (PqxdhRegistrationJointAcceptCut.scan work index) owners state), ∀ raw next,
      reached.1.1 = .pending raw next → ∀ reply, (next reply).IsQueryBoundP P n := by
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
  exact scan_inherit P _ work n bounded index (owners, state) (reached.1.1, (reached.1.2, reached.2)) lifted raw next
    pending

/-- The continuation of an active opaque cut keeps a bound. -/
def InheritsCut (P : (SourceSpec KemSK).Domain → Prop) [DecidablePred P] (n : ℕ) :
    OpaqueCut Reader KemSK X R → Prop
  | .complete _ => True
  | .pending _ _ _ _ _ _ next => ∀ reply, (next reply).IsQueryBoundP P n

/-- Every cut reached by the explicit opaque scan inherits every query bound of the program. -/
theorem opaqueScan_inherit (P : (SourceSpec KemSK).Domain → Prop) [DecidablePred P]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (n : ℕ) (bounded : work.IsQueryBoundP P n)
    (index : Nat) (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ cut ∈ support (opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity observe work index
      owners state), InheritsCut P n cut := by
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
        exact commands_inherit P setup codec checks identityIndex publicIdentity work n bounded index owners state
          found commandsReached raw next scanCut

/-- The continuation of an active prechallenge context keeps a bound. -/
def Inherits (P : (SourceSpec KemSK).Domain → Prop) [DecidablePred P] {count : Nat} (n : ℕ) :
    OpaqueContext Reader KemSK A X count → Prop
  | .ready _ _ (some cut) _ _ => InheritsCut P n cut
  | _ => True

/-- Every prechallenge context of the KEM-ideal branch inherits every query bound of the source program. -/
theorem sourcePreOpaque_inherit (P : (SourceSpec KemSK).Domain → Prop) [DecidablePred P]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) (n : ℕ)
    (bounded : work.IsQueryBoundP P n) :
    ∀ context ∈ support (sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index chosen), Inherits P n context := by
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
    · simp only [Inherits]
    · simp only [Inherits]
      have scanReached := support_option _ _ _ cut result.2 (by rw [← cutCase]; exact resultReached)
      exact opaqueScan_inherit P setup codec checks _ _ _ work n bounded index [] _ cut scanReached

/-- Every outcome of G1's prefix for the KEM-ideal branch has a context whose continuation inherits every query bound of the source program. -/
theorem sharedStart_inherit (P : (SourceSpec KemSK).Domain → Prop) [DecidablePred P]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (n : ℕ) (bounded : work.IsQueryBoundP P n) :
    ∀ start ∈ support (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index), Inherits P n start.2.2.1 := by
  intro start reached
  simp only [sharedStart, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨chosen, _, context, contextReached, encapsulated, _, rfl⟩ := reached
  exact sourcePreOpaque_inherit P setup codec checks ensureInit supplied decision work runtime count selected index
    chosen n bounded context contextReached

end Start

/-! ### Hidden reads -/

section Hidden

variable {κ V : Type} {A : OracleSpec κ}

/-- A hidden read: a request of the left summand of the right summand. -/
def valueRead? {κ₁ κ₂ κ₃ : Type} : κ₁ ⊕ (κ₂ ⊕ κ₃) → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A lifted base program makes no hidden read. -/
theorem liftComp_hidden {α : Type} (work : OracleComp A α) :
    (OracleComp.liftComp work (A + TSpec V)).IsQueryBoundP (fun query => valueRead? query = true) 0 := by
  exact IsQueryBoundP.liftComp_subSpec (p := fun _ => False) (fun query => by simp [valueRead?])
    (PqxdhRegistrationJointBeaconOpaqueFinishRouter.free_false work)

/-- Forwarding through a stateless interpreter keeps every hidden read and adds none. -/
theorem fwd_hidden {κ' α : Type} {B : OracleSpec κ'} (layer : QueryImpl A (OracleComp B))
    (work : OracleComp (A + TSpec V) α) (n : ℕ)
    (bounded : work.IsQueryBoundP (fun query => valueRead? query = true) n) :
    (simulateQ (fwd (T := TSpec V) layer) work).IsQueryBoundP (fun query => valueRead? query = true) n := by
  refine IsQueryBoundP.simulateQ_of_step bounded (fun query read => ?_) (fun query read => ?_)
  · rcases query with query | (point | point)
    · simp [valueRead?] at read
    · exact query_one _ _
    · simp [valueRead?] at read
  · rcases query with query | (point | point)
    · exact liftComp_hidden _
    · simp [valueRead?] at read
    · exact query_free _ _ (by simp [valueRead?])

/-- Forwarding through an optional stateful interpreter keeps every hidden read and adds none. -/
theorem fwdOption_hidden {κ' J α : Type} {B : OracleSpec κ'} (layer : QueryImpl A (OptionT (StateT J (OracleComp B))))
    (work : OracleComp (A + TSpec V) α) (n : ℕ)
    (bounded : work.IsQueryBoundP (fun query => valueRead? query = true) n) (state : J) :
    (((simulateQ (fwdOption (T := TSpec V) layer) work).run).run state).IsQueryBoundP
      (fun query => valueRead? query = true) n := by
  refine isQueryBoundP_option_of_step _ work n bounded (fun query current => ?_) state
  rcases query with query | (point | point)
  · simp only [valueRead?, Bool.false_eq_true, ite_false]
    exact liftComp_hidden _
  · simp only [valueRead?, ite_true]
    rw [fwdOption_inr, isQueryBoundP_map_iff]
    exact query_one _ _
  · simp only [valueRead?, Bool.false_eq_true, ite_false]
    rw [fwdOption_inr, isQueryBoundP_map_iff]
    exact query_free _ _ (by simp)

end Hidden

/-! ### Hidden reads of the skeleton's native layer -/

section Native

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- A native-layer program of the skeleton makes at most `k` hidden reads. -/
def HiddenN {α : Type} (work : NGame KemSK V α) (k : ℕ) : Prop :=
  ∀ state, (work.run state).IsQueryBoundP (fun query => valueRead? query = true) k

/-- A native-layer handler step of the skeleton makes at most `k` hidden reads. -/
def HiddenC {α : Type} (work : SClient KemSK V α) (k : ℕ) : Prop :=
  ∀ state, (work.run state).IsQueryBoundP (fun query => valueRead? query = true) k

theorem hiddenN_pure {α : Type} (value : α) : HiddenN (pure value : NGame KemSK V α) 0 :=
  fun _ => trivial

theorem hiddenN_bind {α β : Type} {work : NGame KemSK V α} {next : α → NGame KemSK V β} {a b : ℕ}
    (first : HiddenN work a) (rest : ∀ value, HiddenN (next value) b) : HiddenN (work >>= next) (a + b) := by
  intro state
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (first state) fun result _ => rest result.1 result.2

theorem hiddenN_mono {α : Type} {work : NGame KemSK V α} {a b : ℕ} (reads : HiddenN work a) (le : a ≤ b) :
    HiddenN work b :=
  fun state => (reads state).mono le

theorem hiddenN_map {α β : Type} (f : α → β) {work : NGame KemSK V α} {k : ℕ} (reads : HiddenN work k) :
    HiddenN (f <$> work) k := by
  intro state
  rw [StateT.run_map, isQueryBoundP_map_iff]
  exact reads state

theorem hiddenN_game {α : Type} (work : StateT (GameState KemSK) ProbComp α) :
    HiddenN (gameStep (V := V) work) 0 := by
  intro state
  rw [PqxdhRegistrationJointKemPostSkeleton.gameStep_run, isQueryBoundP_map_iff]
  exact liftComp_hidden _

theorem hiddenN_table (point : Pqxdh.Bytes) : HiddenN (tableRead (KemSK := KemSK) (V := V) point) 0 := by
  intro state
  rw [PqxdhRegistrationJointKemPostSkeleton.tableRead_eq, isQueryBoundP_map_iff]
  exact query_free _ _ (by simp [valueRead?])

theorem hiddenN_value (point : PqxdhCorrelatedExtractFamily.Message) :
    HiddenN (valueRead (KemSK := KemSK) (V := V) point) 1 := by
  intro state
  rw [PqxdhRegistrationJointKemPostSkeleton.valueRead_eq, isQueryBoundP_map_iff]
  exact query_one _ _

theorem hiddenC_liftT {α : Type} {work : NGame KemSK V α} {k : ℕ} (reads : HiddenN work k) :
    HiddenC (liftT work) k :=
  fun state => fwd_hidden _ _ k (reads state)

theorem hiddenC_forward (query : (Enc KemSK).Domain) :
    HiddenC (fun state => (fun reply => (reply, state)) <$> encLift (V := V) query :
      SClient KemSK V (Enc KemSK |>.Range query)) 0 := by
  intro state
  change ((fun reply => (reply, state)) <$> encLift (V := V) query).IsQueryBoundP _ 0
  rw [isQueryBoundP_map_iff]
  exact query_free _ _ (by simp [valueRead?])

theorem hiddenN_client (hmac : PqxdhSecretInputKdf.HmacSha512) (control : beaconcrypt_core.pqxdh.ServerState)
    (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    HiddenN (clientStep (KemSK := KemSK) (V := V) hmac control binding input) 0 := by
  unfold clientStep
  split
  · exact hiddenN_pure _
  · exact hiddenN_pure _
  · exact hiddenN_pure _
  · exact hiddenN_bind (a := 0) (b := 0) (hiddenN_map _ (hiddenN_table _)) fun _ =>
      hiddenN_bind (a := 0) (b := 0) (fun _ => trivial) fun _ => hiddenN_pure _

theorem hiddenN_acceptTail (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity) (before : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    HiddenN (acceptTail (V := V) setup publicIdentity before collected) 0 := by
  unfold acceptTail
  dsimp only
  refine hiddenN_bind (a := 0) (b := 0) (fun _ => trivial) fun _ => ?_
  rcases collected with ⟨_ | input, consumed⟩
  · exact hiddenN_pure _
  · refine hiddenN_bind (a := 0) (b := 0) (hiddenN_client _ _ _ _) fun returned => ?_
    split
    · exact hiddenN_bind (a := 0) (b := 0) (fun _ => trivial) fun _ => hiddenN_pure _
    · exact hiddenN_pure _

theorem hiddenN_group (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (services : Services V Response) (pending : Pending Response) :
    HiddenN (groupStep (KemSK := KemSK) setup codec services pending) 1 := by
  unfold groupStep
  split
  · split
    · exact hiddenN_bind (a := 1) (b := 0) (hiddenN_value _) fun _ => hiddenN_game _
    · exact hiddenN_mono (hiddenN_bind (a := 0) (b := 0) (hiddenN_table _) fun _ => hiddenN_game _) (Nat.zero_le _)
  · exact hiddenN_mono (hiddenN_pure _) (Nat.zero_le _)

theorem hiddenN_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (services : Services V Response) (session : Nat) (payload : Option Pqxdh.Bytes) :
    HiddenN (buildStep (KemSK := KemSK) setup codec checks services session payload) 0 := by
  intro state
  change (match state.1.pending session with
    | none => pure (none, state)
    | some token => _ : OracleComp (SkelSpec V) _).IsQueryBoundP _ 0
  split
  · trivial
  · exact isQueryBoundP_bind (n := 0) (m := 0) (liftComp_hidden _) fun _ _ => trivial

theorem hiddenN_tail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) :
    HiddenN (tailStep (KemSK := KemSK) (V := V) setup codec query) 0 := by
  rcases query with query | (input | request | response)
  · exact hiddenN_game _
  · exact hiddenN_bind (a := 0) (b := 0) (hiddenN_table _) fun _ => hiddenN_pure _
  · exact hiddenN_game _
  · exact hiddenN_game _

theorem hiddenN_hmac (setup : Setup baseSpec KemSK) (key : HmacBlock) (message : Pqxdh.Bytes) :
    HiddenN (hmacStep (KemSK := KemSK) (V := V) setup key message) 0 := by
  unfold hmacStep
  split
  · exact hiddenN_table _
  · exact hiddenN_pure _

/-- The grouped Beacon finish request. -/
def groupRequest? {κ₁ κ₂ : Type} : κ₁ ⊕ κ₂ → Bool
  | .inr _ => true
  | .inl _ => false

/-- Every native step of the skeleton makes at most one hidden read, and only on a grouped Beacon finish. -/
theorem skelImpl_hidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (query : (GSpec KemSK Response).Domain) :
    HiddenC (skelImpl setup codec checks identityIndex publicIdentity services query)
      (if groupRequest? query = true then 1 else 0) := by
  rcases query with ((pool | tail) | shared) | pending
  · exact hiddenC_forward (.inl pool)
  · exact hiddenC_liftT (hiddenN_tail setup codec tail)
  · simp only [groupRequest?, Bool.false_eq_true, ite_false]
    cases shared with
    | accept raw =>
        intro state
        change ((acceptStep (V := V) setup codec checks identityIndex publicIdentity raw).run state).IsQueryBoundP _ 0
        unfold acceptStep
        rw [StateT.run_bind]
        refine isQueryBoundP_bind (n := 0) (m := 0) trivial fun first _ => ?_
        rw [StateT.run_bind]
        refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun second _ =>
          hiddenC_liftT (hiddenN_acceptTail setup publicIdentity _ _) _
        change ((fun result => (result, first.2)) <$> simulateQ (encLift (V := V)) _).IsQueryBoundP _ 0
        rw [isQueryBoundP_map_iff]
        exact simulate_free (encLift (KemSK := KemSK) (V := V)) _
          (fun query => query_free _ _ (by simp [valueRead?])) _
    | build session payload => exact hiddenC_liftT (hiddenN_build setup codec checks services session payload)
    | hmac key message => exact hiddenC_liftT (hiddenN_hmac setup key message)
    | hash bytes => exact hiddenC_liftT (hiddenN_game _)
    | reveal keyId => exact hiddenC_liftT (hiddenN_game _)
  · simp only [groupRequest?, ite_true]
    exact hiddenC_liftT (hiddenN_group setup codec services pending)

/-- The Server's resumption interpreter makes at most one hidden read, on its private root request. -/
theorem resumeImpl_hidden (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat) (services : Services V Response)
    (query : (PqxdhRegistrationJointKemOpaqueResume.Spec Reader KemSK).Domain) :
    HiddenC (resumeImpl hmac index services query) (if resumeRoot query = true then 1 else 0) := by
  rcases query with query | ((input | aux) | mutation)
  · exact hiddenC_forward query
  · simp only [resumeRoot, ite_true]
    refine hiddenC_liftT ?_
    simp only [resumeTail]
    split
    · exact hiddenN_bind (a := 1) (b := 0) (hiddenN_value _) fun _ =>
        hiddenN_bind (a := 0) (b := 0) (fun _ => trivial) fun _ => hiddenN_pure _
    · exact hiddenN_mono (hiddenN_bind (a := 0) (b := 0) (hiddenN_table _) fun _ => hiddenN_pure _) (Nat.zero_le _)
  · simp only [resumeRoot, Bool.false_eq_true, ite_false]
    refine hiddenC_liftT ?_
    cases aux with
    | eraseShared => exact hiddenN_pure _
    | eraseInput => exact hiddenN_pure _
    | consume rid => exact fun _ => trivial
  · simp only [resumeRoot, Bool.false_eq_true, ite_false]
    refine hiddenC_liftT ?_
    cases mutation with
    | install game => exact fun _ => trivial
    | publish slot token => exact fun _ => trivial

end Native

/-! ### Grouped Beacon finishes of the grouped client -/

section Programs

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every source request makes at most one grouped Beacon finish, and only if it is a Beacon finish request. -/
theorem groupedClient_group (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    ((groupedClient setup codec selected challenge query).run owners).IsQueryBoundP
      (fun query => groupRequest? (κ₁ := (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) query = true)
      (if FinishKind query then 1 else 0) := by
  have lifted : ∀ {α : Type} (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α),
      ((liftGrouped work).run owners).IsQueryBoundP
        (fun query => groupRequest? (κ₁ := (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) query =
          true) 0 := by
    intro _ work
    exact simulate_free groupedLift _ (fun query => query_free _ _ (by simp [groupRequest?])) _
  rcases query with (coin | request) | read
  · exact (lifted _).mono (Nat.zero_le _)
  · cases request with
    | finish address raw =>
        simp only [groupedClient, groupedFinish, StateT.run, FinishKind]
        split
        · trivial
        · rw [isQueryBoundP_map_iff]
          refine IsQueryBoundP.simulateQ_of_step
            (PqxdhRegistrationJointKemRomSplit.groupedOwner_bound raw _) (fun query owner => ?_)
            (fun query owner => ?_)
          · rcases query with query | query
            · simp [PqxdhRegistrationJointKemRomSplit.ownerGroup] at owner
            · exact query_one _ _
          · rcases query with query | query
            · exact simulate_free (groupedPoolLift (KemSK := KemSK) (Response := Response)) _
                (fun query => query_free _ _ (by simp [groupRequest?])) _
            · simp [PqxdhRegistrationJointKemRomSplit.ownerGroup] at owner
    | _ => exact (lifted _).mono (Nat.zero_le _)
  · exact (lifted _).mono (Nat.zero_le _)

end Programs

/-! ### Hidden reads of the post-challenge client and root requests of the root client -/

section Client

open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext)
open PqxdhCorrelatedExpand (RootSpec rootCoins)
open PqxdhCorrelatedExpandHybrid (IsRoot)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R V : Type}

/-- The resumed client of the skeleton makes at most one hidden read for the Server's resumption and one per Beacon finish request of the continuation. -/
theorem skelResume_hidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (game : GameState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat) (ciphertext : MlKem768Ciphertext)
    (services : Services V Response) (m : ℕ)
    (bounded : ∀ reply, (next reply).IsQueryBoundP (FinishKind (KemSK := KemSK)) m) :
    (skelResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners next
      selected ciphertext services).IsQueryBoundP (fun query => valueRead? query = true) (1 + m) := by
  unfold skelResume
  refine isQueryBoundP_bind
    (IsQueryBoundP.simulateQ_run_StateT_of_step (resume_root setup codec checks identityIndex publicIdentity raw value
      ephemeral _ _ game consumed) (fun query state => resumeImpl_hidden setup.hmac game.sessions services query state) _)
    fun answer _ => ?_
  have tagged : (PqxdhRegistrationJointAcceptKemCut.tagged observe raw next answer.1).IsQueryBoundP
      (FinishKind (KemSK := KemSK)) m := by
    unfold PqxdhRegistrationJointAcceptKemCut.tagged
    rw [isQueryBoundP_map_iff]
    exact bounded answer.1
  refine IsQueryBoundP.simulateQ_run_StateT_of_step ?_ (fun query state =>
    skelImpl_hidden setup codec checks identityIndex publicIdentity services query state) answer.2
  exact IsQueryBoundP.simulateQ_run_StateT_of_step tagged (fun query current =>
    groupedClient_group setup codec selected ciphertext query current) owners

/-- The skeleton's post-challenge phase makes at most `1 + m` hidden reads when the continuation at the cut makes at most `m` Beacon finish requests. -/
theorem postSkel_hidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (services : Services V Response)
    (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (context : OpaqueContext Reader KemSK A X count) (m : ℕ)
    (bounded : Inherits (FinishKind (KemSK := KemSK)) m context) :
    (postSkel setup codec checks decision count selected services chosen challenge context).IsQueryBoundP
      (fun query => valueRead? query = true) (1 + m) := by
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩),
    state, runtime⟩
  · trivial
  · trivial
  · trivial
  · simp only [postSkel]
    split
    · rw [isQueryBoundP_map_iff]
      refine fwd_hidden _ _ _ ?_
      refine fwdOption_hidden _ _ _ ?_ _
      refine fwd_hidden _ _ _ ?_
      exact skelResume_hidden setup codec checks _ _ _ raw value ephemeral consumed native.2 owners next selected.val
        challenge services m bounded
    · trivial

/-- The root client's interpretation makes one root request per hidden read and none otherwise. -/
theorem publicLocal_root (query : (SkelSpec RootOutput).Domain) (cache : HmacOracle.QueryCache) :
    ((publicLocal query).run cache).IsQueryBoundP IsRoot (if valueRead? query = true then 1 else 0) := by
  rcases query with coin | (message | point)
  · change ((fun reply => (reply, cache)) <$> (liftM (RootSpec.query (.inl coin)) : OracleComp RootSpec _)).IsQueryBoundP
      IsRoot _
    rw [isQueryBoundP_map_iff]
    exact query_free _ _ (by simp [IsRoot])
  · change ((fun reply => (reply, cache)) <$> (liftM (RootSpec.query (.inr message)) : OracleComp RootSpec _)).IsQueryBoundP
      IsRoot _
    rw [isQueryBoundP_map_iff]
    exact query_one _ _
  · exact PqxdhCorrelatedExpandQueryBounds.rootCoins_roots ((HmacOracle.randomOracle point).run cache)

/-- Stage S2, the root count: the root client makes at most `1 + qFinish` root requests, repeated requests included, where `qFinish` is the source budget of Beacon finish requests. -/
theorem rootClient_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP IsRoot (1 + budget (.inl 5)) := by
  have inherits := sharedStart_inherit (Reader := Reader) FinishKind setup codec checks ensureInit supplied decision work
    runtime count selected index (budget (.inl 5)) (certified_finish work budget certified)
  unfold rootClient internalize
  rw [← Nat.zero_add (1 + budget (.inl 5))]
  refine isQueryBoundP_bind (PqxdhCorrelatedExpandQueryBounds.rootCoins_roots _) fun start reached => ?_
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step ?_ (fun query cache => publicLocal_root query cache) start.1
  refine postSkel_hidden setup codec checks decision count selected _ start.2.1 start.2.2.2 start.2.2.1 _ ?_
  exact inherits start (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached)

end Client

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.certified_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.certified_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.inherit_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.inherit_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.scan_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.scan_inherit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.commands_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.commands_inherit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.opaqueScan_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.opaqueScan_inherit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.sourcePreOpaque_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.sourcePreOpaque_inherit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.sharedStart_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.sharedStart_inherit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.liftComp_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.liftComp_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.fwd_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.fwd_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.fwdOption_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.fwdOption_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_game

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_table

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenC_liftT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenC_liftT

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenC_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenC_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_client

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_acceptTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_acceptTail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_group

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_build

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_tail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.hiddenN_hmac

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.skelImpl_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.skelImpl_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.resumeImpl_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.resumeImpl_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.groupedClient_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.groupedClient_group

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.skelResume_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.skelResume_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.postSkel_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.postSkel_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.publicLocal_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.publicLocal_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.rootClient_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.rootClient_root
