-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSecrecy

/-! The post-run "later quantum" reveal mode LQ of the common deployment experiment (stage LQ-1). The game `laterGame` constructs the Server from a generated seed (never a supplied one), runs a first adversary `A₁` against the CE handler with one ghost change, computes the reveal from the final state, and then runs a second adversary `A₂` on the run's output and the reveal, with post-run coins, the public HMAC and the BLAKE2b oracle as its only queries. The game is defined for either observation mode; as in the classical game, secrecy claims are to be stated in mode P. The ghost change (`snapImpl`): a `finish` command first records the addressed owner's current prekey and one-time scalar fields in the snapshot `Snap`, then runs the unchanged native finish; a capture keeps an earlier captured value where the current field is absent, so a later finish on a terminal owner erases nothing from the snapshot (`capture_absent`). Forgetting the snapshot gives back the CE handler exactly (`snap_erase_run`, `snap_erase`), and an event that ignores the caches has the same distribution at the end of the later-quantum game as at the end of the classical game (`later_event`, `later_classical_event`), so the run-phase terms carry over unchanged. The reveal (`revealOf`) holds, for every created Beacon in creation order, its Ed25519 identity seed (still live after finish) and its X25519 prekey and one-time scalars: the current field if the phase still holds it, otherwise the value captured before finish or abort erased it. The Beacon's X25519 identity secret is the public production conversion of the seed. One-time scalars of failed bundle attempts are in no state and are not revealed. DH outputs are not listed: every Beacon-side DH output is a public function of revealed scalars and public points, and so is the Server-side output of a session with an honest Beacon whose response was published. Deviation D6: no Server secret is revealed, neither the Server's identity seed (nor its X25519 conversion) nor any Server ephemeral scalar, so Server-side DH outputs against points whose discrete logarithm the adversary does not know, and DH values of sessions whose ephemeral key was never published, stay unrevealed. Never revealed: ML-KEM secret keys and shared secrets, the Extract family and R1 cache, ghost touches, roots, chains, kernels, skipped keys and plaintexts; the reveal's type holds only identity seeds and scalars. The post phase (`postImpl`) answers coins with fresh uniform draws and HMAC and BLAKE2b with the same native handler commands as during the run, on the final caches; it has no protocol, `test` or `fresh` command, and it changes only the Extract family, the BLAKE2b cache and the ghost touch list (`post_frame`, `later_frame`). The post-run queries are classical: this is a classical adversary with a post-run disclosure, not a quantum or QROM adversary. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLater
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhRegistrationJointLiveRead (Field Value value)
open PqxdhDeploymentInterface (Spec Command ModeSpec Mode FreshBounds asModeO)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl wrap)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- The prekey and one-time scalars captured for one owner. -/
structure Captured where
  prekey : Option ScalarBytes
  oneTime : Option ScalarBytes

/-- The ghost snapshot of captured scalars, by owner handle. -/
abbrev Snap := Nat → Captured

/-- The empty snapshot. -/
def Snap.empty : Snap := fun _ => ⟨none, none⟩

/-- The scalar of a prekey or one-time field value; every other field value gives nothing. -/
def scalarOf : Option (Value KemSK) → Option ScalarBytes
  | some (.prekey scalar) => some scalar
  | some (.oneTime scalar) => some scalar
  | _ => none

/-- The current value of one field of the owner at a handle, exactly as the source14 field read answers it. -/
def fieldOf (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : Nat) (field : Field) :
    Option (Value KemSK) :=
  (owners[index]?).bind (value field)

/-- Capture the prekey and one-time field values of one owner; a captured value is kept where the current field is absent. -/
def capture (snap : Snap) (index : Nat) (prekey oneTime : Option (Value KemSK)) : Snap :=
  Function.update snap index ⟨(scalarOf prekey).or (snap index).prekey, (scalarOf oneTime).or (snap index).oneTime⟩

/-- The owner addressed by a `finish` command; no other command captures. -/
def finishOwner : Spec.Domain → Option Nat
  | .inr (.finish owner _) => some owner
  | _ => none

/-- The snapshot after a command: a `finish` captures the addressed owner's current fields, every other command keeps the snapshot. -/
def snapshotAt (snap : Snap) (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) : Option Nat → Snap
  | none => snap
  | some index => capture snap index (fieldOf owners index .prekey) (fieldOf owners index .oneTime)

/-- The revealed secrets of one honest Beacon: its Ed25519 identity seed and its X25519 prekey and one-time scalars. -/
structure Revealed where
  identity : IdentitySeed
  prekey : Option ScalarBytes
  oneTime : Option ScalarBytes

/-- The reveal: one entry per created Beacon, in creation order. -/
abbrev Reveal := List Revealed

/-- The revealed secrets of one owner: the identity seed and, for each scalar, the current field or else the captured value. -/
def revealed (snap : Snap) (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) : Revealed :=
  ⟨owner.beacon.identity, (scalarOf (value .prekey owner)).or (snap index).prekey,
    (scalarOf (value .oneTime owner)).or (snap index).oneTime⟩

/-- The reveal of the owner at a handle, if one was created. -/
def revealAt (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (snap : Snap) (index : Nat) : Option Revealed :=
  (owners[index]?).map (revealed snap index)

/-- The reveal of a final state: every created owner's identity seed and current or captured scalars. -/
def revealOf (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (snap : Snap) : Reveal :=
  (List.range owners.length).filterMap (revealAt owners snap)

/-- The post-run commands: the public HMAC and the BLAKE2b oracle. -/
inductive PostQuery where
  | hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
  | hash (bytes : Pqxdh.Bytes)

/-- Replies of the post-run commands: an HMAC block and a BLAKE2b digest. -/
abbrev PostQuerySpec : OracleSpec PostQuery
  | .hmac _ _ => PqxdhSecretInputKdf.HmacBlock
  | .hash _ => CtxRomAuth.CtxDigest

/-- The post-run interface: uniform coins, the public HMAC and the BLAKE2b oracle. -/
abbrev PostSpec := unifSpec + PostQuerySpec

/-- The post-run query classes: coin 0, HMAC 1, BLAKE2b 2. -/
def postClass : PostSpec.Domain → Fin 3
  | .inl _ => 0
  | .inr (.hmac _ _) => 1
  | .inr (.hash _) => 2

/-- Post-run budgets `qCoin₂`, `qHmac₂` and `qHash₂`, separate from the run-phase budget. -/
structure PostBudget where
  coin : Nat
  hmac : Nat
  hash : Nat

/-- The cap of each post-run class. -/
def PostBudget.cap (budget : PostBudget) : Fin 3 → Nat := ![budget.coin, budget.hmac, budget.hash]

/-- A post-run adversary respects a post-run budget when every class stays within its cap on every execution path. -/
def PostBudget.Respects {Out : Type} (budget : PostBudget) (adversary : OracleComp PostSpec Out) : Prop :=
  ∀ kind, adversary.IsQueryBoundP (fun query => postClass query = kind) (budget.cap kind)

/-- A post-run query as the run-phase command it repeats. -/
def postEmbed : QueryImpl PostSpec (OracleComp Spec)
  | .inl coin => (Spec.query (.inl coin) : OracleComp Spec _)
  | .inr (.hmac key message) => (Spec.query (.inr (.hmac key message)) : OracleComp Spec _)
  | .inr (.hash bytes) => (Spec.query (.inr (.hash bytes)) : OracleComp Spec _)

/-- The post-run handler on the final deployment state: fresh coins, and the native HMAC and BLAKE2b commands of the run on the final caches. -/
noncomputable def postImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) : QueryImpl PostSpec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin : ProbComp _)
  | .inr (.hmac key message) => PqxdhDeploymentNative.onNative
      (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.hmac key message)))
  | .inr (.hash bytes) => PqxdhDeploymentNative.onNative
      (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.hash bytes)))

/-- The native handler with the finish snapshot: a `finish` first captures the addressed owner's current prekey and one-time fields, then every command runs the unchanged native handler. -/
noncomputable def snapImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) :
    QueryImpl Spec (StateT (Snap × PqxdhDeploymentNative.State KemSK) ProbComp) := fun query state =>
  (fun result => (result.1, (snapshotAt state.1 state.2.native.owners (finishOwner query), result.2))) <$>
    (PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state.2

/-- The run-phase state: the secrecy ledger, the snapshot and the native deployment state. -/
abbrev LaterState (KemSK : Type) := Ledger × (Snap × PqxdhDeploymentNative.State KemSK)

/-- The run-phase handler: the secrecy layer composed with the snapshot handler. -/
noncomputable def laterHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds) :
    QueryImpl PqxdhDeploymentInterface.FullSpec (StateT (LaterState KemSK) ProbComp) :=
  ((snapImpl setup codec checks route serverSeed).mapStateTBase
    (ledgerImpl setup.source.crypto codec setup.serverKeyId bounds)).flattenStateT

/-- The run phase alone, from the constructed Server: the adversary `A₁` against the run-phase handler from the empty ledger and snapshot. -/
noncomputable def laterRun (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × LaterState KemSK)) :=
  fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      (simulateQ (laterHandler setup codec checks route created.seed bounds) (asModeO mode adversary)).run
        (Ledger.empty, (Snap.empty, PqxdhDeploymentNative.initial created))

/-- The later execution from a deployment state: the run phase of `A₁`, the reveal of the final state, and the post phase of `A₂` on the run's output and the reveal. The ledger and snapshot of the run are returned with the state after the post phase. -/
noncomputable def laterExec (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (start : PqxdhDeploymentNative.State KemSK) : ProbComp (Out × LaterState KemSK) := do
  let run ← (simulateQ (laterHandler setup codec checks route serverSeed bounds) (asModeO mode first)).run
    (Ledger.empty, (Snap.empty, start))
  let post ← (simulateQ (postImpl setup codec checks serverSeed)
    (second run.1 (revealOf run.2.2.2.native.owners run.2.2.1))).run run.2.2.2
  pure (post.1, (run.2.1, (run.2.2.1, post.2)))

/-- The later-quantum game: the actual Server constructor with a generated seed (never a supplied one), then the later execution of `A₁` and `A₂` from the initial deployment state. A constructor failure ends the run with no outcome. -/
noncomputable def laterGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK)) :=
  fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      laterExec setup codec checks route created.seed bounds mode first second (PqxdhDeploymentNative.initial created)

/-- Forgetting the snapshot of one snapshot-handler step gives the native handler step. -/
theorem snapImpl_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (state : Snap × PqxdhDeploymentNative.State KemSK) :
    Prod.map id Prod.snd <$> (snapImpl setup codec checks route serverSeed query).run state =
      (PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state.2 := by
  simp only [snapImpl, StateT.run, Functor.map_map, Prod.map_apply, id_eq, Prod.mk.eta, id_map']

/-- Forgetting the snapshot of a whole snapshot-handler run gives the native run: the ghost changes no reply and no native state. -/
theorem snap_erase_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) {Result : Type}
    (program : OracleComp Spec Result) (snap : Snap) (state : PqxdhDeploymentNative.State KemSK) :
    Prod.map id Prod.snd <$> (simulateQ (snapImpl setup codec checks route serverSeed) program).run (snap, state) =
      (simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed) program).run state :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (fun query state => snapImpl_erase setup codec checks route serverSeed query state) program (snap, state)

/-- Running a complete-interface adversary under the run-phase handler is running the wrapped adversary under the snapshot handler, with the ledger moved into the state. -/
theorem later_run_wrap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (adversary : OracleComp PqxdhDeploymentInterface.FullSpec X) (state : Snap × PqxdhDeploymentNative.State KemSK) :
    (simulateQ (laterHandler setup codec checks route serverSeed bounds) adversary).run (Ledger.empty, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (snapImpl setup codec checks route serverSeed)
          (wrap setup.source.crypto codec setup.serverKeyId bounds adversary)).run state := by
  rw [wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  simp only [laterHandler]
  exact (id_map _).symm

/-- Theorem `snap_erase`: forgetting the snapshot of the run phase gives exactly the classical common deployment experiment, jointly over the Server's public data, the adversary's output, the ledger, the complete deployment state and the runtime state. Every run-phase event therefore has the same probability in the later-quantum game as in the classical game. -/
theorem snap_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (fun outcome => (outcome.1.map fun result => (result.1, result.2.1, (result.2.2.1, result.2.2.2.2)), outcome.2)) <$>
        (laterRun setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime =
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run
        runtime := by
  simp only [laterRun, PqxdhDeploymentSecrecy.game, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure, Option.map_none]
  · have later := later_run_wrap setup codec checks route created.seed bounds (asModeO mode adversary)
      (Snap.empty, PqxdhDeploymentNative.initial created)
    have classical := PqxdhDeploymentSecrecy.run_wrap setup codec checks route created.seed bounds
      (asModeO mode adversary) (PqxdhDeploymentNative.initial created)
    have erased := snap_erase_run setup codec checks route created.seed
      (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary)) Snap.empty
      (PqxdhDeploymentNative.initial created)
    simp only [StateT.run] at later classical erased
    simp only [later, classical, ← erased, Functor.map_map, Option.map_some]
    rfl

/-- A capture of an InitSent owner records exactly its prekey and one-time scalars, whatever was captured before. -/
theorem capture_initSent (snap : Snap) (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : owners[index]? = some owner)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (prekey oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (phase : owner.beacon.phase = .initSent control prekey oneTime keys) :
    snapshotAt snap owners (some index) index = ⟨some prekey, some oneTime⟩ := by
  simp only [snapshotAt, capture, fieldOf, found, Option.bind_some, value,
    PqxdhRegistrationJointLiveRead.localValue, phase, scalarOf, Function.update_self, Option.some_or]

/-- The reveal holds exactly one entry per created owner, in creation order. -/
theorem revealOf_eq (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (snap : Snap) :
    revealOf owners snap = owners.mapIdx (revealed snap) := by
  induction owners using List.reverseRecOn with
  | nil => rfl
  | append_singleton init last ih =>
      rw [List.mapIdx_concat, ← ih]
      simp only [revealOf, List.length_append, List.length_singleton, List.range_succ, List.filterMap_append]
      congr 1
      · apply List.filterMap_congr
        intro index member
        have below : index < init.length := List.mem_range.mp member
        simp only [revealAt, List.getElem?_append_left below]
      · simp only [revealAt, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
          Option.map_some, List.filterMap_cons, List.filterMap_nil]

/-- The post phase is the native handler restricted to coins, HMAC and BLAKE2b: running a post-run adversary under `postImpl` is running it, as the run-phase commands it repeats, under the native handler. -/
theorem post_embed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (adversary : OracleComp PostSpec Out) :
    simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed) (simulateQ postEmbed adversary) =
      simulateQ (postImpl setup codec checks serverSeed) adversary := by
  induction adversary using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, ih]
      congr 1
      rcases query with coin | (⟨key, message⟩ | bytes)
      · simp only [postEmbed, simulateQ_spec_query]
        rfl
      · simp only [postEmbed, simulateQ_spec_query]
        rfl
      · simp only [postEmbed, simulateQ_spec_query]
        rfl

/-- A deployment state with the Extract family, the BLAKE2b cache and the ghost touch list replaced and everything else kept. -/
def withCaches (state : PqxdhDeploymentNative.State KemSK) (family : PqxdhJointDhExtractFamily.State)
    (cache : CtxRomAuth.CtxRO.QueryCache) (touches : List Touch) : PqxdhDeploymentNative.State KemSK :=
  { state with native := { state.native with shared := (family,
    { state.native.shared.2 with ctx := cache, ghost := { state.native.shared.2.ghost with touches := touches } }) } }

/-- Two deployment states differ at most in the Extract family, the BLAKE2b cache and the ghost touch list. -/
def Caches (state result : PqxdhDeploymentNative.State KemSK) : Prop :=
  result = withCaches state result.native.shared.1 result.native.shared.2.ctx result.native.shared.2.ghost.touches

/-- The native public HMAC changes at most the Extract family and the ghost touch list of the shared native state. -/
theorem nativeHmac_support (setup : Setup baseSpec KemSK) (serverSeed : IdentitySeed) (scalar : ScalarBytes)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (shared : NativeState KemSK)
    (result : PqxdhSecretInputKdf.HmacBlock × NativeState KemSK)
    (supported : result ∈ support ((nativeHmac setup serverSeed scalar key message).run shared)) :
    ∃ family touches, result.2 = (family, { shared.2 with ghost := { shared.2.ghost with touches := touches } }) := by
  unfold nativeHmac at supported
  dsimp only at supported
  split at supported
  · rw [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨_, middle⟩, touched, forwarded⟩ := supported
    have touchedRun : (nativeTouch (KemSK := KemSK) (.adversary message)).run shared =
        pure ((), (shared.1, { shared.2 with ghost := { shared.2.ghost with
          touches := shared.2.ghost.touches ++ [.adversary message] } })) := rfl
    rw [touchedRun, support_pure, Set.mem_singleton_iff] at touched
    cases touched
    change result ∈ support ((fun inner : PqxdhSecretInputKdf.HmacBlock × PqxdhJointDhExtractFamily.State =>
      (inner.1, (inner.2, _))) <$> _) at forwarded
    rw [support_map] at forwarded
    obtain ⟨inner, _, rfl⟩ := forwarded
    exact ⟨inner.2, _, rfl⟩
  · change result ∈ support ((fun inner : PqxdhSecretInputKdf.HmacBlock × PqxdhJointDhExtractFamily.State =>
      (inner.1, (inner.2, _))) <$> _) at supported
    rw [support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    exact ⟨inner.2, shared.2.ghost.touches, rfl⟩

/-- One post-run query changes at most the Extract family, the BLAKE2b cache and the ghost touch list: owners, the Server, pending tokens, the session counter, the other ghost fields, the raw-attempt counters and the produced frames are untouched. -/
theorem post_step_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (query : PostSpec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (result : PostSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((postImpl setup codec checks serverSeed query).run state)) :
    Caches state result.2 := by
  rcases query with coin | (⟨key, message⟩ | bytes)
  · simp only [postImpl, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  · rw [show (postImpl setup codec checks serverSeed (.inr (.hmac key message))).run state =
        (fun inner => (inner.1, { state with native := { state.native with shared := inner.2 } })) <$>
          (nativeHmac setup serverSeed PqxdhRegistrationSchedule.observationScalar key message).run state.native.shared
        from by simp only [postImpl, PqxdhDeploymentNative.onNative, PqxdhRegistrationSchedule.handler,
          PqxdhRegistrationSchedule.onShared, StateT.run, Functor.map_map]; rfl, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    obtain ⟨family, touches, same⟩ := nativeHmac_support setup serverSeed _ key message _ inner member
    simp only [same]
    rfl
  · simp only [postImpl, PqxdhDeploymentNative.onNative, PqxdhRegistrationSchedule.handler,
      PqxdhRegistrationSchedule.onShared, nativeHash, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨inner, innerSupport, rfl⟩ := supported
    obtain ⟨shared, sharedSupport, rfl⟩ := innerSupport
    obtain ⟨digest, _, rfl⟩ := sharedSupport
    rfl

/-- A state differs from itself at most in its caches. -/
theorem caches_refl (state : PqxdhDeploymentNative.State KemSK) : Caches state state := rfl

/-- Differing at most in the caches is transitive. -/
theorem caches_trans (first second third : PqxdhDeploymentNative.State KemSK) (left : Caches first second)
    (right : Caches second third) : Caches first third := by
  unfold Caches at left right ⊢
  calc third = withCaches second third.native.shared.1 third.native.shared.2.ctx third.native.shared.2.ghost.touches :=
        right
    _ = withCaches first third.native.shared.1 third.native.shared.2.ctx third.native.shared.2.ghost.touches := by
        rw [left]
        rfl

/-- Post-phase frame lemma: a whole post-run phase changes at most the Extract family, the BLAKE2b cache and the ghost touch list. No owner, Server peer, pending token, counter, other ghost field or produced frame changes, and no protocol command runs. -/
theorem post_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (adversary : OracleComp PostSpec Out) (state : PqxdhDeploymentNative.State KemSK)
    (result : Out × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((simulateQ (postImpl setup codec checks serverSeed) adversary).run state)) :
    Caches state result.2 :=
  run_rel (postImpl setup codec checks serverSeed) Caches caches_refl caches_trans
    (post_step_frame setup codec checks serverSeed) adversary state result supported

/-- Every outcome of the later execution keeps the run phase's ledger and snapshot, and its final deployment state differs from the run phase's final state at most in the caches. -/
theorem later_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (start : PqxdhDeploymentNative.State KemSK) (result : Out × LaterState KemSK)
    (supported : result ∈ support (laterExec setup codec checks route serverSeed bounds mode first second start)) :
    ∃ run ∈ support ((simulateQ (laterHandler setup codec checks route serverSeed bounds) (asModeO mode first)).run
        (Ledger.empty, (Snap.empty, start))),
      result.2.1 = run.2.1 ∧ result.2.2.1 = run.2.2.1 ∧ Caches run.2.2.2 result.2.2.2 := by
  simp only [laterExec, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨run, runSupport, post, postSupport, rfl⟩ := supported
  exact ⟨run, runSupport, rfl, rfl, post_frame setup codec checks serverSeed _ _ post postSupport⟩

/-- A capture with both current fields absent keeps the snapshot: a later finish on a terminal owner erases nothing. -/
theorem capture_absent (snap : Snap) (index : Nat) : capture (KemSK := KemSK) snap index none none = snap := by
  funext other
  by_cases same : other = index
  · subst same
    simp only [capture, scalarOf, Option.none_or, Function.update_self]
  · simp only [capture, Function.update_of_ne same]

/-- The reveal has one entry per created owner. -/
theorem revealOf_length (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (snap : Snap) :
    (revealOf owners snap).length = owners.length := by
  rw [revealOf_eq, List.length_mapIdx]

/-- Run-phase events: an event of the Server's public data, the ledger, the snapshot and the deployment state that ignores the caches (the Extract family, the BLAKE2b cache and the ghost touch list) has the same distribution at the end of the later-quantum game as at the end of its run phase. -/
theorem later_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out)
    (event : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × LaterState KemSK) → Bool)
    (invariant : ∀ created ledger snap state result, Caches state result →
      event (some (created, (ledger, (snap, result)))) = event (some (created, (ledger, (snap, state)))))
    (runtime : A) :
    𝒟[(fun outcome => event (outcome.1.map fun result => (result.1, result.2.2))) <$>
        (laterGame setup codec checks route ensureInit identityIndex bounds mode first second).run runtime] =
      𝒟[(fun outcome => event (outcome.1.map fun result => (result.1, result.2.2))) <$>
        (laterRun setup codec checks route ensureInit identityIndex bounds mode first).run runtime] := by
  simp only [laterGame, laterRun, StateT.run, map_bind]
  apply evalDist_bind_congr
  rintro ⟨_ | created, after⟩
  · rfl
  · simp only [laterExec, Functor.map_map, map_bind, map_pure, Option.map_some]
    rw [map_eq_bind_pure_comp]
    apply evalDist_bind_congr
    intro run
    simp only [Function.comp_apply]
    conv_rhs => rw [← OracleComp.evalDist_bind_const ((simulateQ (postImpl setup codec checks created.seed)
      (second run.1 (revealOf run.2.2.2.native.owners run.2.2.1))).run run.2.2.2)]
    apply OracleComp.evalDist_bind_congr_of_support
    intro post member
    simp only [invariant _ _ _ _ _ (post_frame setup codec checks created.seed _ _ post member)]

/-- Run-phase events against the classical game: an event of the Server's public data, the ledger and the deployment state that ignores the caches has the same distribution at the end of the later-quantum game as at the end of the classical common deployment experiment. This is how the run-phase terms (for example the symbolic-eligibility terms) carry over unchanged. -/
theorem later_classical_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out)
    (event : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × PqxdhDeploymentSecrecy.State KemSK) → Bool)
    (invariant : ∀ created ledger state result, Caches state result →
      event (some (created, (ledger, result))) = event (some (created, (ledger, state))))
    (runtime : A) :
    𝒟[(fun outcome => event (outcome.1.map fun result => (result.1, (result.2.2.1, result.2.2.2.2)))) <$>
        (laterGame setup codec checks route ensureInit identityIndex bounds mode first second).run runtime] =
      𝒟[(fun outcome => event (outcome.1.map fun result => (result.1, result.2.2))) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode first).run runtime] := by
  have later := later_event setup codec checks route ensureInit identityIndex bounds mode first second
    (fun outcome => event (outcome.map fun result => (result.1, (result.2.1, result.2.2.2))))
    (fun created ledger snap state result caches => by
      simp only [Option.map_some, invariant created ledger state result caches])
    runtime
  rw [← snap_erase setup codec checks route ensureInit identityIndex bounds mode first runtime, Functor.map_map]
  convert later using 2 <;> (congr 1; funext outcome; rcases outcome with ⟨_ | result, after⟩ <;> rfl)

end BeaconcryptCore.Computational.PqxdhDeploymentLater

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.snapImpl_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.snapImpl_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.snap_erase_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.snap_erase_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.later_run_wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.later_run_wrap

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.snap_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.snap_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.capture_initSent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.capture_initSent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.revealOf_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.revealOf_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.post_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.post_embed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.nativeHmac_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.nativeHmac_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.post_step_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.post_step_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.caches_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.caches_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.caches_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.caches_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.post_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.post_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.later_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.later_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.capture_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.capture_absent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.revealOf_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.revealOf_length

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.later_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.later_event

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLater.later_classical_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLater.later_classical_event
