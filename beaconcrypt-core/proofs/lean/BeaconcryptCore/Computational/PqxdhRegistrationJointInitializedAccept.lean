-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServerAccept

/-! Actual source construction initializes the complete Server accept consumer. The generated seed remains private, caller-known imports retain their origin, and ownership/public-key facts follow from the same constructor run. The existing native root/cache idealization is retained, not replaced by a security assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServerBirth (ClientCreated encode)
open PqxdhLiveServerConstruction (Created)
open PqxdhRegistrationJointServerPrefix (State)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A : Type}

/-- Exact source initial shared state from the seedless owner, including the deterministic aborted compatibility field; no extra honest Beacon or secret is generated. -/
def initial (created : ClientCreated Unit) : NativeState KemSK :=
  (PqxdhJointDhExtractFamily.empty,
    { ctx := ∅
      server :=
        { server := ⟨created.server.server.identity, created.server.server.peers, ()⟩
          identityKeyId := created.server.server.metadata.sender
          control := created.control
          consumed := created.consumed }
      pending := fun _ => none
      beacon := ⟨⟨(), created.server.server.metadata.sender, created.server.server.identity,
        .aborted ⟨created.server.server.metadata.sender⟩⟩, 0⟩
      sessions := 0
      ghost := Ghost.empty })

/-- The seedless initial representation is exactly the native source schedule initialization, retaining every field. -/
theorem initial_encode (created : Created Unit) :
    initial (KemSK := KemSK) (encode created) = (PqxdhRegistrationSchedule.initial created).shared := by
  rfl

/-- Same-run source construction also supplies its actual public identity; this does not posit authentication or key ownership by an honest party. -/
theorem source_public (joint : Primitives) (ensureInit : StateT A ProbComp Bool)
    (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (state after : State KemSK A) (created : Created Unit)
    (supported : (some created, after) ∈ support ((PqxdhRegistrationJointServerBirth.source joint ensureInit sender supplied).run state)) :
    created.publicIdentity = joint.publicKeys created.seed := by
  obtain ⟨seed, shape, _⟩ := PqxdhLiveServerConstruction.construct_origin joint ensureInit state.1.1.seeds.length
    sender supplied state.2 after.2 created
    (PqxdhRegistrationJointServerBirth.source_constructor joint ensureInit sender supplied state after created supported).2
  rw [shape]
  rfl

/-- Private analysis output retains the initialization record/origin, actual optional pending handle and complete native poststate. Only the handle is the public accept reply. -/
abbrev Outcome (KemSK : Type) := ClientCreated Unit × Option Nat × NativeState KemSK

/-- Actual seedless construction followed by the complete raw accept client; every constructor and accept rejection remains an ordinary returned outcome. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) :
    StateT (State KemSK A) ProbComp (Option (Outcome KemSK)) := fun state => do
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client (P := Unit) setup.serverKeyId supplied)).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (created, result.1, result.2.2), (result.2.1, born.2.2))) <$>
      (PqxdhRegistrationJointServerAccept.client setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity raw).run (born.2.1, initial created)

/-- Source mathematical counterpart runs the actual constructor and full native accept with private histories; the exact constructor seed is available only to its source interpretation. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) :
    StateT (State KemSK A) ProbComp (Option (Outcome KemSK)) := fun state => do
  let born ← (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (encode created, result.1, result.2.2), (result.2.1, born.2.2))) <$>
      (PqxdhRegistrationJointServerAccept.source setup codec checks created.seed created.server.server.metadata.identityIndex raw).run
        (born.2.1, (PqxdhRegistrationSchedule.initial created).shared)

/-- Same-execution constructor support discharges both private-slot and public-key premises for the whole actual accept, with no generated-only, honest-Server or successful-admission assumption. -/
theorem initialized_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) (state : State KemSK A) :
    (client setup codec checks ensureInit supplied raw).run state =
      (source setup codec checks ensureInit supplied raw).run state := by
  have born := PqxdhRegistrationJointServerBirth.client_source (P := Unit) setup ensureInit setup.serverKeyId supplied state
  simp only [StateT.run] at born
  simp only [client, source, StateT.run, born, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨(_ | created), after⟩ supported
  · rfl
  · simp only [Option.map_some]
    congr 1
    change (PqxdhRegistrationJointServerAccept.client setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity raw).run (after.1, initial (encode created)) = _
    rw [initial_encode, source_public setup.joint ensureInit setup.serverKeyId supplied state after created supported]
    exact PqxdhRegistrationJointServerAccept.client_source setup codec checks created.seed
      created.server.server.metadata.identityIndex raw _
      (PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId supplied state after created supported)

/-- Actual source constructor followed by the original complete native accept, retaining the whole native poststate and constructor origin as private analysis output. -/
noncomputable def native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) :
    StateT A ProbComp (Option (Outcome KemSK)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId supplied).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (encode created, result), born.2)) <$>
      (nativeAccept setup codec checks created.seed PqxdhRegistrationSchedule.observationScalar raw).run
        (PqxdhRegistrationSchedule.initial created).shared

/-- Complete initialization and acceptance recover the actual original native run after erasing only the private service pool. Both imported and generated origins, every failure and all native caches/state remain. -/
theorem initialized_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) (state : State KemSK A) :
    (fun result => (result.1, result.2.2)) <$> (client setup codec checks ensureInit supplied raw).run state =
      (native setup codec checks ensureInit state.1.1.seeds.length supplied raw).run state.2 := by
  rw [initialized_source]
  simp only [source, native, PqxdhRegistrationJointServerBirth.source, StateT.run, map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨(_ | created), runtime⟩
  · rfl
  · simpa only [StateT.run, Functor.map_map] using congrArg
      (fun work => (fun result => (some (encode created, result), runtime)) <$> work)
      (PqxdhRegistrationJointServerAccept.source_native setup codec checks created.seed
        created.server.server.metadata.identityIndex raw
        (PqxdhRegistrationJointServerBirth.install created state.1, (PqxdhRegistrationSchedule.initial created).shared))

/-- All initialization work, generated identity randomness, prefix scalar/encapsulation work and the reached restricted Extract draw are charged in the same complete execution. -/
theorem initialized_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) (state : State KemSK A) :
    ((client setup codec checks ensureInit supplied raw).run state).IsTotalQueryBound
      ((qInit + if supplied.isNone then 32 else 0) + (96 + caps.encapsCost)) := by
  have nativeBound : ((native setup codec checks ensureInit state.1.1.seeds.length supplied raw).run state.2).IsTotalQueryBound
      ((qInit + if supplied.isNone then 32 else 0) + (96 + caps.encapsCost)) := by
    simp only [native, StateT.run]
    apply isTotalQueryBound_bind (PqxdhLiveServerConstruction.construct_uniform setup.joint ensureInit qInit initBound
      state.1.1.seeds.length setup.serverKeyId supplied state.2)
    rintro ⟨(_ | created), runtime⟩
    · trivial
    · simpa only [StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
        PqxdhRegistrationSchedule.accept_uniform setup codec checks caps bounded created.seed
          PqxdhRegistrationSchedule.observationScalar raw (PqxdhRegistrationSchedule.initial created).shared
  rw [← initialized_native setup codec checks ensureInit supplied raw state] at nativeBound
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using nativeBound

end BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.initial_encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.initial_encode

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.source_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.source_public

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.initialized_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.initialized_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.initialized_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.initialized_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept.initialized_uniform
