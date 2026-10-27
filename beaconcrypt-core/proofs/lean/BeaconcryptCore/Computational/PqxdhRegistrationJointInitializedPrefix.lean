-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth

/-! Same-execution initialization discharges the Server prefix's exact private identity-slot premise. The whole initialized owner, origin, optional prefix result, consumed-registration state, private histories and runtime remain in the compared distribution. This is a source/interface equality, not an authentication, freshness or honest-Server assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix
open PqxdhJointIdentity PqxdhServerAuthExperiment
open PqxdhRegistrationJointServerPrefix (State)
open PqxdhRegistrationJointServerBirth (ClientCreated encode)
open PqxdhLiveServerConstruction (Created)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response P A : Type}

abbrev Answer (Reader P : Type) := ClientCreated P × Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32)

/-- The actual compiled raw prefix is addressed by the seedless owner's exact identity index; every consumed-registration update is reinstalled into that complete owner. -/
def clientBody (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (created : ClientCreated P) : StateT (State KemSK A) ProbComp (Answer Reader P) := fun state =>
  (fun result => (({ created with consumed := result.2.2 }, result.1), (result.2.1, state.2))) <$>
    (simulateQ (PqxdhRegistrationJointServerPrefix.impl setup (serverAux setup codec checks))
      (PqxdhRegistrationJointServerPrefix.clientPrefix created.server.server.metadata.identityIndex raw)).run
        (state.1, created.consumed)

/-- Mathematical source counterpart retains the exact actual seed only within its native interpretation, with the same complete owner and service histories. -/
def sourceBody (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (created : Created P) : StateT (State KemSK A) ProbComp (Answer Reader P) := fun state =>
  (fun result => ((encode { created with consumed := result.2.2 }, result.1), (result.2.1, state.2))) <$>
    (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint created.seed
      created.server.server.metadata.identityIndex (serverAux setup codec checks))
      (PqxdhServerRootPreparation.collect raw)).run (state.1, created.consumed)

/-- Same-state source ownership suffices for the whole raw-prefix body, retaining the full native initialized owner rather than only public key marginals. -/
theorem body_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (created : Created P) (state : State KemSK A)
    (owned : state.1.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) :
    (clientBody setup codec checks raw (encode created)).run state =
      (sourceBody setup codec checks raw created).run state := by
  simp only [clientBody, sourceBody, StateT.run, encode]
  congr 1
  exact PqxdhRegistrationJointServerPrefix.prefix_source setup codec checks created.seed
    created.server.server.metadata.identityIndex raw state.1 created.consumed owned

/-- Executable initialization followed by the actual raw Server prefix; neither stage carries the generated Server seed outside its private interpreter. -/
def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) :
    StateT (State KemSK A) ProbComp (Option (Answer Reader P)) := do
  let created ← simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client sender supplied)
  match created with
  | none => pure none
  | some created => some <$> clientBody setup codec checks raw created

/-- The same actual source constructor and native prefix, retaining only private mathematical annotations in addition to the original state. -/
def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) :
    StateT (State KemSK A) ProbComp (Option (Answer Reader P)) := do
  let created ← PqxdhRegistrationJointServerBirth.source setup.joint ensureInit sender supplied
  match created with
  | none => pure none
  | some created => some <$> sourceBody setup codec checks raw created

/-- Actual same-execution initialization discharges every prefix slot premise for both generated and imported identities. All optional constructor/prefix results, origins and complete states agree without an honest-Server premise. -/
theorem initialized_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes)
    (state : State KemSK A) :
    (client (P := P) setup codec checks ensureInit sender supplied raw).run state =
      (source (P := P) setup codec checks ensureInit sender supplied raw).run state := by
  simp only [client, source, StateT.run_bind, PqxdhRegistrationJointServerBirth.client_source, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨(_ | created), after⟩ supported
  · rfl
  · simp only [Option.map_some, StateT.run_map]
    rw [body_source setup codec checks raw created after
      (PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit sender supplied state after created supported)]

/-- The unannotated actual native prefix retains its full initialized owner and consumed-registration poststate. -/
noncomputable def nativeBody (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (created : Created P) : StateT A ProbComp (Answer Reader P) := fun runtime =>
  (fun result => ((encode { created with consumed := result.2 }, result.1), runtime)) <$>
    (PqxdhServerAuthNative.nativePrefix setup codec checks created.seed raw).run created.consumed

/-- Erasing only the private service pool recovers the complete original raw-prefix distribution, including its actual native consumed-registration update. -/
theorem body_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (created : Created P) (state : State KemSK A) :
    (fun result => (result.1, result.2.2)) <$> (sourceBody setup codec checks raw created).run state =
      (nativeBody setup codec checks raw created).run state.2 := by
  have projected := PqxdhRegistrationJointServerPrefix.program_projection setup.joint created.seed
    created.server.server.metadata.identityIndex (serverAux setup codec checks)
    (PqxdhServerRootPreparation.collect raw) (state.1, created.consumed)
  simpa only [sourceBody, nativeBody, PqxdhServerAuthNative.nativePrefix, StateT.run, Functor.map_map] using congrArg
    (fun work => (fun result => ((encode { created with consumed := result.2 }, result.1), state.2)) <$> work) projected

/-- Original source construction followed by its actual native raw prefix, with the same chosen initialization index and full runtime state. -/
noncomputable def native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (sender : Std.U64)
    (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) : StateT A ProbComp (Option (Answer Reader P)) := do
  let created ← PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex sender supplied
  match created with
  | none => pure none
  | some created => some <$> nativeBody setup codec checks raw created

/-- The complete compiled initialization/prefix distribution projects to the actual source constructor and actual native prefix, preserving their order, all outcomes and the entire initialized owner/runtime. -/
theorem initialized_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes)
    (state : State KemSK A) :
    (fun result => (result.1, result.2.2)) <$> (client (P := P) setup codec checks ensureInit sender supplied raw).run state =
      (native (P := P) setup codec checks ensureInit state.1.1.seeds.length sender supplied raw).run state.2 := by
  rw [initialized_source]
  simp only [source, native, StateT.run_bind]
  simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨(_ | created), runtime⟩
  · rfl
  · change (fun result => (result.1, result.2.2)) <$> StateT.run (some <$> sourceBody setup codec checks raw created) _ =
      StateT.run (some <$> nativeBody setup codec checks raw created) runtime
    simpa only [StateT.run_map, Functor.map_map] using congrArg
      (fun work => (fun result => (some result.1, result.2)) <$> work)
      (body_projection setup codec checks raw created (PqxdhRegistrationJointServerBirth.install created state.1, runtime))

/-- The entire native prefix body, with its owner-update continuation, charges scalar sampling and the actual KEM encapsulation/base sampler. -/
theorem native_body_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (raw : Pqxdh.Bytes) (created : Created P) (runtime : A) :
    ((nativeBody setup codec checks raw created).run runtime).IsTotalQueryBound (32 + caps.encapsCost) := by
  simp only [nativeBody, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
  change ((PqxdhServerAuthNative.nativePrefix setup codec checks created.seed raw).run created.consumed).IsTotalQueryBound _
  rw [PqxdhServerAuthNative.native_prefix, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
  exact PqxdhServerAuthSourceCosts.server_prefix_uniform setup codec checks caps bounded raw created.consumed

/-- The complete initialized client charges the initialization callback, the generated branch's identity sampler, the prefix scalar sampler, and KEM encapsulation/base work. Early failures only reduce these caps. -/
theorem initialized_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (raw : Pqxdh.Bytes) (state : State KemSK A) :
    ((client (P := P) setup codec checks ensureInit sender supplied raw).run state).IsTotalQueryBound
      ((qInit + if supplied.isNone then 32 else 0) + (32 + caps.encapsCost)) := by
  have nativeBound : ((native (P := P) setup codec checks ensureInit state.1.1.seeds.length sender supplied raw).run state.2).IsTotalQueryBound
      ((qInit + if supplied.isNone then 32 else 0) + (32 + caps.encapsCost)) := by
    simp only [native, StateT.run_bind]
    apply isTotalQueryBound_bind (PqxdhLiveServerConstruction.construct_uniform setup.joint ensureInit qInit initBound
      state.1.1.seeds.length sender supplied state.2)
    rintro ⟨(_ | created), runtime⟩
    · trivial
    · simpa only [StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff] using
        native_body_uniform setup codec checks caps bounded raw created runtime
  rw [← initialized_native setup codec checks ensureInit sender supplied raw state] at nativeBound
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using nativeBound

end BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.body_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.initialized_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.body_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.body_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.initialized_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.initialized_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.native_body_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.native_body_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.initialized_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedPrefix.initialized_uniform
