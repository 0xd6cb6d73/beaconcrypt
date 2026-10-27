-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocol

/-! Actual dynamic storage fixes physical roles and installation origins, preserves existing senders, and advances hidden send coordinates before optional writer replies. A private trace of the literal sealing service erases to the complete source execution and has no repeated structural coordinate from the actual initial state. This is an operational history theorem; key-byte aliases and the selected CTX stop join remain separate. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance
open PqxdhRecordLiftInterface PqxdhRecordLiftWorldCompiler
variable {n : Nat}

def sendDirection : Role → Bool
  | .server => false
  | .beacon => true

/-- The actual storage role fixes both directional labels; caller-known kernels carry no hidden-label obligation. -/
def Oriented (role : Role) : StoredKernel n → Prop
  | .known _ => True
  | .hidden slot kernel => PqxdhRecordLiftChainCoordinates.Certified kernel ∧
      KernelOrigin slot kernel ∧ kernel.send_chain.direction = sendDirection role ∧
        kernel.receive_chain.direction = !sendDirection role

/-- Physical Server peers and established Beacon owners carry their own role's source orientation. -/
def Roles (state : State n) : Prop :=
  (∀ server, state.server = some server → ∀ keyId peer, server.peers keyId = some peer →
    Oriented .server peer.kernel) ∧
  (∀ phase ∈ state.owners, match phase with
    | .inactive _ => True
    | .established _ kernel => Oriented .beacon kernel)

/-- Arbitrary private lookup replies and optional opening results preserve physical role orientation through the actual receive. -/
theorem kernel_receive_oriented {P : Type} (role : Role)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative P) (stored : StoredKernel n)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (oriented : Oriented role stored)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelReceive seeds lookup native stored target context).run state)) :
    Oriented role result.1.1 := by
  cases stored with
  | hidden slot kernel =>
      simp only [kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have coordinates := PqxdhRecordLiftChainCoordinates.receive_origins kernel inner.1.1
        (PqxdhRecordLiftChainCoordinates.admitted_receive_coordinates seeds lookup
          (PqxdhRecordLiftNativeAdapters.receiveOpen native) kernel context target
          oriented.1.1.capacity state inner member)
      exact ⟨PqxdhRecordLiftChainCoordinates.receive_certified seeds lookup
        (PqxdhRecordLiftNativeAdapters.receiveOpen native) kernel context target oriented.1 state inner member,
        ⟨(congrArg (fun coordinate => coordinate.slot) coordinates.1).trans oriented.2.1.1,
          coordinates.2.1.trans oriented.2.1.2⟩,
        (congrArg (fun coordinate => coordinate.direction) coordinates.1).trans oriented.2.2.1,
        coordinates.2.2.trans oriented.2.2.2⟩
  | known kernel =>
      simp only [kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      exact supported.elim fun inner ⟨_, equal⟩ => equal ▸ True.intro

/-- The actual send keeps its physical role orientation even when the native writer returns no ciphertext. -/
theorem kernel_send_oriented {P : Type} (role : Role)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.SendNative P) (stored : StoredKernel n)
    (context : RawCtxSourceSend.SealContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (oriented : Oriented role stored)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelSend seeds lookup native stored context).run state)) :
    Oriented role result.1.1 := by
  cases stored with
  | hidden slot kernel =>
      simp only [kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have coordinates := PqxdhRecordLiftChainCoordinates.send_origins kernel inner.1.1
        (PqxdhRecordLiftChainCoordinates.admitted_send_coordinates seeds lookup
          (PqxdhRecordLiftNativeAdapters.sendSeal native) kernel context state inner member)
      exact ⟨PqxdhRecordLiftChainCoordinates.send_certified seeds lookup
        (PqxdhRecordLiftNativeAdapters.sendSeal native) kernel context oriented.1 state inner member,
        ⟨coordinates.2.2.1.trans oriented.2.1.1,
          (congrArg (fun coordinate => coordinate.slot) coordinates.1).trans oriented.2.1.2⟩,
        coordinates.2.2.2.trans oriented.2.2.1,
        (congrArg (fun coordinate => coordinate.direction) coordinates.1).trans oriented.2.2.2⟩
  | known kernel =>
      simp only [kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      exact supported.elim fun inner ⟨_, equal⟩ => equal ▸ True.intro

/-- The source initializer, rather than a caller-supplied role certificate, establishes both physical directions. -/
theorem labeledKernel_oriented (role : Role) (slot : Slot n) :
    Oriented role (.hidden slot (labeledKernel role slot)) := by
  refine ⟨(labeledKernel_ready ∅ role slot).2, labeledKernel_origin role slot, ?_⟩
  have actual := labeledKernel_exact role slot
  cases role <;> exact (RustM.ok.inj actual) ▸ ⟨rfl, rfl⟩

/-- Parser rejection, cached/future opening and rollback all preserve the selected physical owner's directions. -/
theorem owner_receive_oriented {P : Type} (role : Role)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (oriented : Oriented role owner.kernel)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((ownerReceive seeds lookup native decode raw owner).run state)) :
    Oriented role result.1.2.kernel := by
  simp only [ownerReceive, StateT.run] at supported
  repeat' split at supported
  case h_2.isTrue =>
    simp only [bind_pure_comp, support_map] at supported
    exact supported.elim fun inner ⟨member, equal⟩ => equal ▸
      kernel_receive_oriented role seeds lookup (receiveNative native) owner.kernel _ _ state oriented inner member
  all_goals simp only [support_pure, Set.mem_singleton_iff] at supported
  all_goals exact supported.symm ▸ oriented

/-- Empty input and a completed native send preserve the selected physical owner's directions. -/
theorem owner_send_oriented {P : Type} (role : Role)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (oriented : Oriented role owner.kernel)
    (result : (Option RawCtxSourceSend.Encrypted × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((ownerSend seeds lookup native sender plaintext owner).run state)) :
    Oriented role result.1.2.kernel := by
  simp only [ownerSend, StateT.run] at supported
  split_ifs at supported with empty
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    exact supported.symm ▸ oriented
  · simp only [bind_pure_comp, support_map] at supported
    exact supported.elim fun inner ⟨member, equal⟩ => equal ▸
      kernel_send_oriented role seeds lookup (sendNative native) owner.kernel _ state oriented inner member

/-- The complete selected-owner command preserves directions for either source branch. -/
theorem owner_step_oriented {P : Type} (role : Role)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (oriented : Oriented role owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((ownerStep seeds lookup native sender decode query owner).run state)) :
    Oriented role result.1.2.kernel := by
  cases query with
  | inl plaintext => exact owner_send_oriented role seeds lookup native sender plaintext owner state oriented result supported
  | inr raw => exact owner_receive_oriented role seeds lookup native decode raw owner state oriented result supported

/-- Replacing one physical Server peer preserves the role invariant of every other stored record. -/
theorem roles_server_store (state : State n) (server : Server n)
    (existing : state.server = some server) (keyId : Std.U64) (peer : Peer n)
    (before : Roles state) (added : Oriented .server peer.kernel) :
    Roles { state with server := some { server with peers := Function.update server.peers keyId (some peer) } } := by
  constructor
  · intro selected found target stored present
    simp only [Option.some.injEq] at found
    subst selected
    change Function.update server.peers keyId (some peer) target = some stored at present
    by_cases same : target = keyId
    · subst target
      rw [Function.update_self] at present
      cases Option.some.inj present
      exact added
    · rw [Function.update_of_ne same] at present
      exact before.1 server existing target stored present
  · exact before.2

/-- Replacing one Beacon phase preserves every other physical record's role invariant. -/
theorem roles_owner_store (state : State n) (owner : Nat) (phase : Phase n) (before : Roles state)
    (added : match phase with | .inactive _ => True | .established _ kernel => Oriented .beacon kernel) :
    Roles { state with owners := state.owners.set owner phase } := by
  constructor
  · exact before.1
  · intro selected member
    rcases List.mem_or_eq_of_mem_set member with prior | equal
    · exact before.2 selected prior
    · subst selected
      exact added

/-- Actual role-directed seed resolution supplies the new orientation and leaves all existing records intact. -/
theorem resolve_roles (role : Role) (ref : KernelRef n) (state : State n) (roles : Roles state)
    (result : StoredKernel n × State n) (supported : result ∈ support ((resolve role ref).run state)) :
    Roles result.2 ∧ Oriented role result.1 := by
  cases ref with
  | known known =>
      simp only [resolve, StateT.run] at supported
      subst result
      exact ⟨roles, trivial⟩
  | hidden slot =>
      simp only [resolve, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact ⟨roles, labeledKernel_oriented role slot⟩

/-- The one-use marker changes no physical record. -/
theorem markUsed_roles (state : State n) (role : Role) (ref : KernelRef n) (roles : Roles state) :
    Roles (markUsed state role ref) := by
  cases ref <;> exact roles

/-- Successful Beacon installation establishes the physical Beacon directions; refusal leaves them intact. -/
theorem installBeacon_roles (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : State n) (roles : Roles state) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) : Roles result.2 := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have resolved := resolve_roles .beacon ref state roles inner member
    have owners : (markUsed inner.2 .beacon ref).owners = state.owners := by
      cases ref <;> exact (resolve_fields .beacon _ state inner member).2.1
    rw [← owners]
    apply roles_owner_store _ _ _ (markUsed_roles inner.2 .beacon ref resolved.1)
    cases ref <;> exact resolved.2
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact roles

/-- Successful Server installation establishes the physical Server directions; occupied handles and repeat use are refused. -/
theorem installServer_roles (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : State n) (roles : Roles state) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) : Roles result.2 := by
  simp only [installServer, StateT.run] at supported
  cases found : state.server with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact roles
  | some server =>
      simp only [found] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        have resolved := resolve_roles .server ref state roles inner member
        have same : (markUsed inner.2 .server ref).server = some server := by
          cases ref <;> exact (resolve_fields .server _ state inner member).1.trans found
        apply roles_server_store _ server same keyId ⟨identity, inner.1⟩
          (markUsed_roles inner.2 .server ref resolved.1)
        cases ref <;> exact resolved.2
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact roles

/-- The actual constructor imports only caller-known peers; it cannot assign a hidden record the wrong role. -/
theorem initialize_roles (created : PqxdhLiveServerConstruction.Created Unit) (state : State n)
    (roles : Roles state) (result : Unit × State n)
    (supported : result ∈ support ((initializeServer created).run state)) : Roles result.2 := by
  simp only [initializeServer, StateT.run] at supported
  cases found : state.server with
  | some server =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact roles
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      constructor
      · intro server existing keyId peer present
        simp only [Option.some.injEq] at existing
        subst server
        simp only [Server.fromKnown] at present
        cases entry : created.server.server.peers keyId with
        | none => simp [entry] at present
        | some native =>
            simp only [entry, Option.map_some, Option.some.injEq] at present
            subst peer
            trivial
      · exact roles.2

theorem roles_append (state : State n) (phase : InactivePhase) (roles : Roles state) :
    Roles { state with owners := state.owners ++ [.inactive phase] } := by
  constructor
  · exact roles.1
  · intro present member
    rcases List.mem_append.mp member with prior | appended
    · exact roles.2 present prior
    · simp only [List.mem_singleton] at appended
      subst present
      trivial

/-- Administrative transitions, presence checks and public hashing preserve both physical roles. -/
theorem capability_roles (query : (CapabilitySpec n).Domain) (state : State n) (roles : Roles state)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) : Roles result.2 := by
  cases query with
  | installServer keyId identity ref => exact installServer_roles keyId identity ref state roles result supported
  | installBeacon owner shell ref => exact installBeacon_roles owner shell ref state roles result supported
  | peerPresent keyId =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact roles
  | ownerPresent owner =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact roles
  | appendOwner sender pin phase =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact roles_append state phase roles
  | hash bytes =>
      simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact roles
  | advanceOwner owner phase =>
      simp only [capability, StateT.run] at supported
      split at supported
      · split_ifs at supported with allowed
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact roles_owner_store state owner (.inactive phase) roles trivial
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact roles
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact roles

/-- Direct environment effects cannot alter physical role orientation. -/
theorem effects_roles (query : (EnvEffects n).Domain) (state : State n) (roles : Roles state)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) : Roles result.2 := by
  cases query with
  | inl coin =>
      simp only [effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact roles
  | inr request => exact capability_roles request (chargeEffect (.inr request) state) roles result supported

/-- The logged interpreter preserves physical directions under every lookup policy, including mixed real/ideal policies. -/
theorem ownerRun_oriented {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (role : Role) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (oriented : Oriented role owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (supported : result ∈ support (ownerRun policy setup codec sender query owner state)) :
    Oriented role result.1.2.kernel :=
  owner_step_oriented role (cachedSeeds state) _ _ sender codec.frameRead query owner
    (state.chain, (state.primitive, [])) oriented result supported

/-- A Beacon's complete putback retains its source shell and updates exactly its own physical kernel. -/
theorem beaconPublish_roles {Reply : Type} (state : State n) (owner : Nat) (shell : BeaconShell)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (roles : Roles state) (oriented : Oriented .beacon result.1.2.kernel) :
    Roles (beaconPublish state owner shell result).2 :=
  roles_owner_store state owner (.established shell result.1.2.kernel) roles oriented

/-- The Server raw-attempt counter does not change any physical record. -/
theorem roles_serverRaw (state : State n) (server : Server n) (existing : state.server = some server)
    (rawAttempts : Nat) (roles : Roles state) :
    Roles { state with server := some { server with rawAttempts := rawAttempts } } := by
  refine ⟨?_, roles.2⟩
  intro actual found keyId peer selected
  cases Option.some.inj found
  exact roles.1 server existing keyId peer selected

/-- A Server's complete putback retains every unselected peer and the selected peer's physical role. -/
theorem serverPublish_roles {Reply : Type} (tag : PqxdhDeploymentInterface.FrameTag)
    (state : State n) (server : Server n) (existing : state.server = some server)
    (keyId : Std.U64) (peer : Peer n)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (roles : Roles state) (oriented : Oriented .server result.1.2.kernel) :
    Roles (serverPublish tag state server keyId peer result).2 := by
  let counted := { state with server := some { server with rawAttempts := result.1.2.rawAttempts } }
  exact roles_server_store counted { server with rawAttempts := result.1.2.rawAttempts } rfl keyId
    { peer with kernel := result.1.2.kernel }
    (roles_serverRaw state server existing result.1.2.rawAttempts roles) oriented

/-- Every Beacon routing branch preserves the physical role under an arbitrary private lookup policy. -/
theorem beaconStep_roles {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State n) (roles : Roles state)
    (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep policy setup codec owner query).run state)) :
    Roles result.2 := by
  cases selected : state.owners[owner]? with
  | none =>
      simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact roles
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported <;>
            subst result <;> exact roles
      | established shell kernel =>
          simp only [beaconStep, StateT.run, selected, support_map] at supported
          obtain ⟨inner, member, rfl⟩ := supported
          have present := List.mem_of_getElem? selected
          have oriented : Oriented .beacon kernel := roles.2 _ present
          exact beaconPublish_roles state owner shell inner roles
            (ownerRun_oriented policy .beacon setup codec shell.identityKeyId query _ state oriented inner member)

/-- Every Server routing branch preserves the physical role, including absent peers and failed header routing. -/
theorem serverStep_roles {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State n) (roles : Roles state)
    (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep policy setup codec route query).run state)) :
    Roles result.2 := by
  cases existing : state.server with
  | none =>
      cases query <;>
        simp only [serverStep, StateT.run, existing, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact roles
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [serverStep, StateT.run, existing, selected, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact roles
          | some peer =>
              simp only [serverStep, StateT.run, existing, selected, support_map] at supported
              obtain ⟨inner, member, rfl⟩ := supported
              have oriented := roles.1 server existing keyId peer selected
              exact serverPublish_roles _ state server existing keyId peer inner roles
                (ownerRun_oriented policy .server setup codec server.sender (.inl plaintext) _ state oriented inner member)
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [serverStep, StateT.run, existing, routed, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact roles_serverRaw state server existing (server.rawAttempts + 1) roles
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact roles_serverRaw state server existing (server.rawAttempts + 1) roles
              | some peer =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_map] at supported
                  obtain ⟨inner, member, rfl⟩ := supported
                  have oriented := roles.1 server existing keyId peer selected
                  exact serverPublish_roles _ state server existing keyId peer inner roles
                    (ownerRun_oriented policy .server setup codec server.sender (.inr raw) _ state oriented inner member)

/-- Every actual world request preserves physical orientation under any lookup policy. -/
theorem handler_roles {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n) (roles : Roles state)
    (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler policy setup codec route query).run state)) :
    Roles result.2 := by
  cases query with
  | inl created =>
      exact initialize_roles created state roles result supported
  | inr outer =>
      cases outer with
      | inl effect =>
          exact effects_roles effect state roles result supported
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact serverStep_roles policy setup codec route (.inl send) state roles result supported
              | inr raw => exact serverStep_roles policy setup codec route (.inr raw) state roles result supported
          | inr ownerQuery =>
              obtain ⟨owner, query⟩ := ownerQuery
              cases query with
              | inl plaintext => exact beaconStep_roles policy setup codec owner (.inl plaintext) state roles result supported
              | inr raw => exact beaconStep_roles policy setup codec owner (.inr raw) state roles result supported

/-- No hidden physical records exist initially. -/
theorem initial_roles : Roles (initial : State n) := by
  simp [Roles, initial]

/-- Adaptive commands preserve physical role orientation from the actual preceding state, with no reachability assumption. -/
theorem schedule_roles {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : State n) (roles : Roles state)
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler policy setup codec route) client).run state)) :
    Roles result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact roles
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨inner, member, continued⟩ := supported
      exact ih inner.1 inner.2 (handler_roles policy setup codec route query state roles inner member) result continued

/-- Every result of the actual frozen program has its physical role directions, for arbitrary environment and lookup policy. -/
theorem run_roles {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run policy setup codec route env serverKid bounds mode adversary)) :
    Roles result.2 :=
  schedule_roles policy setup codec route (program env setup.source.crypto codec serverKid bounds mode adversary)
    initial initial_roles result supported

/-- A send preserves the actual installation tag, independently of all source certificates and lookup effects. -/
theorem kernelSend_origin {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.SendNative P) (stored : StoredKernel n)
    (context : RawCtxSourceSend.SealContext) (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelSend seeds lookup native stored context).run state)) :
    result.1.1.origin = stored.origin := by
  cases stored <;> simp only [kernelSend, StateT.run, bind_pure_comp, support_map] at supported
  all_goals obtain ⟨inner, member, rfl⟩ := supported
  all_goals rfl

/-- A receive preserves the actual installation tag, independently of all source certificates and lookup effects. -/
theorem kernelReceive_origin {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative P) (stored : StoredKernel n)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelReceive seeds lookup native stored target context).run state)) :
    result.1.1.origin = stored.origin := by
  cases stored <;> simp only [kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
  all_goals obtain ⟨inner, member, rfl⟩ := supported
  all_goals rfl

/-- Every selected-owner operation preserves its installation origin, including malformed input and complete receive rollback. -/
theorem ownerStep_origin {P : Type}
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((ownerStep seeds lookup native sender decode query owner).run state)) :
    result.1.2.kernel.origin = owner.kernel.origin := by
  cases query with
  | inl plaintext =>
      simp only [ownerStep, ownerSend, StateT.run] at supported
      split_ifs at supported with empty
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        exact supported.symm ▸ rfl
      · simp only [bind_pure_comp, support_map] at supported
        exact supported.elim fun inner ⟨member, equal⟩ => equal ▸
          kernelSend_origin seeds lookup (sendNative native) owner.kernel _ state inner member
  | inr raw =>
      simp only [ownerStep, ownerReceive, StateT.run] at supported
      repeat' split at supported
      case h_2.isTrue =>
        simp only [bind_pure_comp, support_map] at supported
        exact supported.elim fun inner ⟨member, equal⟩ => equal ▸
          kernelReceive_origin seeds lookup (receiveNative native) owner.kernel _ _ state inner member
      all_goals simp only [support_pure, Set.mem_singleton_iff] at supported
      all_goals exact supported.symm ▸ rfl

/-- Logging native calls cannot change the selected record’s installation origin. -/
theorem ownerRun_origin {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (supported : result ∈ support (ownerRun policy setup codec sender query owner state)) :
    result.1.2.kernel.origin = owner.kernel.origin :=
  ownerStep_origin (cachedSeeds state) _ _ sender codec.frameRead query owner
    (state.chain, (state.primitive, [])) result supported

/-- Storing a Server peer changes the computed origin map at exactly the actual target handle. -/
theorem origins_server_store (state : State n) (server : Server n)
    (existing : state.server = some server) (keyId : Std.U64) (peer : Peer n) :
    origins { state with server := some { server with peers := Function.update server.peers keyId (some peer) } } =
      { origins state with peers := Function.update (origins state).peers keyId peer.kernel.origin } := by
  apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
  · funext target
    by_cases same : target = keyId
    · simp [origins, existing, same]
    · simp [origins, existing, Function.update_of_ne same]
  · rfl

/-- Storing a Beacon phase changes the computed origin map at exactly its existing list index. -/
theorem origins_owner_store (state : State n) (owner : Nat) (phase : Phase n)
    (present : owner < state.owners.length) :
    origins { state with owners := state.owners.set owner phase } =
      { origins state with owners := Function.update (origins state).owners owner phase.origin } := by
  apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
  · rfl
  · funext target
    by_cases same : target = owner
    · simp [origins, same, List.getElem?_set_self present]
    · simp [origins, Function.update_of_ne same, List.getElem?_set_ne (Ne.symm same)]

/-- Complete primitive, table and marker changes leave computed origins unchanged when both record stores are unchanged. -/
theorem origins_frame (before after : State n) (server : after.server = before.server)
    (owners : after.owners = before.owners) : origins after = origins before := by
  simp only [origins, server, owners]

/-- The computed Server origins follow the actual installation reply, without assuming prior reachability. -/
theorem installServer_origins (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) :
    origins result.2 = if result.1 then
      { origins state with peers := Function.update (origins state).peers keyId (PqxdhRecordLiftOrigins.origin ref) }
      else origins state := by
  simp only [installServer, StateT.run] at supported
  cases found : state.server with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | some server =>
      simp only [found] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        have fields := resolve_fields .server ref state inner member
        have same : (markUsed inner.2 .server ref).server = some server := by
          cases ref <;> exact fields.1.trans found
        have old : origins (markUsed inner.2 .server ref) = origins state := by
          apply origins_frame
          · cases ref <;> exact fields.1
          · cases ref <;> exact fields.2.1
        change origins { markUsed inner.2 .server ref with
          server := some { server with peers := Function.update server.peers keyId (some ⟨identity, inner.1⟩) } } = _
        rw [origins_server_store _ server same, old, fields.2.2.2.2]
        rfl
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        rfl

/-- The computed Beacon origins follow the actual installation reply at its admitted existing index. -/
theorem installBeacon_origins (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) :
    origins result.2 = if result.1 then
      { origins state with owners := Function.update (origins state).owners owner (PqxdhRecordLiftOrigins.origin ref) }
      else origins state := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have fields := resolve_fields .beacon ref state inner member
    have same : (markUsed inner.2 .beacon ref).owners = state.owners := by
      cases ref <;> exact fields.2.1
    have old : origins (markUsed inner.2 .beacon ref) = origins state := by
      apply origins_frame
      · cases ref <;> exact fields.1
      · exact same
    have bound : owner < (markUsed inner.2 .beacon ref).owners.length := by
      rw [same]
      exact (List.getElem?_eq_some_iff.mp admitted.1).1
    change origins { markUsed inner.2 .beacon ref with
      owners := state.owners.set owner (.established shell inner.1) } = _
    rw [← same, origins_owner_store _ owner _ bound, old]
    rw [show (Phase.established shell inner.1).origin = PqxdhRecordLiftOrigins.origin ref from fields.2.2.2.2]
    rfl
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl

/-- Appending an inactive owner agrees with the returned fresh handle's absent-origin annotation. -/
theorem origins_append (state : State n) (phase : InactivePhase) :
    origins { state with owners := state.owners ++ [.inactive phase] } =
      { origins state with owners := Function.update (origins state).owners state.owners.length none } := by
  apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
  · rfl
  · funext target
    by_cases same : target = state.owners.length
    · simp [origins, same, Phase.origin]
    · rw [Function.update_of_ne same]
      by_cases within : target < state.owners.length
      · simp only [origins, List.getElem?_append_left within]
      · have outside : state.owners.length < target := by omega
        simp only [origins, List.getElem?_append_right (by omega : state.owners.length ≤ target),
          List.getElem?_eq_none (by simp; omega : [Phase.inactive (n := n) phase].length ≤ target - state.owners.length),
          List.getElem?_eq_none (by omega : state.owners.length ≤ target), Option.bind_none]

/-- Whole-owner putback with the same tag preserves the computed origin map. -/
theorem origins_owner_same (state : State n) (owner : Nat) (before after : Phase n)
    (present : state.owners[owner]? = some before) (same : after.origin = before.origin) :
    origins { state with owners := state.owners.set owner after } = origins state := by
  rw [origins_owner_store state owner after (List.getElem?_eq_some_iff.mp present).1]
  apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
  · rfl
  · funext target
    by_cases selected : target = owner
    · subst target
      simp only [Function.update_self, origins, present, Option.bind_some, same]
    · rw [Function.update_of_ne selected]
      rfl

/-- Actual administrative and public-hash replies determine exactly the computed origin annotation. -/
theorem capability_origins (query : (CapabilitySpec n).Domain) (state : State n)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) :
    origins result.2 = PqxdhRecordLiftOrigins.annotate (.inr (.inl (.inr query))) result.1 (origins state) := by
  cases query with
  | installServer keyId identity ref => exact installServer_origins keyId identity ref state result supported
  | installBeacon owner shell ref => exact installBeacon_origins owner shell ref state result supported
  | peerPresent keyId =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | ownerPresent owner =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | appendOwner sender pin phase =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact origins_append state phase
  | hash bytes =>
      simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      rfl
  | advanceOwner owner phase =>
      simp only [capability, StateT.run] at supported
      split at supported
      · rename_i before present
        split_ifs at supported with allowed
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact origins_owner_same state owner (.inactive before) (.inactive phase) present rfl
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          rfl
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        rfl

/-- Charging environment effects and sampling coins leave the administrative origin equation exact. -/
theorem effects_origins (query : (EnvEffects n).Domain) (state : State n)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) :
    origins result.2 = PqxdhRecordLiftOrigins.annotate (.inr (.inl query)) result.1 (origins state) := by
  cases query with
  | inl coin =>
      simp only [effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      rfl
  | inr request => exact capability_origins request (chargeEffect (.inr request) state) result supported

/-- Initial Server construction introduces no hidden origin and cannot reset an existing Server. -/
theorem initialize_origins (created : PqxdhLiveServerConstruction.Created Unit) (state : State n)
    (result : Unit × State n) (supported : result ∈ support ((initializeServer created).run state)) :
    origins result.2 = origins state := by
  simp only [initializeServer, StateT.run] at supported
  cases found : state.server with
  | some server =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
      · funext keyId
        cases entry : created.server.server.peers keyId <;>
          simp [found, Server.fromKnown, Peer.fromKnown, entry, StoredKernel.origin]
      · rfl

/-- Complete Beacon publication preserves the origin of the selected existing owner and every other handle. -/
theorem beaconPublish_origins {Reply : Type} (state : State n) (owner : Nat) (shell : BeaconShell)
    (kernel : StoredKernel n) (present : state.owners[owner]? = some (.established shell kernel))
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (same : result.1.2.kernel.origin = kernel.origin) :
    origins (beaconPublish state owner shell result).2 = origins state :=
  origins_owner_same state owner (.established shell kernel) (.established shell result.1.2.kernel) present same

/-- Complete Server publication preserves both the selected peer's origin and all other dynamic map entries. -/
theorem serverPublish_origins {Reply : Type} (tag : PqxdhDeploymentInterface.FrameTag)
    (state : State n) (server : Server n) (existing : state.server = some server)
    (keyId : Std.U64) (peer : Peer n) (present : server.peers keyId = some peer)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (same : result.1.2.kernel.origin = peer.kernel.origin) :
    origins (serverPublish tag state server keyId peer result).2 = origins state := by
  apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
  · funext target
    by_cases selected : target = keyId
    · subst target
      simp only [serverPublish, produce, Function.update_self, existing, Option.bind_some, present, same]
    · simp only [serverPublish, produce, Function.update_of_ne selected, existing, Option.bind_some]
  · rfl

/-- Ordinary Beacon commands preserve every computed origin and all one-use markers under any lookup policy. -/
theorem beaconStep_provenance {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State n)
    (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep policy setup codec owner query).run state)) :
    origins result.2 = origins state ∧ result.2.used = state.used := by
  cases selected : state.owners[owner]? with
  | none =>
      simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨rfl, rfl⟩
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported <;>
            subst result <;> exact ⟨rfl, rfl⟩
      | established shell kernel =>
          simp only [beaconStep, StateT.run, selected, support_map] at supported
          obtain ⟨inner, member, rfl⟩ := supported
          exact ⟨beaconPublish_origins state owner shell kernel selected inner
            (ownerRun_origin policy setup codec shell.identityKeyId query _ state inner member), rfl⟩

/-- Ordinary Server commands preserve every computed origin and one-use marker, including failed routes. -/
theorem serverStep_provenance {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State n)
    (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep policy setup codec route query).run state)) :
    origins result.2 = origins state ∧ result.2.used = state.used := by
  cases existing : state.server with
  | none =>
      cases query <;>
        simp only [serverStep, StateT.run, existing, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact ⟨rfl, rfl⟩
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [serverStep, StateT.run, existing, selected, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact ⟨rfl, rfl⟩
          | some peer =>
              simp only [serverStep, StateT.run, existing, selected, support_map] at supported
              obtain ⟨inner, member, rfl⟩ := supported
              exact ⟨serverPublish_origins _ state server existing keyId peer selected inner
                (ownerRun_origin policy setup codec server.sender (.inl plaintext) _ state inner member), rfl⟩
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [serverStep, StateT.run, existing, routed, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact ⟨by simp only [origins, existing, Option.bind_some], rfl⟩
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact ⟨by simp only [origins, existing, Option.bind_some], rfl⟩
              | some peer =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_map] at supported
                  obtain ⟨inner, member, rfl⟩ := supported
                  exact ⟨serverPublish_origins _ state server existing keyId peer selected inner
                    (ownerRun_origin policy setup codec server.sender (.inr raw) _ state inner member), rfl⟩

/-- Computed origins agree with actual-reply annotation for every world command, independently of lookup policy and reachability. -/
theorem handler_origins {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n)
    (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler policy setup codec route query).run state)) :
    origins result.2 = PqxdhRecordLiftOrigins.annotate query result.1 (origins state) := by
  cases query with
  | inl created =>
      exact initialize_origins created state result supported
  | inr outer =>
      cases outer with
      | inl effect =>
          exact effects_origins effect state result supported
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact (serverStep_provenance policy setup codec route (.inl send) state result supported).1
              | inr raw => exact (serverStep_provenance policy setup codec route (.inr raw) state result supported).1
          | inr ownerQuery =>
              obtain ⟨owner, query⟩ := ownerQuery
              cases query with
              | inl plaintext => exact (beaconStep_provenance policy setup codec owner (.inl plaintext) state result supported).1
              | inr raw => exact (beaconStep_provenance policy setup codec owner (.inr raw) state result supported).1

/-- Sampling or reusing a hidden seed never changes any slot/role admission marker. -/
theorem resolve_used (role : Role) (ref : KernelRef n) (state : State n)
    (result : StoredKernel n × State n) (supported : result ∈ support ((resolve role ref).run state)) :
    result.2.used = state.used := by
  cases ref with
  | known known =>
      simp only [resolve, StateT.run] at supported
      subst result
      rfl
  | hidden slot =>
      obtain ⟨seed, facts⟩ := resolve_hidden_facts role slot state result supported
      exact facts.2.2.2.1

/-- The actual Server admission branch both consumes the requested role and proves that role was previously unused. -/
theorem installServer_uses (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) :
    result.2.used = (if result.1 then markUsed state .server ref else state).used ∧
      (result.1 = true → Unused state .server ref) := by
  simp only [installServer, StateT.run] at supported
  cases found : state.server with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨rfl, Bool.noConfusion⟩
  | some server =>
      simp only [found] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        have same := resolve_used .server ref state inner member
        refine ⟨?_, fun _ => admitted.2⟩
        cases ref <;> simp only [markUsed, same, ↓reduceIte]
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨rfl, Bool.noConfusion⟩

/-- The actual Beacon admission branch consumes only its unused role and never resets any previous marker. -/
theorem installBeacon_uses (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) :
    result.2.used = (if result.1 then markUsed state .beacon ref else state).used ∧
      (result.1 = true → Unused state .beacon ref) := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have same := resolve_used .beacon ref state inner member
    refine ⟨?_, fun _ => admitted.2⟩
    cases ref <;> simp only [markUsed, same, ↓reduceIte]
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨rfl, Bool.noConfusion⟩

/-- The exact conditional admission update cannot clear any used slot/role pair. -/
theorem marker_update_persists (before after : State n) (role : Role) (ref : KernelRef n) (success : Bool)
    (same : after.used = (if success then markUsed before role ref else before).used) :
    PqxdhRecordLiftWorld.UsesPersist (world before) (world after) := by
  intro slot selected used
  change before.used slot selected = true at used
  change after.used slot selected = true
  rw [same]
  cases success with
  | false => exact used
  | true =>
      change (markUsed before role ref).used slot selected = true
      cases ref with
      | known kernel => exact used
      | hidden target =>
          simp only [markUsed, Function.update_apply]
          split_ifs <;> simp_all [Function.update_apply]

/-- Actual capability replies preserve used markers and supply the installation facts needed for origin uniqueness. -/
theorem capability_marker_facts (query : (CapabilitySpec n).Domain) (state : State n)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) :
    PqxdhRecordLiftWorld.UsesPersist (world state) (world result.2) ∧
      PqxdhRecordLiftOrigins.MarkedReply (.inr (.inl (.inr query))) result.1 (world result.2) ∧
      PqxdhRecordLiftOrigins.UnusedReply (.inr (.inl (.inr query))) result.1 (world state) := by
  cases query with
  | installServer keyId identity ref =>
      have facts := installServer_uses keyId identity ref state result supported
      refine ⟨marker_update_persists state result.2 .server ref result.1 facts.1, ?_, ?_⟩
      · cases ref with
        | known kernel => trivial
        | hidden slot =>
            intro success
            change result.2.used slot .server = true
            have exactUsed := congrArg (fun used => used slot .server) facts.1
            simpa only [success, ↓reduceIte, markUsed, Function.update_self] using exactUsed
      · cases ref with
        | known kernel => trivial
        | hidden slot => exact facts.2
  | installBeacon owner shell ref =>
      have facts := installBeacon_uses owner shell ref state result supported
      refine ⟨marker_update_persists state result.2 .beacon ref result.1 facts.1, ?_, ?_⟩
      · cases ref with
        | known kernel => trivial
        | hidden slot =>
            intro success
            change result.2.used slot .beacon = true
            have exactUsed := congrArg (fun used => used slot .beacon) facts.1
            simpa only [success, ↓reduceIte, markUsed, Function.update_self] using exactUsed
      · cases ref with
        | known kernel => trivial
        | hidden slot => exact facts.2
  | peerPresent keyId =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨fun _ _ used => used, trivial, trivial⟩
  | ownerPresent owner =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨fun _ _ used => used, trivial, trivial⟩
  | appendOwner sender pin phase =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨fun _ _ used => used, trivial, trivial⟩
  | hash bytes =>
      simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact ⟨fun _ _ used => used, trivial, trivial⟩
  | advanceOwner owner phase =>
      simp only [capability, StateT.run] at supported
      repeat' split at supported
      all_goals simp only [support_pure, Set.mem_singleton_iff] at supported
      all_goals subst result
      all_goals exact ⟨fun _ _ used => used, trivial, trivial⟩

/-- Uniform draws and charged capability dispatch preserve all admission facts. -/
theorem effects_marker_facts (query : (EnvEffects n).Domain) (state : State n)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) :
    PqxdhRecordLiftWorld.UsesPersist (world state) (world result.2) ∧
      PqxdhRecordLiftOrigins.MarkedReply (.inr (.inl query)) result.1 (world result.2) ∧
      PqxdhRecordLiftOrigins.UnusedReply (.inr (.inl query)) result.1 (world state) := by
  cases query with
  | inl coin =>
      simp only [effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact ⟨fun _ _ used => used, trivial, trivial⟩
  | inr request =>
      exact capability_marker_facts request (chargeEffect (.inr request) state) result supported

/-- Every actual world command preserves markers and proves its successful hidden-installation admission facts. -/
theorem handler_marker_facts {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler policy setup codec route query).run state)) :
    PqxdhRecordLiftWorld.UsesPersist (world state) (world result.2) ∧
      PqxdhRecordLiftOrigins.MarkedReply query result.1 (world result.2) ∧
      PqxdhRecordLiftOrigins.UnusedReply query result.1 (world state) := by
  rcases query with created | (effect | record)
  · simp only [handler, initializeServer, StateT.run] at supported
    cases found : state.server <;>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> exact ⟨fun _ _ used => used, trivial, trivial⟩
  · exact effects_marker_facts effect state result supported
  · rcases record with serverQuery | ⟨owner, ownerQuery⟩
    · cases serverQuery with
      | inl send =>
          have same := (serverStep_provenance policy setup codec route (.inl send) state result supported).2
          exact ⟨fun slot role used => by change result.2.used slot role = true; rw [same]; exact used, trivial, trivial⟩
      | inr raw =>
          have same := (serverStep_provenance policy setup codec route (.inr raw) state result supported).2
          exact ⟨fun slot role used => by change result.2.used slot role = true; rw [same]; exact used, trivial, trivial⟩
    · cases ownerQuery with
      | inl plaintext =>
          have same := (beaconStep_provenance policy setup codec owner (.inl plaintext) state result supported).2
          exact ⟨fun slot role used => by change result.2.used slot role = true; rw [same]; exact used, trivial, trivial⟩
      | inr raw =>
          have same := (beaconStep_provenance policy setup codec owner (.inr raw) state result supported).2
          exact ⟨fun slot role used => by change result.2.used slot role = true; rw [same]; exact used, trivial, trivial⟩

/-- Every stored hidden origin has consumed its physical role, and each role has at most one handle for that slot. Only structural origin tags occur in this predicate. -/
def Provenance (state : State n) : Prop :=
  PqxdhRecordLiftOrigins.Marked (world state, origins state) ∧
    PqxdhRecordLiftOrigins.Unique (origins state)

/-- Origin uniqueness is preserved by the actual handler, using its proved annotation and admission equations. -/
theorem handler_provenance {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n) (before : Provenance state)
    (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler policy setup codec route query).run state)) :
    Provenance result.2 := by
  have facts := handler_marker_facts policy setup codec route query state result supported
  change PqxdhRecordLiftOrigins.Marked (world result.2, origins result.2) ∧
    PqxdhRecordLiftOrigins.Unique (origins result.2)
  rw [handler_origins policy setup codec route query state result supported]
  exact ⟨PqxdhRecordLiftOrigins.annotate_marked query result.1 (world state) (world result.2)
      (origins state) before.1 facts.1 facts.2.1,
    PqxdhRecordLiftOrigins.annotate_unique query result.1 (world state) (origins state) before.1 before.2 facts.2.2⟩

/-- The actual empty compiler world starts with no hidden origins and no consumed roles. -/
theorem initial_provenance : Provenance (initial : State n) :=
  PqxdhRecordLiftOrigins.initial_facts

/-- Every supported adaptive schedule preserves exact computed-origin uniqueness and consumed-role provenance. -/
theorem schedule_provenance {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : State n) (provenance : Provenance state)
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler policy setup codec route) client).run state)) :
    Provenance result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact provenance
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨inner, member, continued⟩ := supported
      exact ih inner.1 inner.2 (handler_provenance policy setup codec route query state provenance inner member) result continued

/-- The actual frozen program derives unique hidden origins from its empty initial world, without a Frame or reachable-prefix assumption. -/
theorem run_provenance {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run policy setup codec route env serverKid bounds mode adversary)) :
    Provenance result.2 :=
  schedule_provenance policy setup codec route (program env setup.source.crypto codec serverKid bounds mode adversary)
    initial initial_provenance result supported

/-- A structural coordinate held for sending by one actual physical peer or established owner. -/
def HiddenSender (state : State n) : Std.U64 ⊕ Nat → Label n → Prop
  | .inl keyId, coordinate => ∃ server peer slot kernel,
      state.server = some server ∧ server.peers keyId = some peer ∧
        peer.kernel = .hidden slot kernel ∧ kernel.send_chain = coordinate
  | .inr owner, coordinate => ∃ shell slot kernel,
      state.owners[owner]? = some (.established shell (.hidden slot kernel)) ∧ kernel.send_chain = coordinate

/-- A live hidden send coordinate supplies its actual origin and the direction fixed by its physical role. -/
theorem hiddenSender_facts (state : State n) (roles : Roles state) (handle : Std.U64 ⊕ Nat)
    (coordinate : Label n) (sending : HiddenSender state handle coordinate) :
    match handle with
    | .inl keyId => (origins state).peers keyId = some coordinate.slot ∧ coordinate.direction = false
    | .inr owner => (origins state).owners owner = some coordinate.slot ∧ coordinate.direction = true := by
  cases handle with
  | inl keyId =>
      obtain ⟨server, peer, slot, kernel, existing, present, stored, rfl⟩ := sending
      have oriented := roles.1 server existing keyId peer present
      rw [stored] at oriented
      refine ⟨?_, oriented.2.2.1⟩
      simp only [origins, existing, Option.bind_some, present, stored, StoredKernel.origin, oriented.2.1.1]
  | inr owner =>
      obtain ⟨shell, slot, kernel, present, rfl⟩ := sending
      have oriented : Oriented .beacon (.hidden slot kernel) := roles.2 _ (List.mem_of_getElem? present)
      refine ⟨?_, oriented.2.2.1⟩
      simp only [origins, present, Option.bind_some, Phase.origin, StoredKernel.origin, oriented.2.1.1]

/-- One structural send coordinate belongs to at most one live physical handle, without comparing any key bytes. -/
theorem hiddenSender_unique (state : State n) (roles : Roles state) (provenance : Provenance state)
    (left right : Std.U64 ⊕ Nat) (coordinate : Label n)
    (sendLeft : HiddenSender state left coordinate) (sendRight : HiddenSender state right coordinate) :
    left = right := by
  have first := hiddenSender_facts state roles left coordinate sendLeft
  have second := hiddenSender_facts state roles right coordinate sendRight
  cases left with
  | inl keyLeft =>
      cases right with
      | inl keyRight => exact congrArg Sum.inl (provenance.2.1 keyLeft keyRight coordinate.slot first.1 second.1)
      | inr ownerRight => exact Bool.noConfusion (first.2.symm.trans second.2)
  | inr ownerLeft =>
      cases right with
      | inl keyRight => exact Bool.noConfusion (first.2.symm.trans second.2)
      | inr ownerRight => exact congrArg Sum.inr (provenance.2.2 ownerLeft ownerRight coordinate.slot first.1 second.1)

/-- Actual adaptive execution derives one live sender per structural coordinate from initial storage and admission guards. -/
theorem initial_schedule_sender_unique {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler policy setup codec route) client).run initial))
    (left right : Std.U64 ⊕ Nat) (coordinate : Label n)
    (sendLeft : HiddenSender result.2 left coordinate) (sendRight : HiddenSender result.2 right coordinate) :
    left = right :=
  hiddenSender_unique result.2
    (schedule_roles policy setup codec route client initial initial_roles result supported)
    (schedule_provenance policy setup codec route client initial initial_provenance result supported)
    left right coordinate sendLeft sendRight

/-- An admitted source send installs exactly its successor kernel before accepting any optional writer reply; the source counter increments without wrapping. -/
theorem send_requested_progress {P Context Output : Type}
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (sealing : PqxdhRecordLiftChainCompiler.Seal Context Output P)
    (entry : LabeledKernel n) (context : Context)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) Context)
    (admitted : RawCtxChainSend.normalBegin entry context = .requested pending)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (result : (LabeledKernel n × Option Output) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((PqxdhRecordLiftChainCompiler.send seeds lookup sealing
      (RawCtxChainSend.normalBegin entry context)).run state)) :
    result.1.1 = { entry with control := pending.committed_control, send_chain := PqxdhRecordLiftChainState.advance entry.send_chain 1 } ∧
      result.1.1.control.send_sequence.val = entry.control.send_sequence.val + 1 := by
  simp only [admitted, PqxdhRecordLiftChainCompiler.send, StateT.run] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨looked, lookupSupported, continued⟩ := supported
  simp only [bind_pure_comp, support_map] at continued
  obtain ⟨sealed, sealSupported, rfl⟩ := continued
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked entry context
  rw [admitted] at tracked
  have kernel := PqxdhRecordLiftChainState.send_ready_kernel entry context pending pending.request tracked
  refine ⟨kernel, ?_⟩
  rw [kernel]
  exact tracked.2.2.2.1

/-- Every source send either returns the entire exhausted entry unchanged or advances exactly once while retaining the complete receive side. -/
theorem send_outcome {P Context Output : Type}
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (sealing : PqxdhRecordLiftChainCompiler.Seal Context Output P)
    (entry : LabeledKernel n) (context : Context)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (result : (LabeledKernel n × Option Output) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((PqxdhRecordLiftChainCompiler.send seeds lookup sealing
      (RawCtxChainSend.normalBegin entry context)).run state)) :
    result = ((entry, none), state) ∨
      (result.1.1.send_chain = PqxdhRecordLiftChainState.advance entry.send_chain 1 ∧
        result.1.1.control.send_sequence.val = entry.control.send_sequence.val + 1 ∧
        result.1.1.receive_chain = entry.receive_chain ∧ result.1.1.receive_slots = entry.receive_slots ∧
        result.1.1.control.receive_sequence = entry.control.receive_sequence ∧
        result.1.1.control.receive_cache = entry.control.receive_cache) := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked entry context
  cases admitted : RawCtxChainSend.normalBegin entry context with
  | exhausted original prior =>
      rw [admitted] at tracked
      simp only [admitted, PqxdhRecordLiftChainCompiler.send, StateT.run,
        support_pure, Set.mem_singleton_iff] at supported
      exact Or.inl (supported.trans (congrArg (fun kernel => ((kernel, none), state)) tracked.1))
  | requested pending =>
      have progress := send_requested_progress seeds lookup sealing entry context pending admitted state result supported
      rw [admitted] at tracked
      apply Or.inr
      rw [progress.1]
      exact ⟨rfl, tracked.2.2.2.1, rfl, rfl, tracked.2.2.2.2.1, tracked.2.2.2.2.2⟩

/-- At the source U64 maximum, send returns the entire state unchanged and invokes neither lookup nor sealing. -/
theorem send_max {P Context Output : Type}
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (sealing : PqxdhRecordLiftChainCompiler.Seal Context Output P)
    (entry : LabeledKernel n) (context : Context)
    (top : entry.control.send_sequence = core.num.U64.MAX)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) :
    (PqxdhRecordLiftChainCompiler.send seeds lookup sealing
      (RawCtxChainSend.normalBegin entry context)).run state = pure ((entry, none), state) := by
  have actual := RawCtxChainSend.normalBegin_exact entry context
  simp only [RawCtxChainSend.beginSend, control.advance_send_max entry.control top, bind_tc_ok] at actual
  rw [← RustM.ok.inj actual]
  rfl

/-- Every hidden native send retains its installation tag, never decreases the structural send position, and preserves the complete receive side. -/
theorem kernelSend_progress {P : Type}
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.SendNative P) (slot : Slot n) (entry : LabeledKernel n)
    (context : RawCtxSourceSend.SealContext) (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelSend seeds lookup native (.hidden slot entry) context).run state)) :
    ∃ after, result.1.1 = .hidden slot after ∧ entry.send_chain.position ≤ after.send_chain.position ∧
      after.receive_chain = entry.receive_chain ∧ after.receive_slots = entry.receive_slots := by
  simp only [kernelSend, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  rcases send_outcome seeds lookup (PqxdhRecordLiftNativeAdapters.sendSeal native) entry context state inner member with unchanged | advanced
  · subst inner
    exact ⟨entry, rfl, le_rfl, rfl, rfl⟩
  · refine ⟨inner.1.1, rfl, ?_, advanced.2.2.1, advanced.2.2.2.1⟩
    rw [advanced.1]
    exact Nat.le_add_right _ _

/-- Every hidden receive, including failed opening and rollback, preserves the entire send coordinate of its actual certified source kernel. -/
theorem kernelReceive_send {P : Type}
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative P) (slot : Slot n) (entry : LabeledKernel n)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (certified : PqxdhRecordLiftChainCoordinates.Certified entry)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelReceive seeds lookup native (.hidden slot entry) target context).run state)) :
    ∃ after, result.1.1 = .hidden slot after ∧ after.send_chain = entry.send_chain := by
  simp only [kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  refine ⟨inner.1.1, rfl, ?_⟩
  exact (PqxdhRecordLiftChainCoordinates.receive_origins entry inner.1.1
    (PqxdhRecordLiftChainCoordinates.admitted_receive_coordinates seeds lookup
      (PqxdhRecordLiftNativeAdapters.receiveOpen native) entry context target certified.1.capacity state inner member)).1

/-- Existing hidden storage keeps its actual installation tag and never moves its send position backwards. -/
def StoredAhead (before after : StoredKernel n) : Prop :=
  ∀ slot kernel, before = .hidden slot kernel → ∃ next,
    after = .hidden slot next ∧ kernel.send_chain.position ≤ next.send_chain.position

theorem storedAhead_refl (kernel : StoredKernel n) : StoredAhead kernel kernel := by
  intro slot entry same
  exact ⟨entry, same, le_rfl⟩

theorem storedAhead_trans (first middle last : StoredKernel n)
    (left : StoredAhead first middle) (right : StoredAhead middle last) : StoredAhead first last := by
  intro slot entry same
  obtain ⟨next, found, progress⟩ := left slot entry same
  obtain ⟨final, present, advanced⟩ := right slot next found
  exact ⟨final, present, progress.trans advanced⟩

/-- Native send progress is independent of the physical role and of every private lookup or writer response. -/
theorem kernelSend_ahead {P : Type}
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.SendNative P) (stored : StoredKernel n)
    (context : RawCtxSourceSend.SealContext) (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelSend seeds lookup native stored context).run state)) :
    StoredAhead stored result.1.1 := by
  intro slot entry same
  subst stored
  obtain ⟨next, found, progress, _⟩ := kernelSend_progress seeds lookup native slot entry context state result supported
  exact ⟨next, found, progress⟩

/-- Receive progress uses only the actual source certificate already implied by physical role orientation. -/
theorem kernelReceive_ahead {P : Type} (role : Role)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative P) (stored : StoredKernel n)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (oriented : Oriented role stored)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelReceive seeds lookup native stored target context).run state)) :
    StoredAhead stored result.1.1 := by
  intro slot entry same
  subst stored
  obtain ⟨next, found, unchanged⟩ := kernelReceive_send seeds lookup native slot entry target context state oriented.1 result supported
  exact ⟨next, found, by rw [unchanged]⟩

/-- Both selected-owner branches preserve the installed hidden sender and its nondecreasing position. -/
theorem ownerStep_ahead {P : Type} (role : Role)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (oriented : Oriented role owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((ownerStep seeds lookup native sender decode query owner).run state)) :
    StoredAhead owner.kernel result.1.2.kernel := by
  cases query with
  | inl plaintext =>
      simp only [ownerStep, ownerSend, StateT.run] at supported
      split_ifs at supported with empty
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        exact supported.symm ▸ storedAhead_refl owner.kernel
      · simp only [bind_pure_comp, support_map] at supported
        exact supported.elim fun inner ⟨member, equal⟩ => equal ▸
          kernelSend_ahead seeds lookup (sendNative native) owner.kernel _ state inner member
  | inr raw =>
      simp only [ownerStep, ownerReceive, StateT.run] at supported
      repeat' split at supported
      case h_2.isTrue =>
        simp only [bind_pure_comp, support_map] at supported
        exact supported.elim fun inner ⟨member, equal⟩ => equal ▸
          kernelReceive_ahead role seeds lookup (receiveNative native) owner.kernel _ _ state oriented inner member
      all_goals simp only [support_pure, Set.mem_singleton_iff] at supported
      all_goals exact supported.symm ▸ storedAhead_refl owner.kernel

/-- Native logging retains the selected hidden sender's monotone position. -/
theorem ownerRun_ahead {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (role : Role) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (oriented : Oriented role owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (supported : result ∈ support (ownerRun policy setup codec sender query owner state)) :
    StoredAhead owner.kernel result.1.2.kernel :=
  ownerStep_ahead role (cachedSeeds state) _ _ sender codec.frameRead query owner
    (state.chain, (state.primitive, [])) oriented result supported

/-- Every existing physical record remains at its handle, with a nondecreasing hidden send position. -/
def Forward (before after : State n) : Prop :=
  (∀ server, before.server = some server → ∀ keyId peer, server.peers keyId = some peer →
    ∃ nextServer nextPeer, after.server = some nextServer ∧ nextServer.peers keyId = some nextPeer ∧
      StoredAhead peer.kernel nextPeer.kernel) ∧
  (∀ (owner : Nat) (shell : BeaconShell) (kernel : StoredKernel n), before.owners[owner]? = some (.established shell kernel) →
    ∃ nextShell nextKernel, after.owners[owner]? = some (.established nextShell nextKernel) ∧
      StoredAhead kernel nextKernel)

theorem forward_refl (state : State n) : Forward state state := by
  exact ⟨fun server existing keyId peer present => ⟨server, peer, existing, present, storedAhead_refl _⟩,
    fun owner shell kernel present => ⟨shell, kernel, present, storedAhead_refl _⟩⟩

theorem forward_trans (first middle last : State n) (left : Forward first middle)
    (right : Forward middle last) : Forward first last := by
  constructor
  · intro server existing keyId peer present
    obtain ⟨nextServer, nextPeer, middleServer, middlePeer, progress⟩ := left.1 server existing keyId peer present
    obtain ⟨finalServer, finalPeer, finalServerFound, finalPeerFound, advanced⟩ := right.1 nextServer middleServer keyId nextPeer middlePeer
    exact ⟨finalServer, finalPeer, finalServerFound, finalPeerFound, storedAhead_trans _ _ _ progress advanced⟩
  · intro owner shell kernel present
    obtain ⟨nextShell, nextKernel, found, progress⟩ := left.2 owner shell kernel present
    obtain ⟨finalShell, finalKernel, finalFound, advanced⟩ := right.2 owner nextShell nextKernel found
    exact ⟨finalShell, finalKernel, finalFound, storedAhead_trans _ _ _ progress advanced⟩

/-- Changes to private effects, seed/table caches and public logs cannot move an actual record handle. -/
theorem forward_frame (before after : State n) (server : after.server = before.server)
    (owners : after.owners = before.owners) : Forward before after := by
  constructor
  · intro old existing keyId peer present
    exact ⟨old, peer, server.trans existing, present, storedAhead_refl _⟩
  · intro owner shell kernel present
    exact ⟨shell, kernel, by rw [owners]; exact present, storedAhead_refl _⟩

/-- Replacing a single Server entry retains all old handles when its actual old entry advances. -/
theorem forward_server_store (state : State n) (server : Server n)
    (existing : state.server = some server) (keyId : Std.U64) (next : Peer n)
    (progress : ∀ peer, server.peers keyId = some peer → StoredAhead peer.kernel next.kernel)
    (rawAttempts : Nat) :
    Forward state { state with server := some { server with
      peers := Function.update server.peers keyId (some next), rawAttempts := rawAttempts } } := by
  constructor
  · intro old found target peer present
    have same := Option.some.inj (found.symm.trans existing)
    subst old
    refine ⟨{ server with peers := Function.update server.peers keyId (some next), rawAttempts := rawAttempts }, ?_⟩
    by_cases selected : target = keyId
    · subst target
      exact ⟨next, rfl, Function.update_self _ _ _, progress peer present⟩
    · exact ⟨peer, rfl, (Function.update_of_ne selected _ _).trans present, storedAhead_refl _⟩
  · intro owner shell kernel present
    exact ⟨shell, kernel, present, storedAhead_refl _⟩

/-- Replacing one owner phase retains all established handles when an old selected kernel advances. -/
theorem forward_owner_store (state : State n) (owner : Nat) (phase : Phase n)
    (progress : ∀ shell kernel, state.owners[owner]? = some (.established shell kernel) →
      ∃ nextShell nextKernel, phase = .established nextShell nextKernel ∧ StoredAhead kernel nextKernel) :
    Forward state { state with owners := state.owners.set owner phase } := by
  constructor
  · intro server existing keyId peer present
    exact ⟨server, peer, existing, present, storedAhead_refl _⟩
  · intro target shell kernel present
    by_cases same : target = owner
    · subst target
      obtain ⟨nextShell, nextKernel, changed, advanced⟩ := progress shell kernel present
      refine ⟨nextShell, nextKernel, ?_, advanced⟩
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp present).1, changed]
    · exact ⟨shell, kernel, (List.getElem?_set_ne (Ne.symm same)).trans present, storedAhead_refl _⟩

/-- Reinstalling the complete selected Server kernel retains every physical record handle and its send progress. -/
theorem serverPublish_forward {Reply : Type} (tag : PqxdhDeploymentInterface.FrameTag)
    (state : State n) (server : Server n) (existing : state.server = some server)
    (keyId : Std.U64) (peer : Peer n) (selected : server.peers keyId = some peer)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (progress : StoredAhead peer.kernel result.1.2.kernel) :
    Forward state (serverPublish tag state server keyId peer result).2 := by
  apply forward_server_store state server existing keyId { peer with kernel := result.1.2.kernel } _ result.1.2.rawAttempts
  intro previous present
  have same := Option.some.inj (present.symm.trans selected)
  subst previous
  exact progress

/-- Reinstalling one established Beacon retains all old indices and the selected kernel's send progress. -/
theorem beaconPublish_forward {Reply : Type} (state : State n) (owner : Nat) (shell : BeaconShell)
    (kernel : StoredKernel n) (selected : state.owners[owner]? = some (.established shell kernel))
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (progress : StoredAhead kernel result.1.2.kernel) :
    Forward state (beaconPublish state owner shell result).2 := by
  apply forward_owner_store state owner (.established shell result.1.2.kernel)
  intro oldShell oldKernel present
  have same := (Phase.established.inj (Option.some.inj (present.symm.trans selected))).2
  subst oldKernel
  exact ⟨shell, result.1.2.kernel, rfl, progress⟩

/-- Raw-attempt accounting alone leaves every Server peer and Beacon record unchanged. -/
theorem forward_serverRaw (state : State n) (server : Server n)
    (existing : state.server = some server) (rawAttempts : Nat) :
    Forward state { state with server := some { server with rawAttempts := rawAttempts } } := by
  constructor
  · intro old found keyId peer present
    have same := Option.some.inj (found.symm.trans existing)
    subst old
    exact ⟨{ server with rawAttempts := rawAttempts }, peer, rfl, present, storedAhead_refl _⟩
  · intro owner shell kernel present
    exact ⟨shell, kernel, present, storedAhead_refl _⟩

/-- Every selected Beacon request preserves all existing handles and nondecreasing send positions. -/
theorem beaconStep_forward {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State n) (roles : Roles state)
    (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep policy setup codec owner query).run state)) :
    Forward state result.2 := by
  cases selected : state.owners[owner]? with
  | none =>
      simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact forward_refl state
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported <;>
            subst result <;> exact forward_refl state
      | established shell kernel =>
          simp only [beaconStep, StateT.run, selected, support_map] at supported
          obtain ⟨inner, member, rfl⟩ := supported
          have oriented : Oriented .beacon kernel := roles.2 _ (List.mem_of_getElem? selected)
          exact beaconPublish_forward state owner shell kernel selected inner
            (ownerRun_ahead policy .beacon setup codec shell.identityKeyId query _ state oriented inner member)

/-- Header failure, absent peers and complete Server callbacks all preserve prior physical senders. -/
theorem serverStep_forward {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State n) (roles : Roles state)
    (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep policy setup codec route query).run state)) :
    Forward state result.2 := by
  cases existing : state.server with
  | none =>
      cases query <;>
        simp only [serverStep, StateT.run, existing, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact forward_refl state
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [serverStep, StateT.run, existing, selected, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact forward_refl state
          | some peer =>
              simp only [serverStep, StateT.run, existing, selected, support_map] at supported
              obtain ⟨inner, member, rfl⟩ := supported
              have oriented := roles.1 server existing keyId peer selected
              exact serverPublish_forward _ state server existing keyId peer selected inner
                (ownerRun_ahead policy .server setup codec server.sender (.inl plaintext) _ state oriented inner member)
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [serverStep, StateT.run, existing, routed, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact forward_serverRaw state server existing (server.rawAttempts + 1)
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact forward_serverRaw state server existing (server.rawAttempts + 1)
              | some peer =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_map] at supported
                  obtain ⟨inner, member, rfl⟩ := supported
                  have oriented := roles.1 server existing keyId peer selected
                  exact serverPublish_forward _ state server existing keyId peer selected inner
                    (ownerRun_ahead policy .server setup codec server.sender (.inr raw) _ state oriented inner member)

/-- Installation resolution changes no preexisting physical record, even when it samples a new seed. -/
theorem resolve_forward (role : Role) (ref : KernelRef n) (state : State n)
    (result : StoredKernel n × State n) (supported : result ∈ support ((resolve role ref).run state)) :
    Forward state result.2 :=
  forward_frame state result.2 (resolve_fields role ref state result supported).1
    (resolve_fields role ref state result supported).2.1

/-- One-use admission marks cannot remove or rewind an existing record. -/
theorem markUsed_forward (state : State n) (role : Role) (ref : KernelRef n) :
    Forward state (markUsed state role ref) := by
  cases ref <;> exact forward_refl state

/-- Actual Server installation admits only an empty target, so even a successful hidden install cannot reset an old sender. -/
theorem installServer_forward (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) : Forward state result.2 := by
  simp only [installServer, StateT.run] at supported
  cases found : state.server with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact forward_refl state
  | some server =>
      simp only [found] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        have same : (markUsed inner.2 .server ref).server = some server := by
          cases ref <;> exact (resolve_fields .server _ state inner member).1.trans found
        refine forward_trans state (markUsed inner.2 .server ref) _
          (forward_trans state inner.2 _ (resolve_forward .server ref state inner member)
            (markUsed_forward inner.2 .server ref)) ?_
        apply forward_server_store _ server same keyId ⟨identity, inner.1⟩ _ server.rawAttempts
        intro peer present
        have impossible := present.symm.trans admitted.1
        cases impossible
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact forward_refl state

/-- Actual Beacon installation requires an inactive init-sent target and cannot reset an established record. -/
theorem installBeacon_forward (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) : Forward state result.2 := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have owners : (markUsed inner.2 .beacon ref).owners = state.owners := by
      cases ref <;> exact (resolve_fields .beacon _ state inner member).2.1
    refine forward_trans state (markUsed inner.2 .beacon ref) _
      (forward_trans state inner.2 _ (resolve_forward .beacon ref state inner member)
        (markUsed_forward inner.2 .beacon ref)) ?_
    rw [← owners]
    apply forward_owner_store
    intro oldShell oldKernel present
    rw [owners] at present
    have impossible := Option.some.inj (present.symm.trans admitted.1)
    cases impossible
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact forward_refl state

/-- Server construction is a one-time absent-store update; duplicate initialization cannot reset a sender. -/
theorem initialize_forward (created : PqxdhLiveServerConstruction.Created Unit) (state : State n)
    (result : Unit × State n) (supported : result ∈ support ((initializeServer created).run state)) :
    Forward state result.2 := by
  simp only [initializeServer, StateT.run] at supported
  cases found : state.server with
  | some server =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact forward_refl state
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      constructor
      · intro server existing
        have impossible := found.symm.trans existing
        cases impossible
      · intro owner shell kernel present
        exact ⟨shell, kernel, present, storedAhead_refl _⟩

/-- Appending registration state leaves all existing owner indices intact. -/
theorem forward_append (state : State n) (phase : InactivePhase) :
    Forward state { state with owners := state.owners ++ [.inactive phase] } := by
  constructor
  · exact (forward_refl state).1
  · intro owner shell kernel present
    exact ⟨shell, kernel, (List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1).trans present,
      storedAhead_refl _⟩

/-- Every administrative operation preserves established physical records; permitted phase changes apply only to inactive owners. -/
theorem capability_forward (query : (CapabilitySpec n).Domain) (state : State n)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) : Forward state result.2 := by
  cases query with
  | installServer keyId identity ref => exact installServer_forward keyId identity ref state result supported
  | installBeacon owner shell ref => exact installBeacon_forward owner shell ref state result supported
  | peerPresent keyId =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact forward_refl state
  | ownerPresent owner =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact forward_refl state
  | appendOwner sender pin phase =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact forward_append state phase
  | hash bytes =>
      simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact forward_frame state _ rfl rfl
  | advanceOwner owner phase =>
      simp only [capability, StateT.run] at supported
      cases selected : state.owners[owner]? with
      | none =>
          simp only [selected, support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact forward_refl state
      | some current =>
          cases current with
          | established shell kernel =>
              simp only [selected, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact forward_refl state
          | inactive before =>
              simp only [selected] at supported
              split_ifs at supported with allowed
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst result
                apply forward_owner_store state owner (.inactive phase)
                intro oldShell oldKernel present
                rw [selected] at present
                cases present
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst result
                exact forward_refl state

/-- Charging and running any environment effect preserves established records. -/
theorem effects_forward (query : (EnvEffects n).Domain) (state : State n)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) : Forward state result.2 := by
  cases query with
  | inl coin =>
      simp only [effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact forward_frame state _ rfl rfl
  | inr request => exact capability_forward request (chargeEffect (.inr request) state) result supported

/-- An actual World request cannot remove or rewind a previously established hidden sender. -/
theorem handler_forward {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n) (roles : Roles state)
    (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler policy setup codec route query).run state)) :
    Forward state result.2 := by
  cases query with
  | inl created => exact initialize_forward created state result supported
  | inr outer =>
      cases outer with
      | inl effect => exact effects_forward effect state result supported
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact serverStep_forward policy setup codec route (.inl send) state roles result supported
              | inr raw => exact serverStep_forward policy setup codec route (.inr raw) state roles result supported
          | inr ownerQuery =>
              obtain ⟨owner, query⟩ := ownerQuery
              cases query with
              | inl plaintext => exact beaconStep_forward policy setup codec owner (.inl plaintext) state roles result supported
              | inr raw => exact beaconStep_forward policy setup codec owner (.inr raw) state roles result supported

/-- Arbitrary adaptive continuation preserves old physical handles and their monotone send positions. -/
theorem schedule_forward {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : State n) (roles : Roles state)
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler policy setup codec route) client).run state)) :
    Forward state result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact forward_refl state
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨inner, member, continued⟩ := supported
      exact forward_trans state inner.2 result.2
        (handler_forward policy setup codec route query state roles inner member)
        (ih inner.1 inner.2 (handler_roles policy setup codec route query state roles inner member) result continued)

/-- Structural slot and direction already determine the physical sender handle; equality of chain or material bytes is irrelevant. -/
theorem hiddenSender_origin_unique (state : State n) (roles : Roles state) (provenance : Provenance state)
    (left right : Std.U64 ⊕ Nat) (first second : Label n)
    (sendLeft : HiddenSender state left first) (sendRight : HiddenSender state right second)
    (slot : first.slot = second.slot) (direction : first.direction = second.direction) : left = right := by
  have a := hiddenSender_facts state roles left first sendLeft
  have b := hiddenSender_facts state roles right second sendRight
  cases left with
  | inl keyLeft =>
      cases right with
      | inl keyRight =>
          exact congrArg Sum.inl (provenance.2.1 keyLeft keyRight second.slot (a.1.trans (congrArg some slot)) b.1)
      | inr ownerRight => exact Bool.noConfusion (a.2.symm.trans (direction.trans b.2))
  | inr ownerLeft =>
      cases right with
      | inl keyRight => exact Bool.noConfusion (a.2.symm.trans (direction.trans b.2))
      | inr ownerRight =>
          exact congrArg Sum.inr (provenance.2.2 ownerLeft ownerRight second.slot (a.1.trans (congrArg some slot)) b.1)

/-- A fixed physical handle has one literal current send coordinate. -/
theorem hiddenSender_functional (state : State n) (handle : Std.U64 ⊕ Nat) (left right : Label n)
    (first : HiddenSender state handle left) (second : HiddenSender state handle right) : left = right := by
  cases handle with
  | inl keyId =>
      obtain ⟨server, peer, slot, kernel, existing, present, stored, rfl⟩ := first
      obtain ⟨nextServer, nextPeer, nextSlot, nextKernel, nextExisting, nextPresent, nextStored, rfl⟩ := second
      have servers := Option.some.inj (existing.symm.trans nextExisting)
      subst nextServer
      have peers := Option.some.inj (present.symm.trans nextPresent)
      subst nextPeer
      have kernels := (StoredKernel.hidden.inj (stored.symm.trans nextStored)).2
      subst nextKernel
      rfl
  | inr owner =>
      obtain ⟨shell, slot, kernel, present, rfl⟩ := first
      obtain ⟨nextShell, nextSlot, nextKernel, nextPresent, rfl⟩ := second
      have stored := (Phase.established.inj (Option.some.inj (present.symm.trans nextPresent))).2
      have kernels := (StoredKernel.hidden.inj stored).2
      subst nextKernel
      rfl

/-- Actual record persistence supplies the same physical sender at a later position, retaining its structural slot and direction. -/
theorem hiddenSender_forward (before after : State n) (prior : Roles before) (roles : Roles after)
    (forward : Forward before after) (handle : Std.U64 ⊕ Nat) (coordinate : Label n)
    (sending : HiddenSender before handle coordinate) :
    ∃ next, HiddenSender after handle next ∧ next.slot = coordinate.slot ∧
      next.direction = coordinate.direction ∧ coordinate.position ≤ next.position := by
  cases handle with
  | inl keyId =>
      obtain ⟨server, peer, slot, kernel, existing, present, stored, rfl⟩ := sending
      obtain ⟨nextServer, nextPeer, nextExisting, nextPresent, ahead⟩ := forward.1 server existing keyId peer present
      obtain ⟨next, nextStored, progress⟩ := ahead slot kernel stored
      have old := prior.1 server existing keyId peer present
      have new := roles.1 nextServer nextExisting keyId nextPeer nextPresent
      rw [stored] at old
      rw [nextStored] at new
      exact ⟨next.send_chain, ⟨nextServer, nextPeer, slot, next, nextExisting, nextPresent, nextStored, rfl⟩,
        new.2.1.1.trans old.2.1.1.symm, new.2.2.1.trans old.2.2.1.symm, progress⟩
  | inr owner =>
      obtain ⟨shell, slot, kernel, present, rfl⟩ := sending
      obtain ⟨nextShell, nextKernel, nextPresent, ahead⟩ := forward.2 owner shell (.hidden slot kernel) present
      obtain ⟨next, nextStored, progress⟩ := ahead slot kernel rfl
      have old : Oriented .beacon (.hidden slot kernel) := prior.2 _ (List.mem_of_getElem? present)
      have new : Oriented .beacon nextKernel := roles.2 _ (List.mem_of_getElem? nextPresent)
      rw [nextStored] at new
      exact ⟨next.send_chain, ⟨nextShell, slot, next, nextStored ▸ nextPresent, rfl⟩,
        new.2.1.1.trans old.2.1.1.symm, new.2.2.1.trans old.2.2.1.symm, progress⟩

/-- Each past attempted coordinate lies strictly behind an actual current physical sender. This invariant alone makes no claim that an arbitrary list is an execution trace. -/
def Past (state : State n) (attempts : List (Label n)) : Prop :=
  ∀ coordinate ∈ attempts, ∃ handle current, HiddenSender state handle current ∧
    current.slot = coordinate.slot ∧ current.direction = coordinate.direction ∧
      coordinate.position < current.position

/-- Established sender persistence keeps all previously attempted coordinates strictly behind their same physical record. -/
theorem past_forward (before after : State n) (prior : Roles before) (roles : Roles after)
    (forward : Forward before after) (attempts : List (Label n)) (past : Past before attempts) :
    Past after attempts := by
  intro coordinate member
  obtain ⟨handle, current, sending, slot, direction, earlier⟩ := past coordinate member
  obtain ⟨next, sent, sameSlot, sameDirection, progress⟩ := hiddenSender_forward before after prior roles forward handle current sending
  exact ⟨handle, next, sent, sameSlot.trans slot, sameDirection.trans direction, earlier.trans_le progress⟩

/-- A current physical send coordinate cannot equal a past attempt once actual origin uniqueness and strict history progress hold. -/
theorem past_not_current (state : State n) (roles : Roles state) (provenance : Provenance state)
    (attempts : List (Label n)) (past : Past state attempts) (handle : Std.U64 ⊕ Nat)
    (coordinate : Label n) (sending : HiddenSender state handle coordinate) : coordinate ∉ attempts := by
  intro member
  obtain ⟨prior, current, sent, slot, direction, earlier⟩ := past coordinate member
  have same := hiddenSender_origin_unique state roles provenance prior handle current coordinate sent sending slot direction
  subst prior
  have coordinates := hiddenSender_functional state handle current coordinate sent sending
  rw [coordinates] at earlier
  exact (Nat.lt_irrefl _) earlier

/-- The private attempt log records the actual labeled sealing request before its optional writer response. -/
def sealingCoordinates : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain → List (Label n)
  | .sealing pending => [pending.material]
  | _ => []

/-- Private trace instrumentation preserves the complete service state and every literal response, including writer failure. -/
def recordService {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp)) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (P × List (Label n)) ProbComp) :=
  fun query state => do
    let attempts := state.2 ++ sealingCoordinates query
    let result ← (service query).run state.1
    pure (result.1, (result.2, attempts))

/-- Dropping only the private attempt list recovers the exact original service call. -/
theorem recordService_erasure {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (state : P × List (Label n)) :
    Prod.map id Prod.fst <$> (recordService service query).run state = (service query).run state.1 := by
  simp [recordService, StateT.run, Functor.map_map]

/-- The exact arbitrary private-service continuation retains its complete reply/control/environment result when only instrumentation is erased. -/
theorem recordService_complete {P Result : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : P × List (Label n)) :
    Prod.map id Prod.fst <$> (simulateQ (recordService service) client).run state =
      (simulateQ service client).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (recordService_erasure service) client state

/-- Complete actual protocol execution with a private history, retaining its original complete control and private state. -/
noncomputable def tracedSchedule {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : State n) (attempts : List (Label n)) :
    ProbComp ((Result × PqxdhRecordLiftProtocol.Control n) × (PqxdhRecordLiftProtocol.Private n × List (Label n))) :=
  (simulateQ (recordService (PqxdhRecordLiftProtocol.interpreter policy setup codec))
    (PqxdhRecordLiftProtocol.schedule codec.frameRead route client
      (PqxdhRecordLiftProtocol.control state))).run (PqxdhRecordLiftProtocol.privateState state, attempts)

/-- Actual adaptive source execution is recovered exactly, including its complete state; the private attempt log is not a security observation. -/
theorem tracedSchedule_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : State n) (attempts : List (Label n)) :
    PqxdhRecordLiftProtocol.rejoin <$> (Prod.map id Prod.fst <$>
      tracedSchedule policy setup codec route client state attempts) =
      (simulateQ (handler policy setup codec route) client).run state := by
  rw [tracedSchedule, recordService_complete]
  exact PqxdhRecordLiftProtocol.schedule_join policy setup codec route client state

/-- A supported service result carries exactly the old private trace plus this actual request's sealing coordinate. -/
theorem recordService_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (state : P × List (Label n))
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × (P × List (Label n)))
    (supported : result ∈ support ((recordService service query).run state)) :
    result.2.2 = state.2 ++ sealingCoordinates query := by
  simp only [recordService, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  rfl

/-- An admitted hidden source send records exactly its current coordinate once and returns the successor kernel even when the writer returns none. -/
theorem protocol_send_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (slot : Slot n) (entry : LabeledKernel n) (context : RawCtxSourceSend.SealContext)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) RawCtxSourceSend.SealContext)
    (admitted : RawCtxChainSend.normalBegin entry context = .requested pending)
    (state : P × List (Label n))
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      (PqxdhRecordLiftProtocol.kernelSend (.hidden slot entry) context)).run state)) :
    result.1.1 = .hidden slot { entry with control := pending.committed_control, send_chain := PqxdhRecordLiftChainState.advance entry.send_chain 1 } ∧
      result.2.2 = state.2 ++ [entry.send_chain] := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked entry context
  rw [admitted] at tracked
  simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
    admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, PqxdhRecordLiftProtocol.localLift, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨looked, lookupSupported, continued⟩ := supported
  rw [mem_support_bind_iff] at continued
  obtain ⟨sealed, sealSupported, finished⟩ := continued
  simp only [support_pure, Set.mem_singleton_iff] at finished
  subst result
  exact ⟨congrArg (StoredKernel.hidden slot)
    (PqxdhRecordLiftChainState.send_ready_kernel entry context pending pending.request tracked),
    by
      change sealed.2.2 = state.2 ++ [entry.send_chain]
      have sealTrace := recordService_trace service (.sealing (RawCtxChainSend.ready pending
        (PqxdhRecordLiftChainState.advance pending.request 1, pending.request))) looked.2 sealed sealSupported
      have lookupTrace := recordService_trace service (.lookup pending.request) state looked lookupSupported
      rw [sealTrace, lookupTrace]
      simp only [sealingCoordinates, List.append_nil, RawCtxChainSend.ready, tracked.2.2.1]⟩

/-- The full recursive opaque receive makes no sealing attempt, including cached opening, future derivation and rollback. -/
theorem receiveProgram_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (effect : PqxdhRecordLiftChainCompiler.Effect (Slot n) RawCtxWholeOwner.OpenContext)
    (state : P × List (Label n))
    (result : (LabeledKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      (simulateQ PqxdhRecordLiftProtocol.localLift
        (PqxdhRecordLiftOpaqueDrivers.receiveProgram effect))).run state)) : result.2.2 = state.2 := by
  generalize depthEq : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result with
  | h depth ih =>
      cases effect with
      | rejected entry context =>
          simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          subst result
          rfl
      | openRequested pending =>
          simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind, simulateQ_spec_query,
            simulateQ_pure, PqxdhRecordLiftProtocol.localLift, StateT.run_bind, StateT.run_pure] at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨opened, member, finished⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at finished
          subst result
          exact (recordService_trace service (.opening pending) state opened member).trans (List.append_nil _)
      | kdfRequested pending =>
          simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind, simulateQ_spec_query,
            PqxdhRecordLiftProtocol.localLift, StateT.run_bind] at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨looked, member, continued⟩ := supported
          have unchanged := recordService_trace service (.lookup pending.request) state looked member
          exact (ih _ (depthEq ▸ RawCtxChainReceive.normalResume_rank pending
            (PqxdhRecordLiftChainState.advance pending.request 1, pending.request)) _ looked.2 result continued rfl).trans
              (unchanged.trans (List.append_nil _))

/-- Both caller-known and hidden whole-kernel receive preserve the private sealing history. -/
theorem protocol_receive_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : P × List (Label n))
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      (PqxdhRecordLiftProtocol.kernelReceive stored target context)).run state)) : result.2.2 = state.2 := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨opened, member, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      exact (recordService_trace service (.knownReceive kernel target context) state opened member).trans (List.append_nil _)
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨opened, member, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      exact receiveProgram_trace service _ state opened member

/-- A local operation either has no hidden sealing attempt or records its actual old coordinate and installs the strict successor. -/
def AttemptDelta (before after : StoredKernel n) (prior next : List (Label n)) : Prop :=
  next = prior ∨ ∃ slot entry final, before = .hidden slot entry ∧ after = .hidden slot final ∧
    final.send_chain = PqxdhRecordLiftChainState.advance entry.send_chain 1 ∧ next = prior ++ [entry.send_chain]

/-- The exact source send's private log counts only hidden coordinate attempts; caller-known sends and exhausted hidden sends add none. -/
theorem protocol_kernelSend_delta {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext) (state : P × List (Label n))
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      (PqxdhRecordLiftProtocol.kernelSend stored context)).run state)) :
    AttemptDelta stored result.1.1 state.2 result.2.2 := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelSend, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨sealed, member, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      exact Or.inl ((recordService_trace service (.knownSend kernel context) state sealed member).trans (List.append_nil _))
  | hidden slot entry =>
      cases admitted : RawCtxChainSend.normalBegin entry context with
      | exhausted original prior =>
          simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
            admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_pure,
            pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact Or.inl rfl
      | requested pending =>
          have actual := protocol_send_trace service slot entry context pending admitted state result supported
          exact Or.inr ⟨slot, entry,
            { entry with control := pending.committed_control, send_chain := PqxdhRecordLiftChainState.advance entry.send_chain 1 },
            rfl, actual.1, rfl, actual.2⟩

/-- Literal empty-input/parser guards and optional replies preserve the exact hidden attempt delta for one owner command. -/
theorem protocol_ownerStep_delta {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : P × List (Label n))
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      (PqxdhRecordLiftProtocol.ownerStep sender decode query owner)).run state)) :
    AttemptDelta owner.kernel result.1.2.kernel state.2 result.2.2 := by
  cases query with
  | inl plaintext =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerSend] at supported
      split_ifs at supported with empty
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact Or.inl rfl
      · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨sealed, member, finished⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at finished
        subst result
        exact protocol_kernelSend_delta service owner.kernel _ state sealed member
  | inr raw =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerReceive] at supported
      repeat' split at supported
      case h_2.isTrue =>
        simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨opened, member, finished⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at finished
        subst result
        exact Or.inl (protocol_receive_trace service owner.kernel _ _ state opened member)
      all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      all_goals subst result
      all_goals exact Or.inl rfl

/-- Publishing actual attempted frames does not add another sealing attempt to the private coordinate history. -/
theorem protocol_ownerRun_delta {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : P × List (Label n))
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner)).run state)) :
    AttemptDelta owner.kernel result.1.2.kernel state.2 result.2.2 := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨inner, member, continued⟩ := supported
  rw [mem_support_bind_iff] at continued
  obtain ⟨published, publishedMember, finished⟩ := continued
  simp only [support_pure, Set.mem_singleton_iff] at finished
  subst result
  have trace := (recordService_trace service (.publish tag) inner.2 published publishedMember).trans (List.append_nil _)
  change AttemptDelta owner.kernel inner.1.2.kernel state.2 published.2.2
  rw [trace]
  exact protocol_ownerStep_delta service sender decode query owner state inner member

/-- One actual request either adds no attempt or logs one current physical coordinate whose stored sender advances strictly. -/
def AttemptStep (before after : State n) (prior next : List (Label n)) : Prop :=
  next = prior ∨ ∃ handle coordinate current,
    HiddenSender before handle coordinate ∧ HiddenSender after handle current ∧
    current.slot = coordinate.slot ∧ current.direction = coordinate.direction ∧
    coordinate.position < current.position ∧ next = prior ++ [coordinate]

/-- Complete Server putback turns the literal local trace delta into a strict physical sender step. -/
theorem server_attemptStep (before after : State n) (server : Server n)
    (existing : before.server = some server) (keyId : Std.U64) (peer : Peer n)
    (selected : server.peers keyId = some peer) (kernel : StoredKernel n) (raw : Nat)
    (stored : after.server = some { server with
      peers := Function.update server.peers keyId (some { peer with kernel := kernel }), rawAttempts := raw })
    (prior next : List (Label n)) (delta : AttemptDelta peer.kernel kernel prior next) :
    AttemptStep before after prior next := by
  rcases delta with unchanged | ⟨slot, entry, final, oldStored, newStored, advanced, trace⟩
  · exact Or.inl unchanged
  · refine Or.inr ⟨Sum.inl keyId, entry.send_chain, final.send_chain,
      ⟨server, peer, slot, entry, existing, selected, oldStored, rfl⟩, ?_, ?_, ?_, ?_, trace⟩
    · exact ⟨_, { peer with kernel := kernel }, slot, final, stored,
        Function.update_self _ _ _, newStored, rfl⟩
    · rw [advanced]; rfl
    · rw [advanced]; rfl
    · rw [advanced]; exact Nat.lt_succ_self _

/-- Complete Beacon putback turns the literal local trace delta into a strict physical sender step at the same owner index. -/
theorem beacon_attemptStep (before after : State n) (owner : Nat) (shell : BeaconShell)
    (kernel nextKernel : StoredKernel n)
    (selected : before.owners[owner]? = some (.established shell kernel))
    (stored : after.owners = before.owners.set owner (.established shell nextKernel))
    (prior next : List (Label n)) (delta : AttemptDelta kernel nextKernel prior next) :
    AttemptStep before after prior next := by
  rcases delta with unchanged | ⟨slot, entry, final, oldStored, newStored, advanced, trace⟩
  · exact Or.inl unchanged
  · refine Or.inr ⟨Sum.inr owner, entry.send_chain, final.send_chain,
      ⟨shell, slot, entry, oldStored ▸ selected, rfl⟩, ?_, ?_, ?_, ?_, trace⟩
    · refine ⟨shell, slot, final, ?_, rfl⟩
      rw [stored, List.getElem?_set_self (List.getElem?_eq_some_iff.mp selected).1, newStored]
    · rw [advanced]; rfl
    · rw [advanced]; rfl
    · rw [advanced]; exact Nat.lt_succ_self _

/-- The actual source Server routing program has at most one hidden attempt per request, with strict putback at its selected physical peer. -/
theorem protocol_serverStep_trace
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (state : PqxdhRecordLiftProtocol.Private n × List (Label n))
    (result : (RawCtxServerMixed.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n) ×
      (PqxdhRecordLiftProtocol.Private n × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      ((PqxdhRecordLiftProtocol.serverStep decode route query).run control)).run state)) :
    AttemptStep (PqxdhRecordLiftProtocol.join control state.1)
      (PqxdhRecordLiftProtocol.join result.1.2 result.2.1) state.2 result.2.2 := by
  change result ∈ support ((simulateQ (recordService service)
    (PqxdhRecordLiftProtocol.serverStep decode route query control)).run state) at supported
  cases existing : control.server with
  | none =>
      cases query <;>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact Or.inl rfl
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected, simulateQ_pure,
                StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact Or.inl rfl
          | some peer =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected,
                simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
              rw [mem_support_bind_iff] at supported
              obtain ⟨inner, member, finished⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at finished
              subst result
              exact server_attemptStep _ _ server existing keyId peer selected inner.1.2.kernel inner.1.2.rawAttempts rfl _ _
                (protocol_ownerRun_delta service _ server.sender decode (.inl plaintext) _ state inner member)
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, simulateQ_pure,
                StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact Or.inl rfl
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected, simulateQ_pure,
                    StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact Or.inl rfl
              | some peer =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected,
                    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
                  rw [mem_support_bind_iff] at supported
                  obtain ⟨inner, member, finished⟩ := supported
                  simp only [support_pure, Set.mem_singleton_iff] at finished
                  subst result
                  exact server_attemptStep _ _ server existing keyId peer selected inner.1.2.kernel inner.1.2.rawAttempts rfl _ _
                    (protocol_ownerRun_delta service _ server.sender decode (.inr raw) _ state inner member)

/-- The actual Beacon program preserves the same physical owner index when recording its one possible hidden sealing attempt. -/
theorem protocol_beaconStep_trace
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (control : PqxdhRecordLiftProtocol.Control n) (state : PqxdhRecordLiftProtocol.Private n × List (Label n))
    (result : (RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n) ×
      (PqxdhRecordLiftProtocol.Private n × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      ((PqxdhRecordLiftProtocol.beaconStep decode owner query).run control)).run state)) :
    AttemptStep (PqxdhRecordLiftProtocol.join control state.1)
      (PqxdhRecordLiftProtocol.join result.1.2 result.2.1) state.2 result.2.2 := by
  change result ∈ support ((simulateQ (recordService service)
    (PqxdhRecordLiftProtocol.beaconStep decode owner query control)).run state) at supported
  cases selected : control.owners[owner]? with
  | none =>
      simp only [PqxdhRecordLiftProtocol.beaconStep, selected, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact Or.inl rfl
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [PqxdhRecordLiftProtocol.beaconStep, selected, simulateQ_pure,
              StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported <;>
            subst result <;> exact Or.inl rfl
      | established shell kernel =>
          simp only [PqxdhRecordLiftProtocol.beaconStep, selected, simulateQ_bind,
            simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨inner, member, finished⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at finished
          subst result
          exact beacon_attemptStep _ _ owner shell kernel inner.1.2.kernel selected rfl _ _
            (protocol_ownerRun_delta service _ shell.identityKeyId decode query _ state inner member)

/-- Allocating or reusing an installation seed is not a hidden record sealing attempt. -/
theorem protocol_resolve_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (role : Role) (ref : KernelRef n) (state : P × List (Label n))
    (result : StoredKernel n × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      (PqxdhRecordLiftProtocol.resolve role ref)).run state)) : result.2.2 = state.2 := by
  cases ref with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.resolve, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | hidden slot =>
      simp only [PqxdhRecordLiftProtocol.resolve, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨allocated, member, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      exact (recordService_trace service (.allocate slot) state allocated member).trans (List.append_nil _)

/-- Source Server install guards and seed resolution never produce an ordinary hidden-record sealing attempt. -/
theorem protocol_installServer_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (state : P × List (Label n))
    (result : (Bool × PqxdhRecordLiftProtocol.Control n) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      ((PqxdhRecordLiftProtocol.installServer keyId identity ref).run control)).run state)) : result.2.2 = state.2 := by
  change result ∈ support ((simulateQ (recordService service)
    (PqxdhRecordLiftProtocol.installServer keyId identity ref control)).run state) at supported
  cases found : control.server with
  | none =>
      simp only [PqxdhRecordLiftProtocol.installServer, found, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | some server =>
      simp only [PqxdhRecordLiftProtocol.installServer, found] at supported
      split_ifs at supported with admitted
      · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨resolved, member, finished⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at finished
        subst result
        exact protocol_resolve_trace service .server ref state resolved member
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst result
        rfl

/-- Source Beacon install guards and seed resolution never produce an ordinary hidden-record sealing attempt. -/
theorem protocol_installBeacon_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (state : P × List (Label n))
    (result : (Bool × PqxdhRecordLiftProtocol.Control n) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      ((PqxdhRecordLiftProtocol.installBeacon owner shell ref).run control)).run state)) : result.2.2 = state.2 := by
  change result ∈ support ((simulateQ (recordService service)
    (PqxdhRecordLiftProtocol.installBeacon owner shell ref control)).run state) at supported
  simp only [PqxdhRecordLiftProtocol.installBeacon] at supported
  split_ifs at supported with admitted
  · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨resolved, member, finished⟩ := supported
    simp only [support_pure, Set.mem_singleton_iff] at finished
    subst result
    exact protocol_resolve_trace service .beacon ref state resolved member
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl

/-- A lifted non-sealing private service preserves the attempt history while retaining its literal reply and the complete control state. -/
theorem protocol_lift_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (notSealing : sealingCoordinates query = [])
    (control : PqxdhRecordLiftProtocol.Control n) (state : P × List (Label n))
    (result : ((PqxdhRecordLiftProtocol.ServiceSpec n).Range query × PqxdhRecordLiftProtocol.Control n) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      ((StateT.lift ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) : PqxdhRecordLiftProtocol.Client n _).run control)).run state)) :
    result.2.2 = state.2 := by
  change result ∈ support ((simulateQ (recordService service)
    ((fun reply => (reply, control)) <$> (PqxdhRecordLiftProtocol.ServiceSpec n).query query)).run state) at supported
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact (recordService_trace service query state inner member).trans (by rw [notSealing, List.append_nil])

/-- Source initialization imports known records but invokes no hidden sealing service. -/
theorem protocol_initialize_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (created : PqxdhLiveServerConstruction.Created Unit) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (Label n)) (result : (Unit × PqxdhRecordLiftProtocol.Control n) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      ((PqxdhRecordLiftProtocol.initializeServer created).run control)).run state)) : result.2.2 = state.2 := by
  change result ∈ support ((simulateQ (recordService service)
    (PqxdhRecordLiftProtocol.initializeServer created control)).run state) at supported
  cases found : control.server <;>
    simp only [PqxdhRecordLiftProtocol.initializeServer, found, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported <;>
    subst result <;> rfl

/-- All frozen administrative, public hash and presence capabilities preserve the ordinary hidden-record attempt history. -/
theorem protocol_capability_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (query : (CapabilitySpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (Label n))
    (result : ((CapabilitySpec n).Range query × PqxdhRecordLiftProtocol.Control n) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      ((PqxdhRecordLiftProtocol.capability query).run control)).run state)) : result.2.2 = state.2 := by
  cases query with
  | installServer keyId identity ref => exact protocol_installServer_trace service keyId identity ref control state result supported
  | installBeacon owner shell ref => exact protocol_installBeacon_trace service owner shell ref control state result supported
  | hash bytes => exact protocol_lift_trace service (.hash bytes) rfl control state result supported
  | peerPresent keyId =>
      change result ∈ support (pure (((control.server.bind fun server => server.peers keyId).isSome, control), state)) at supported
      exact (Set.mem_singleton_iff.mp supported).symm ▸ rfl
  | ownerPresent owner =>
      change result ∈ support (pure (((control.owners[owner]?).isSome, control), state)) at supported
      exact (Set.mem_singleton_iff.mp supported).symm ▸ rfl
  | appendOwner sender pin phase =>
      change result ∈ support (pure ((control.owners.length, { control with owners := control.owners ++ [.inactive phase] }), state)) at supported
      exact (Set.mem_singleton_iff.mp supported).symm ▸ rfl
  | advanceOwner owner phase =>
      change result ∈ support ((simulateQ (recordService service)
        (PqxdhRecordLiftProtocol.capability (.advanceOwner owner phase) control)).run state) at supported
      cases found : control.owners[owner]? with
      | none =>
          simp only [PqxdhRecordLiftProtocol.capability, found, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          subst result
          rfl
      | some current =>
          cases current with
          | established shell kernel =>
              simp only [PqxdhRecordLiftProtocol.capability, found, simulateQ_pure,
                StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
              subst result
              rfl
          | inactive before =>
              simp only [PqxdhRecordLiftProtocol.capability, found] at supported
              split_ifs at supported with legal <;>
                simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported <;>
                subst result <;> rfl

/-- Every charged effect route preserves the attempt list, including arbitrary startup, environment and wrapper coins. -/
theorem protocol_effects_trace {P : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (query : (EnvEffects n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (Label n))
    (result : ((EnvEffects n).Range query × PqxdhRecordLiftProtocol.Control n) × (P × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      ((PqxdhRecordLiftProtocol.effects query).run control)).run state)) : result.2.2 = state.2 := by
  cases query with
  | inl coin =>
      simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨charged, chargeMember, continued⟩ := supported
      rw [mem_support_bind_iff] at continued
      obtain ⟨sampled, sampleMember, finished⟩ := continued
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      have chargedTrace := protocol_lift_trace service (.charge (effectKind (.inl coin))) rfl control state charged chargeMember
      have sampledTrace := (recordService_trace service (.coin coin) charged.2 sampled sampleMember).trans (List.append_nil _)
      exact sampledTrace.trans chargedTrace
  | inr request =>
      simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨charged, chargeMember, continued⟩ := supported
      have chargedTrace := protocol_lift_trace service (.charge (effectKind (.inr request))) rfl control state charged chargeMember
      exact (protocol_capability_trace service request charged.1.2 charged.2 result continued).trans chargedTrace

/-- Every actual global source request has the traced strict-step property, independently of private service replies. -/
theorem protocol_handler_trace
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (state : PqxdhRecordLiftProtocol.Private n × List (Label n))
    (result : ((WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n) ×
      (PqxdhRecordLiftProtocol.Private n × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService service)
      ((PqxdhRecordLiftProtocol.handler decode route query).run control)).run state)) :
    AttemptStep (PqxdhRecordLiftProtocol.join control state.1)
      (PqxdhRecordLiftProtocol.join result.1.2 result.2.1) state.2 result.2.2 := by
  cases query with
  | inl created => exact Or.inl (protocol_initialize_trace service created control state result supported)
  | inr outer =>
      cases outer with
      | inl effect => exact Or.inl (protocol_effects_trace service effect control state result supported)
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact protocol_serverStep_trace service decode route (.inl send) control state result supported
              | inr raw => exact protocol_serverStep_trace service decode route (.inr raw) control state result supported
          | inr ownerQuery =>
              obtain ⟨owner, query⟩ := ownerQuery
              cases query with
              | inl plaintext => exact protocol_beaconStep_trace service decode owner (.inl plaintext) control state result supported
              | inr raw => exact protocol_beaconStep_trace service decode owner (.inr raw) control state result supported

/-- Strict source progress preserves the past-attempt invariant and rules out an actual repeated coordinate. -/
theorem attemptStep_history (before after : State n) (prior : Roles before) (roles : Roles after)
    (provenance : Provenance before) (forward : Forward before after)
    (old next : List (Label n)) (past : Past before old) (distinct : old.Nodup)
    (step : AttemptStep before after old next) : Past after next ∧ next.Nodup := by
  have oldPast := past_forward before after prior roles forward old past
  rcases step with unchanged | ⟨handle, coordinate, current, sending, sent, slot, direction, progress, trace⟩
  · subst next
    exact ⟨oldPast, distinct⟩
  · subst next
    constructor
    · intro attempted member
      rcases List.mem_append.mp member with earlier | fresh
      · exact oldPast attempted earlier
      · have same := List.mem_singleton.mp fresh
        subst attempted
        exact ⟨handle, current, sent, slot, direction, progress⟩
    · rw [← List.concat_eq_append, List.nodup_concat]
      exact ⟨past_not_current before prior provenance old past handle coordinate sending, distinct⟩

/-- A request boundary with no pending writer frames reconstructs its entire original private state. -/
theorem private_join (control : PqxdhRecordLiftProtocol.Control n)
    (secret : PqxdhRecordLiftProtocol.Private n) (empty : secret.pending = []) :
    PqxdhRecordLiftProtocol.privateState (PqxdhRecordLiftProtocol.join control secret) = secret := by
  cases secret
  cases empty
  rfl

/-- The private trace's projection is the exact original full source result and its empty pending writer buffer. -/
theorem protocol_handler_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n) (attempts : List (Label n))
    (result : ((WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n) ×
      (PqxdhRecordLiftProtocol.Private n × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService (PqxdhRecordLiftProtocol.interpreter policy setup codec))
      ((PqxdhRecordLiftProtocol.handler codec.frameRead route query).run (PqxdhRecordLiftProtocol.control state))).run
        (PqxdhRecordLiftProtocol.privateState state, attempts))) :
    ∃ original, original ∈ support ((handler policy setup codec route query).run state) ∧
      (result.1, result.2.1) = PqxdhRecordLiftProtocol.splitResult original := by
  have projected : (result.1, result.2.1) ∈ support
      (Prod.map id Prod.fst <$> (simulateQ (recordService (PqxdhRecordLiftProtocol.interpreter policy setup codec))
        ((PqxdhRecordLiftProtocol.handler codec.frameRead route query).run (PqxdhRecordLiftProtocol.control state))).run
          (PqxdhRecordLiftProtocol.privateState state, attempts)) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [recordService_complete, PqxdhRecordLiftProtocol.handler_factor] at projected
  simp only [support_map] at projected
  obtain ⟨original, member, equal⟩ := projected
  exact ⟨original, member, equal.symm⟩

/-- Internal request-boundary invariant: the writer buffer is empty, roles and origins are actual, and every distinct prior attempt is behind its persistent sender. -/
def TraceGood (control : PqxdhRecordLiftProtocol.Control n)
    (secret : PqxdhRecordLiftProtocol.Private n) (attempts : List (Label n)) : Prop :=
  secret.pending = [] ∧ Roles (PqxdhRecordLiftProtocol.join control secret) ∧
    Provenance (PqxdhRecordLiftProtocol.join control secret) ∧
    Past (PqxdhRecordLiftProtocol.join control secret) attempts ∧ attempts.Nodup

/-- One actual instrumented request derives history preservation from source admission, physical origin uniqueness and strict send putback. -/
theorem protocol_handler_history {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : PqxdhRecordLiftProtocol.Private n) (attempts : List (Label n))
    (good : TraceGood control secret attempts)
    (result : ((WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n) ×
      (PqxdhRecordLiftProtocol.Private n × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService (PqxdhRecordLiftProtocol.interpreter policy setup codec))
      ((PqxdhRecordLiftProtocol.handler codec.frameRead route query).run control)).run (secret, attempts))) :
    TraceGood result.1.2 result.2.1 result.2.2 := by
  obtain ⟨original, member, shape⟩ := protocol_handler_source policy setup codec route query
    (PqxdhRecordLiftProtocol.join control secret) attempts result
    (by
      rw [private_join control secret good.1]
      cases control
      exact supported)
  have whole : PqxdhRecordLiftProtocol.join result.1.2 result.2.1 = original.2 :=
    congrArg Prod.snd (congrArg PqxdhRecordLiftProtocol.rejoin shape)
  have empty : result.2.1.pending = [] := congrArg (fun pair => pair.2.pending) shape
  have roles : Roles (PqxdhRecordLiftProtocol.join result.1.2 result.2.1) :=
    whole.symm ▸ handler_roles policy setup codec route query _ good.2.1 original member
  have provenance : Provenance (PqxdhRecordLiftProtocol.join result.1.2 result.2.1) :=
    whole.symm ▸ handler_provenance policy setup codec route query _ good.2.2.1 original member
  have forward : Forward (PqxdhRecordLiftProtocol.join control secret)
      (PqxdhRecordLiftProtocol.join result.1.2 result.2.1) :=
    whole.symm ▸ handler_forward policy setup codec route query _ good.2.1 original member
  have step := protocol_handler_trace (PqxdhRecordLiftProtocol.interpreter policy setup codec)
    codec.frameRead route query control (secret, attempts) result supported
  exact ⟨empty, roles, provenance,
    attemptStep_history _ _ good.2.1 roles good.2.2.1 forward attempts result.2.2 good.2.2.2.1 good.2.2.2.2 step⟩

/-- Every actual adaptive compiled schedule preserves the complete private attempt invariant, with no condition on the lookup policy. -/
theorem protocol_schedule_history {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : PqxdhRecordLiftProtocol.Private n) (attempts : List (Label n))
    (good : TraceGood control secret attempts)
    (result : (Result × PqxdhRecordLiftProtocol.Control n) ×
      (PqxdhRecordLiftProtocol.Private n × List (Label n)))
    (supported : result ∈ support ((simulateQ (recordService (PqxdhRecordLiftProtocol.interpreter policy setup codec))
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route client control)).run (secret, attempts))) :
    TraceGood result.1.2 result.2.1 result.2.2 := by
  induction client using OracleComp.inductionOn generalizing control secret attempts result with
  | pure value =>
      simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact good
  | query_bind query next ih =>
      simp only [PqxdhRecordLiftProtocol.schedule, StateT.run_bind, simulateQ_bind,
        simulateQ_spec_query] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨inner, member, continued⟩ := supported
      exact ih inner.1.1 inner.1.2 inner.2.1 inner.2.2
        (protocol_handler_history policy setup codec route query control secret attempts good inner member)
        result continued

/-- The actual initial state establishes the trace invariant without any assumed reachable-prefix property. -/
theorem initial_traceGood : TraceGood (PqxdhRecordLiftProtocol.initialControl : PqxdhRecordLiftProtocol.Control n)
    PqxdhRecordLiftProtocol.initialPrivate [] := by
  refine ⟨rfl, initial_roles, initial_provenance, ?_, List.nodup_nil⟩
  intro coordinate member
  cases member

/-- The literal sealing-service trace of every actual adaptive initial World schedule contains each structural hidden coordinate at most once. -/
theorem tracedSchedule_initial_nodup {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result)
    (result : (Result × PqxdhRecordLiftProtocol.Control n) ×
      (PqxdhRecordLiftProtocol.Private n × List (Label n)))
    (supported : result ∈ support (tracedSchedule policy setup codec route client initial [])) :
    result.2.2.Nodup :=
  (protocol_schedule_history policy setup codec route client PqxdhRecordLiftProtocol.initialControl
    PqxdhRecordLiftProtocol.initialPrivate [] initial_traceGood result supported).2.2.2.2

/-- The frozen environment/adversary program inherits historical hidden-send uniqueness from its actual execution, including failed writer replies and both physical directions. -/
theorem tracedProgram_nodup {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × PqxdhRecordLiftProtocol.Control n) ×
      (PqxdhRecordLiftProtocol.Private n × List (Label n)))
    (supported : result ∈ support (tracedSchedule policy setup codec route
      (program env setup.source.crypto codec serverKid bounds mode adversary) initial [])) : result.2.2.Nodup :=
  tracedSchedule_initial_nodup policy setup codec route _ result supported

end BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernel_receive_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernel_receive_oriented

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernel_send_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernel_send_oriented

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.labeledKernel_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.labeledKernel_oriented

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.owner_receive_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.owner_receive_oriented

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.owner_send_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.owner_send_oriented

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.owner_step_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.owner_step_oriented

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.roles_server_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.roles_server_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.roles_owner_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.roles_owner_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.resolve_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.resolve_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.markUsed_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.markUsed_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installBeacon_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installBeacon_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installServer_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installServer_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initialize_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initialize_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.roles_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.roles_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.capability_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.capability_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.effects_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.effects_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerRun_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerRun_oriented

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconPublish_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconPublish_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.roles_serverRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.roles_serverRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverPublish_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverPublish_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconStep_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconStep_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverStep_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverStep_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initial_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initial_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.schedule_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.schedule_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.run_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.run_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelSend_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelSend_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelReceive_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelReceive_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerStep_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerStep_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerRun_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerRun_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_server_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_server_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_owner_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_owner_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installServer_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installServer_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installBeacon_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installBeacon_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_owner_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.origins_owner_same

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.capability_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.capability_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.effects_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.effects_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initialize_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initialize_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconPublish_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconPublish_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverPublish_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverPublish_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconStep_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconStep_provenance

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverStep_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverStep_provenance

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.resolve_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.resolve_used

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installServer_uses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installServer_uses

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installBeacon_uses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installBeacon_uses

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.marker_update_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.marker_update_persists

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.capability_marker_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.capability_marker_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.effects_marker_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.effects_marker_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_marker_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_marker_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_provenance

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initial_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initial_provenance

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.schedule_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.schedule_provenance

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.run_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.run_provenance

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initial_schedule_sender_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initial_schedule_sender_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.send_requested_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.send_requested_progress

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.send_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.send_outcome

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.send_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.send_max

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelSend_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelSend_progress

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelReceive_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelReceive_send

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.storedAhead_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.storedAhead_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.storedAhead_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.storedAhead_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelSend_ahead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelSend_ahead

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelReceive_ahead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.kernelReceive_ahead

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerStep_ahead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerStep_ahead

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerRun_ahead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.ownerRun_ahead

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_server_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_server_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_owner_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_owner_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverPublish_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverPublish_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconPublish_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconPublish_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_serverRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_serverRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconStep_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beaconStep_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverStep_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.serverStep_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.resolve_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.resolve_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.markUsed_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.markUsed_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installServer_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installServer_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installBeacon_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.installBeacon_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initialize_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initialize_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.forward_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.capability_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.capability_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.effects_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.effects_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.handler_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.schedule_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.schedule_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_origin_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_origin_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_functional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_functional

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.hiddenSender_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.past_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.past_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.past_not_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.past_not_current

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.recordService_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.recordService_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.recordService_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.recordService_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.tracedSchedule_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.tracedSchedule_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.recordService_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.recordService_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_send_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_send_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.receiveProgram_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.receiveProgram_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_receive_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_receive_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_kernelSend_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_kernelSend_delta

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_ownerStep_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_ownerStep_delta

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_ownerRun_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_ownerRun_delta

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.server_attemptStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.server_attemptStep

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beacon_attemptStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.beacon_attemptStep

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_serverStep_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_serverStep_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_beaconStep_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_beaconStep_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_resolve_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_resolve_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_installServer_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_installServer_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_installBeacon_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_installBeacon_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_lift_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_lift_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_initialize_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_initialize_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_capability_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_capability_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_effects_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_effects_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_handler_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_handler_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.attemptStep_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.attemptStep_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.private_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.private_join

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_handler_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_handler_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_handler_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_schedule_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.protocol_schedule_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initial_traceGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.initial_traceGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.tracedSchedule_initial_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.tracedSchedule_initial_nodup

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.tracedProgram_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance.tracedProgram_nodup
