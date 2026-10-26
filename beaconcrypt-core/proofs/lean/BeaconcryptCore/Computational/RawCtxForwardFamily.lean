import BeaconcryptCore.Computational.RawCtxForwardServer

/-!
The finite role-family compiler carries the original selected Server or established Beacon context before each private call. It preserves the complete family, the original outside client, all inactive-role outcomes and public requests. Returned role states are installed at the same source index before the outside program resumes. These descriptors are private execution metadata, not network or reveal values.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardFamily
open RawCtxSelectedFamilyContext RawCtxForwardAnnotation

abbrev Base := RawCtxPendingOwnerQueries.Spec RatchetChain
abbrev Spec (M P I D K Result : Type) (S B : Nat) :=
  RawCtxForwardAnnotation.Spec (FamilyContext M P I D K Result S B) Base
abbrev State (M P I D K : Type) (S B : Nat) := NativeFamily M P I D K S B
abbrev SourceSpec := RawCtxProtocolRoles.SourceSpec
variable {M P I D K Result : Type} {S B : Nat}

noncomputable def server
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : ServerSpec.Domain) (before : State M P I D K S B) (index : Fin S)
    (outside : ServerSpec.Range request → OracleComp (SourceSpec S B) Result)
    (after : ServerSpec.Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B)) :
    OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B) := do
  let result ← mapTags (fun inner => FamilyContext.server request before index outside inner)
    (RawCtxForwardServer.program sender route decode (ServerSpec.query request) (before.1 index))
  after result.1 (Function.update before.1 index result.2, before.2)

noncomputable def beacon
    (decode : RawCtxReceive.FrameDecoder) (request : RawCtxMixedOwner.SourceSpec.Domain)
    (before : State M P I D K S B) (index : Fin B)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (SourceSpec S B) Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B)) :
    OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B) :=
  match (before.2 index).beacon.phase with
  | .established control associatedData kernel => do
      let result ← mapTags (fun inner => FamilyContext.beacon request before index control associatedData outside inner)
        (RawCtxForwardOwner.program (before.2 index).beacon.identityKeyId decode
          (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request))
          (RawCtxGenericBeacon.selected (before.2 index) control associatedData kernel))
      after result.1 (before.1, Function.update before.2 index
        (RawCtxGenericBeacon.reinstall (before.2 index) control associatedData result.2))
  | _ =>
      let result := RawCtxGenericBeacon.rejected request (before.2 index)
      after result.1 (before.1, Function.update before.2 index result.2)

noncomputable def program
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Result) :
    State M P I D K S B → OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B) :=
  OracleComp.recOn client (fun result state => pure (result, state))
    (fun request outside recurse state => match request with
      | .inl ⟨index, query⟩ => server sender route decode query state index outside recurse
      | .inr (.inl ⟨index, query⟩) => beacon decode query state index outside recurse
      | .inr (.inr query) => do
          let reply ← (Spec M P I D K Result S B).query (none, .inr (.inr query))
          recurse reply state)

/-- One original family request is fully dispatched before its adaptive outside client. -/
theorem program_query
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (SourceSpec S B).Domain)
    (outside : (SourceSpec S B).Range request → OracleComp (SourceSpec S B) Result)
    (state : State M P I D K S B) :
    program sender route decode (((SourceSpec S B).query request : OracleComp (SourceSpec S B) _) >>= outside) state =
      (match request with
      | .inl ⟨index, query⟩ => server sender route decode query state index outside
          (fun reply updated => program sender route decode (outside reply) updated)
      | .inr (.inl ⟨index, query⟩) => beacon decode query state index outside
          (fun reply updated => program sender route decode (outside reply) updated)
      | .inr (.inr query) => do
          let reply ← (Spec M P I D K Result S B).query (none, .inr (.inr query))
          program sender route decode (outside reply) state) := by
  rcases request with ⟨index, request⟩ | (⟨index, request⟩ | publicQuery) <;> rfl

/-- The selected Server runs completely and is reinstalled at its original family index after annotation erasure. -/
theorem server_erase
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : ServerSpec.Domain) (before : State M P I D K S B) (index : Fin S)
    (outside : ServerSpec.Range request → OracleComp (SourceSpec S B) Result)
    (after : ServerSpec.Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B))
    (after_erase : ∀ reply updated, simulateQ erase (after reply updated) =
      RawCtxPendingFamilyTails.program sender route decode (outside reply) updated) :
    simulateQ erase (server sender route decode request before index outside after) =
      RawCtxPendingFamilyTails.liftServer sender route decode before index outside
        (RawCtxPendingServerTails.program sender route decode (ServerSpec.query request) (before.1 index)) := by
  simp only [server, simulateQ_bind, erase_mapTags, RawCtxForwardServer.program_erase, after_erase,
    RawCtxPendingFamilyTails.liftServer]
  rfl

/-- An established Beacon's full owner operation and original role publication survive descriptor erasure. -/
theorem beacon_erase
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : State M P I D K S B) (index : Fin B)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (SourceSpec S B) Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B))
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 281#usize)
    (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain)
    (active : (before.2 index).beacon.phase = .established control associatedData kernel)
    (after_erase : ∀ reply updated, simulateQ erase (after reply updated) =
      RawCtxPendingFamilyTails.program sender route decode (outside reply) updated) :
    simulateQ erase (beacon decode request before index outside after) =
      RawCtxPendingFamilyTails.liftBeacon sender route decode before index control associatedData outside
        (RawCtxPendingOwnerTails.program (before.2 index).beacon.identityKeyId decode
          (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request))
          (RawCtxGenericBeacon.selected (before.2 index) control associatedData kernel)) := by
  simp only [beacon, active, simulateQ_bind, erase_mapTags, RawCtxForwardOwner.program_erase,
    after_erase, RawCtxPendingFamilyTails.liftBeacon]
  rfl

/-- The complete forward role-family compiler erases to the actual source execution with every original role, reply and public callback. -/
theorem program_erase
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Result) (state : State M P I D K S B) :
    simulateQ erase (program sender route decode client state) =
      RawCtxPendingFamilyTails.program sender route decode client state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind request outside ih =>
    rw [program_query]
    rcases request with ⟨index, request⟩ | (⟨index, request⟩ | publicQuery)
    all_goals dsimp only
    case inr.inl =>
      cases active : (state.2 index).beacon.phase
      case established control associatedData kernel =>
        exact (beacon_erase sender route decode request state index outside _ control associatedData kernel active ih).trans
          (RawCtxPendingFamilyTails.beacon_selected sender route decode request index control associatedData kernel outside state active).symm
      all_goals
        rw [RawCtxPendingFamilyTails.program_query sender route decode (.inr (.inl ⟨index, request⟩)) outside state]
        simp only [beacon, active, StateT.run, RawCtxGenericFamilyFrontend.impl, RawCtxGenericBeacon.impl, pure_bind]
        exact ih _ _
    case inl =>
      exact (server_erase sender route decode request state index outside _ ih).trans
        (RawCtxPendingFamilyTails.server_selected sender route decode request index outside state).symm
    case inr.inr =>
      rw [RawCtxPendingFamilyTails.program_query sender route decode (.inr (.inr publicQuery)) outside state]
      simp only [simulateQ_bind, StateT.run, RawCtxGenericFamilyFrontend.impl,
        RawCtxPendingOwnerQueries.publicForward, bind_assoc, pure_bind, ih]
      rfl

/-- A carried Server context retains its exact original full family continuation. -/
theorem server_sound
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : ServerSpec.Domain) (before : State M P I D K S B) (index : Fin S)
    (outside : ServerSpec.Range request → OracleComp (SourceSpec S B) Result)
    (after : ServerSpec.Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B))
    (after_erase : ∀ reply updated, simulateQ erase (after reply updated) =
      RawCtxPendingFamilyTails.program sender route decode (outside reply) updated)
    (after_sound : ∀ reply updated, Sound (familyFrame sender route decode) (after reply updated)) :
    Sound (familyFrame sender route decode) (server sender route decode request before index outside after) := by
  apply RawCtxForwardAnnotationComposition.sound_map_bind
    (serverFrame sender route decode) (familyFrame sender route decode)
    (fun inner => FamilyContext.server request before index outside inner) _ _
    (RawCtxForwardServer.program_sound _ _ _ _ _) (fun result => after_sound result.1 _)
  simp only [familyFrame, RawCtxForwardAnnotationComposition.appendFrame, after_erase, RawCtxPendingFamilyTails.liftServer]
  intro tag; rfl

/-- The actual Beacon phase dispatch carries only exact owner descriptors, with full family reinstallation before its outside program. -/
theorem beacon_sound
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : State M P I D K S B) (index : Fin B)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (SourceSpec S B) Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B))
    (after_erase : ∀ reply updated, simulateQ erase (after reply updated) =
      RawCtxPendingFamilyTails.program sender route decode (outside reply) updated)
    (after_sound : ∀ reply updated, Sound (familyFrame sender route decode) (after reply updated)) :
    Sound (familyFrame sender route decode) (beacon decode request before index outside after) := by
  cases active : (before.2 index).beacon.phase <;> simp only [beacon, active]
  case established control associatedData kernel =>
    apply RawCtxForwardAnnotationComposition.sound_map_bind
      (ownerFrame (before.2 index).beacon.identityKeyId decode) (familyFrame sender route decode)
      (fun inner => FamilyContext.beacon request before index control associatedData outside inner) _ _
      (RawCtxForwardOwner.program_sound _ _ _ _) (fun result => after_sound result.1 _)
    simp only [familyFrame, RawCtxForwardAnnotationComposition.appendFrame, after_erase, RawCtxPendingFamilyTails.liftBeacon]
    intro tag; rfl
  all_goals exact after_sound _ _

/-- The entire actual role-family client constructs exact pending descriptors before every private callback, with its complete adaptive outside continuation. -/
theorem program_sound
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Result) (state : State M P I D K S B) :
    Sound (familyFrame sender route decode) (program sender route decode client state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => exact sound_pure _ _
  | query_bind request outside ih =>
    rw [program_query]
    rcases request with ⟨index, request⟩ | (⟨index, request⟩ | publicQuery)
    all_goals dsimp only
    · exact server_sound sender route decode _ _ _ _ _ (fun reply updated => program_erase sender route decode (outside reply) updated) ih
    · exact beacon_sound sender route decode _ _ _ _ _ (fun reply updated => program_erase sender route decode (outside reply) updated) ih
    · rw [sound_query]
      exact ⟨(fun _ impossible => nomatch impossible), fun reply => ih reply state⟩

/-- Every private derivation in the selected Server or its outside continuation retains a carried descriptor. -/
theorem server_covered
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : ServerSpec.Domain) (before : State M P I D K S B) (index : Fin S)
    (outside : ServerSpec.Range request → OracleComp (SourceSpec S B) Result)
    (after : ServerSpec.Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B))
    (after_covered : ∀ reply updated, RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (after reply updated)) :
    RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (server sender route decode request before index outside after) := by
  exact RawCtxForwardAnnotationComposition.covered_map_bind _ _ _ _
    (RawCtxForwardServer.program_covered _ _ _ _ _) (fun result => after_covered result.1 _)

/-- Beacon phase dispatch and reinstallation preserve coverage under every original reply. -/
theorem beacon_covered
    (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : State M P I D K S B) (index : Fin B)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (SourceSpec S B) Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B))
    (after_covered : ∀ reply updated, RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (after reply updated)) :
    RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (beacon decode request before index outside after) := by
  cases active : (before.2 index).beacon.phase <;> simp only [beacon, active]
  case established control associatedData kernel =>
    exact RawCtxForwardAnnotationComposition.covered_map_bind _ _ _ _
      (RawCtxForwardOwner.program_covered _ _ _ _) (fun result => after_covered result.1 _)
  all_goals exact after_covered _ _

/-- Every private derivation of the complete actual family client is annotated, and public queries are not, under every adaptive response. -/
theorem program_covered
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Result) (state : State M P I D K S B) :
    RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (program sender route decode client state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => exact RawCtxForwardCoverage.covered_pure _ _
  | query_bind request outside ih =>
    rw [program_query]
    rcases request with ⟨index, request⟩ | (⟨index, request⟩ | publicQuery)
    all_goals dsimp only
    · exact server_covered sender route decode _ _ _ _ _ ih
    · exact beacon_covered decode _ _ _ _ _ ih
    · rw [RawCtxForwardCoverage.covered_query]
      exact ⟨rfl, fun reply => ih reply state⟩

end BeaconcryptCore.Computational.RawCtxForwardFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.program_query

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.server_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.server_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.beacon_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.beacon_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.program_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.server_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.server_sound

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.beacon_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.beacon_sound

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.program_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.program_sound

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.server_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.server_covered

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.beacon_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.beacon_covered

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFamily.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFamily.program_covered
