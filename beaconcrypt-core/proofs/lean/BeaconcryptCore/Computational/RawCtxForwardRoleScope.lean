import BeaconcryptCore.Computational.RawCtxForwardOwnerScope
import BeaconcryptCore.Computational.RawCtxForwardLive

/-!
The actual indexed Server, Beacon and disclosure-aware family compilers retain each inner owner's raw admission certificate in the literal saved descriptor. Routing, inactive roles, publication, public services and arbitrary outside continuations remain the original source operations.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardRoleScope
open RawCtxForwardTags RawCtxSelectedFamilyContext
variable {M P I D K Result : Type} {S B : Nat}

def ServerValid (read : RawCtxReceive.FrameDecoder) : ServerContext M P Result → Prop
  | .owner _ _ _ _ _ inner => RawCtxForwardOwnerScope.Valid read inner

def FamilyValid (read : RawCtxReceive.FrameDecoder) : FamilyContext M P I D K Result S B → Prop
  | .server _ _ _ _ inner => ServerValid read inner
  | .beacon _ _ _ _ _ _ inner => RawCtxForwardOwnerScope.Valid read inner

def LiveValid (read : RawCtxReceive.FrameDecoder) : Context M P I D K Result S B → Prop
  | .family _ _ _ inner => FamilyValid read inner

/-- The selected Server owner uses the actual peer lookup and associated data before saving its certified descriptor. -/
theorem server_owner (sender : M → Std.U64) (read : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : RawCtxForwardServer.State M P) (kid : Std.U64)
    (peer : RawCtxGenericRoleStorage.Peer (RawCtxPendingOwnerQueries.Kernel RatchetChain) P)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp RawCtxForwardServer.SourceSpec Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → RawCtxForwardServer.State M P →
      OracleComp (RawCtxForwardServer.Spec M P Result) (Result × RawCtxForwardServer.State M P))
    (later : ∀ reply updated, All (ServerValid read) (after reply updated)) :
    All (ServerValid read) (RawCtxForwardServer.owner sender read request before kid peer outside after) := by
  apply bind_all
  · apply map_all (RawCtxForwardOwnerScope.Valid read) (ServerValid read)
      (fun inner => ServerContext.owner request before kid peer outside inner) (fun _ valid => valid)
    exact RawCtxForwardOwnerScope.program_valid _ _ _ _
  · exact fun value => later value.1 _

/-- Every actual adaptive Server schedule preserves the inner raw admission certificate through peer lookup, routing failures and publication. -/
theorem server_valid (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxForwardServer.SourceSpec Result)
    (before : RawCtxForwardServer.State M P) :
    All (ServerValid read) (RawCtxForwardServer.program sender route read client before) := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [RawCtxForwardServer.program_query]
      rcases request with ⟨plaintext, kid⟩ | raw
      all_goals dsimp only
      all_goals repeat' first | split | exact ih _ _ | apply server_owner
      all_goals exact ih

/-- The actual family Server wrapper retains its literal inner source certificate through indexed installation. -/
theorem family_server (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (request : RawCtxForwardServer.SourceSpec.Domain)
    (before : RawCtxForwardFamily.State M P I D K S B) (index : Fin S)
    (outside : RawCtxForwardServer.SourceSpec.Range request → OracleComp (RawCtxForwardFamily.SourceSpec S B) Result)
    (after : RawCtxForwardServer.SourceSpec.Range request → RawCtxForwardFamily.State M P I D K S B →
      OracleComp (RawCtxForwardFamily.Spec M P I D K Result S B) (Result × RawCtxForwardFamily.State M P I D K S B))
    (later : ∀ reply updated, All (FamilyValid read) (after reply updated)) :
    All (FamilyValid read) (RawCtxForwardFamily.server sender route read request before index outside after) := by
  apply bind_all
  · apply map_all (ServerValid read) (FamilyValid read)
      (fun inner => FamilyContext.server request before index outside inner) (fun _ valid => valid)
    exact server_valid sender route read _ _
  · exact fun value => later value.1 _

/-- Established Beacons retain their actual admitted owner descriptor, while every inactive phase follows the original continuation without a descriptor. -/
theorem family_beacon (read : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain)
    (before : RawCtxForwardFamily.State M P I D K S B) (index : Fin B)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (RawCtxForwardFamily.SourceSpec S B) Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → RawCtxForwardFamily.State M P I D K S B →
      OracleComp (RawCtxForwardFamily.Spec M P I D K Result S B) (Result × RawCtxForwardFamily.State M P I D K S B))
    (later : ∀ reply updated, All (FamilyValid read) (after reply updated)) :
    All (FamilyValid read) (RawCtxForwardFamily.beacon read request before index outside after) := by
  cases active : (before.2 index).beacon.phase
  all_goals simp only [RawCtxForwardFamily.beacon, active]
  all_goals first | exact later _ _ | apply bind_all
  case established.first =>
    apply map_all (RawCtxForwardOwnerScope.Valid read)
    · exact fun _ valid => valid
    · exact RawCtxForwardOwnerScope.program_valid _ _ _ _
  case established.later => exact fun value => later value.1 _

/-- All descriptors in the actual mixed role-family schedule retain parser and target provenance, without an honest-owner, successful-opening or bounded-client premise. -/
theorem family_valid (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (client : OracleComp (RawCtxForwardFamily.SourceSpec S B) Result)
    (before : RawCtxForwardFamily.State M P I D K S B) :
    All (FamilyValid read) (RawCtxForwardFamily.program sender route read client before) := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [RawCtxForwardFamily.program_query]
      rcases request with ⟨index, request⟩ | (⟨index, request⟩ | publicQuery)
      all_goals dsimp only
      · exact family_server sender route read request before index outside _ ih
      · exact family_beacon read request before index outside _ ih
      · rw [query_all]
        exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply before⟩

/-- Adaptive records and reveals keep every carried raw admission certificate through the actual disclosure history and role-family continuation. -/
theorem live_valid (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (client : OracleComp (RawCtxForwardLive.SourceSpec S B) Result)
    (before : RawCtxForwardLive.State M P I D K S B) :
    All (LiveValid read) (RawCtxForwardLive.program sender route read client before) := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [RawCtxForwardLive.program_query]
      cases request with
      | inl request =>
          unfold RawCtxForwardLive.family
          apply bind_all
          · apply lift_all (FamilyValid read) (LiveValid read)
              (fun inner => Context.family request before.2 outside inner) (fun _ valid => valid)
            exact family_valid sender route read _ _
          · exact fun result => ih result.1 _
      | inr request =>
          exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply _⟩

/-- Any supported scan of the complete original record/reveal schedule returns its actual certified descriptor, preserving the chosen role and retained history. -/
theorem carried_valid {State : Type} (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (client : OracleComp (RawCtxForwardLive.SourceSpec S B) Result)
    (before : RawCtxForwardLive.State M P I D K S B)
    (chosen : (RawCtxForwardLive.Base S B).Domain → State → Bool)
    (selection : ∀ query state, chosen query state = true → RawCtxPendingFamilyLiveTails.selected query = true)
    (impl : QueryImpl (RawCtxForwardLive.Base S B) (StateT State ProbComp)) (initial reached : State)
    (context : Context M P I D K Result S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan RawCtxPendingFamilyLiveTails.selected chosen selection impl
        (RawCtxForwardLive.program sender route read client before)
        (RawCtxForwardLive.program_covered sender route read client before) initial)) :
    LiveValid read context :=
  scan_all RawCtxPendingFamilyLiveTails.selected chosen selection impl (LiveValid read) _
    (RawCtxForwardLive.program_covered sender route read client before) (live_valid sender route read client before)
    initial reached context supported

end BeaconcryptCore.Computational.RawCtxForwardRoleScope

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleScope.server_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleScope.server_owner

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleScope.server_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleScope.server_valid

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleScope.family_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleScope.family_server

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleScope.family_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleScope.family_beacon

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleScope.family_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleScope.family_valid

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleScope.live_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleScope.live_valid

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleScope.carried_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleScope.carried_valid
