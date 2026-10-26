import BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates
import BeaconcryptCore.Computational.RawCtxForwardFamily
import BeaconcryptCore.Computational.RawCtxQuietFamilyTails

/-!
The forward Server and role-family compilers construct their actual descriptors with zero-query captured inner source continuations when executing one source request. These certificates concern the literal annotated values carried by the execution; no descriptor is reconstructed from an existential equality of frames. Every routing, role phase and complete reply remains present.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardRoleCertificates
open RawCtxForwardTags RawCtxSelectedFamilyContext
variable {M P I D K Result : Type} {S B : Nat}

/-- An actual zero-query Server continuation executes its pure original return and carries no new descriptor. -/
theorem server_zero (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxForwardServer.SourceSpec Result)
    (bounded : client.IsTotalQueryBound 0) (state : RawCtxForwardServer.State M P) :
    All RawCtxQuietServerTails.Quiet (RawCtxForwardServer.program sender route decode client state) := by
  obtain ⟨value, rfl⟩ := RawCtxQuietOwnerTails.zero_pure client bounded
  trivial

/-- An actual zero-query family continuation carries no new role descriptor and retains its full original return. -/
theorem family_zero (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (RawCtxForwardFamily.SourceSpec S B) Result)
    (bounded : client.IsTotalQueryBound 0) (state : RawCtxForwardFamily.State M P I D K S B) :
    All RawCtxQuietFamilyTails.Quiet (RawCtxForwardFamily.program sender route decode client state) := by
  obtain ⟨value, rfl⟩ := RawCtxQuietOwnerTails.zero_pure client bounded
  trivial

/-- Wrapping one certified original owner retains its literal descriptor and the zero-query outside Server continuation. -/
theorem server_owner (sender : M → Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : RawCtxForwardServer.State M P) (kid : Std.U64)
    (peer : RawCtxGenericRoleStorage.Peer (RawCtxPendingOwnerQueries.Kernel RatchetChain) P)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp RawCtxForwardServer.SourceSpec Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → RawCtxForwardServer.State M P →
      OracleComp (RawCtxForwardServer.Spec M P Result) (Result × RawCtxForwardServer.State M P))
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (inside : All RawCtxQuietOwnerTails.Quiet
      (RawCtxForwardOwner.program (sender before.server.metadata) decode
        (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request))
        (RawCtxGenericServer.selectedOwner kid (RawCtxServerRouting.associatedBytes before.server.identity peer.identity) peer before.rawAttempts)))
    (later : ∀ reply updated, All RawCtxQuietServerTails.Quiet (after reply updated)) :
    All RawCtxQuietServerTails.Quiet (RawCtxForwardServer.owner sender decode request before kid peer outside after) := by
  apply bind_all
  · exact map_all RawCtxQuietOwnerTails.Quiet RawCtxQuietServerTails.Quiet _
      (fun inner valid => ⟨quiet, valid⟩) _ inside
  · exact fun value => later value.1 _

/-- Every descriptor actually carried by one Server request has its original quiet owner and Server tails. -/
theorem server_quiet (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxForwardServer.SourceSpec Result)
    (bounded : client.IsTotalQueryBound 1) (state : RawCtxForwardServer.State M P) :
    All RawCtxQuietServerTails.Quiet (RawCtxForwardServer.program sender route decode client state) := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind request outside ih =>
      have quiet : ∀ reply, (outside reply).IsTotalQueryBound 0 := by
        simpa only [IsTotalQueryBound, isQueryBound_query_bind_iff, Nat.sub_self, zero_lt_one, true_and] using bounded
      have later : ∀ reply (updated : RawCtxForwardServer.State M P),
          All RawCtxQuietServerTails.Quiet (RawCtxForwardServer.program sender route decode (outside reply) updated) :=
        fun reply updated => server_zero sender route decode _ (quiet reply) updated
      rw [RawCtxForwardServer.program_query]
      rcases request with ⟨plaintext, kid⟩ | raw
      all_goals dsimp only
      all_goals repeat' first | split | exact later _ _ | apply server_owner
      all_goals first | exact quiet | exact later | apply RawCtxForwardOwnerCertificates.program_quiet
      all_goals exact ⟨Nat.zero_lt_one, fun _ => True.intro⟩

/-- The selected Server's literal quiet descriptor retains the original zero-query family tail through its actual indexed installer. -/
theorem family_server (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : RawCtxForwardServer.SourceSpec.Domain)
    (before : RawCtxForwardFamily.State M P I D K S B) (index : Fin S)
    (outside : RawCtxForwardServer.SourceSpec.Range request → OracleComp (RawCtxForwardFamily.SourceSpec S B) Result)
    (after : RawCtxForwardServer.SourceSpec.Range request → RawCtxForwardFamily.State M P I D K S B →
      OracleComp (RawCtxForwardFamily.Spec M P I D K Result S B) (Result × RawCtxForwardFamily.State M P I D K S B))
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (later : ∀ reply updated, All RawCtxQuietFamilyTails.Quiet (after reply updated)) :
    All RawCtxQuietFamilyTails.Quiet (RawCtxForwardFamily.server sender route decode request before index outside after) := by
  apply bind_all
  · apply map_all RawCtxQuietServerTails.Quiet RawCtxQuietFamilyTails.Quiet
      (fun inner => FamilyContext.server request before index outside inner) (fun inner valid => ⟨quiet, valid⟩)
    exact server_quiet sender route decode (RawCtxForwardServer.SourceSpec.query request)
      ⟨Nat.zero_lt_one, fun _ => True.intro⟩ _
  · exact fun value => later value.1 _

/-- Every established Beacon descriptor carries its actual quiet owner/family tails; inactive roles return through the same original outside continuation. -/
theorem family_beacon (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain)
    (before : RawCtxForwardFamily.State M P I D K S B) (index : Fin B)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp (RawCtxForwardFamily.SourceSpec S B) Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → RawCtxForwardFamily.State M P I D K S B →
      OracleComp (RawCtxForwardFamily.Spec M P I D K Result S B) (Result × RawCtxForwardFamily.State M P I D K S B))
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (later : ∀ reply updated, All RawCtxQuietFamilyTails.Quiet (after reply updated)) :
    All RawCtxQuietFamilyTails.Quiet (RawCtxForwardFamily.beacon decode request before index outside after) := by
  cases active : (before.2 index).beacon.phase
  all_goals simp only [RawCtxForwardFamily.beacon, active]
  all_goals first | exact later _ _ | apply bind_all
  case established.first =>
    apply map_all RawCtxQuietOwnerTails.Quiet
    · exact fun _ valid => ⟨quiet, valid⟩
    · apply RawCtxForwardOwnerCertificates.program_quiet
      exact ⟨Nat.zero_lt_one, fun _ => True.intro⟩
  case established.later => exact fun value => later value.1 _

/-- One original family request constructs its exact quiet role descriptors under every source reply, phase, routing and publication outcome. -/
theorem family_quiet (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (RawCtxForwardFamily.SourceSpec S B) Result)
    (bounded : client.IsTotalQueryBound 1) (state : RawCtxForwardFamily.State M P I D K S B) :
    All RawCtxQuietFamilyTails.Quiet (RawCtxForwardFamily.program sender route decode client state) := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind request outside ih =>
      have quiet : ∀ reply, (outside reply).IsTotalQueryBound 0 := by
        simpa only [IsTotalQueryBound, isQueryBound_query_bind_iff, Nat.sub_self, zero_lt_one, true_and] using bounded
      have later : ∀ reply (updated : RawCtxForwardFamily.State M P I D K S B),
          All RawCtxQuietFamilyTails.Quiet (RawCtxForwardFamily.program sender route decode (outside reply) updated) :=
        fun reply updated => family_zero sender route decode _ (quiet reply) updated
      rw [RawCtxForwardFamily.program_query]
      rcases request with ⟨index, request⟩ | (⟨index, request⟩ | publicQuery)
      all_goals dsimp only
      · exact family_server sender route decode request state index outside _ quiet later
      · exact family_beacon decode request state index outside _ quiet later
      · rw [query_all]
        exact ⟨(fun _ impossible => by cases impossible), fun reply => later reply state⟩

end BeaconcryptCore.Computational.RawCtxForwardRoleCertificates

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.server_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.server_zero

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.family_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.family_zero

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.server_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.server_owner

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.server_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.server_quiet

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.family_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.family_server

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.family_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.family_beacon

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.family_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardRoleCertificates.family_quiet
