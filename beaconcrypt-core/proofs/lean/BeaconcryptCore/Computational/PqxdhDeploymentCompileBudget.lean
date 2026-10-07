-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileGame

/-! Budget transport of the CE-3 trial: query caps of the compiled program in the fourteen source14 query kinds, from per-command caps of the deployment adversary. Every coin and registration, HMAC and BLAKE2b command is forwarded once; a create with a wrong-width pin issues nothing. A Server record command issues at most one Server kernel reveal and at most one BLAKE2b query; a Beacon record command issues at most one established-kernel read and at most one BLAKE2b query. HKDF, AEAD and the frame writer are local work and are not charged as queries. No other field read is ever issued. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentCompile (Local compileImpl compile)
open PqxdhDeploymentRecordCache (SourceSpec localPrimitives)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-- The deployment command classes: coin, create, bundle, accept, build, finish, HMAC, BLAKE2b, Server send, Server raw receive, Beacon send and Beacon raw receive. -/
def commandKind : PqxdhDeploymentInterface.Spec.Domain → Fin 12
  | .inl _ => 0
  | .inr (.create _ _) => 1
  | .inr (.bundle _) => 2
  | .inr (.accept _) => 3
  | .inr (.build _ _) => 4
  | .inr (.finish _ _) => 5
  | .inr (.hmac _ _) => 6
  | .inr (.hash _) => 7
  | .inr (.serverSend _ _) => 8
  | .inr (.serverRaw _) => 9
  | .inr (.beaconSend _ _) => 10
  | .inr (.beaconRaw _ _) => 11

/-- One unit of a source kind. -/
def unit (kind target : SourceKind) : Nat := if kind = target then 1 else 0

/-- Source queries of one kind issued by one deployment command of each class. -/
def cost (kind : SourceKind) : Fin 12 → Nat :=
  ![unit kind (.inl 0), unit kind (.inl 1), unit kind (.inl 2), unit kind (.inl 3), unit kind (.inl 4),
    unit kind (.inl 5), unit kind (.inl 6), unit kind (.inl 7),
    unit kind (.inl 8) + unit kind (.inl 7), unit kind (.inl 8) + unit kind (.inl 7),
    unit kind (.inr 4) + unit kind (.inl 7), unit kind (.inr 4) + unit kind (.inl 7)]

/-- Locally answered record primitives issue one BLAKE2b command per commitment hash and nothing else. -/
theorem local_bound {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (kind : SourceKind) (work : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (bound : Nat) (hashes : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) bound) :
    (simulateQ (localPrimitives setup codec) work).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (unit kind (.inl 7) * bound) := by
  induction work using OracleComp.inductionOn generalizing bound with
  | pure value =>
      simp only [simulateQ_pure]
      trivial
  | query_bind query next ih =>
      simp only [isQueryBoundP_query_bind_iff] at hashes
      obtain ⟨allowed, rest⟩ := hashes
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rcases query with request | input | input | bytes | frame
      · simp only [localPrimitives, pure_bind]
        have kindEq : RawCtxMixedOwner.callKind (Sum.inl request) = .kdf := rfl
        have h := rest (RawCtxSourceHkdf.response setup.source.crypto request)
        simp only [kindEq, reduceCtorEq, ite_false] at h
        exact ih _ bound h
      · simp only [localPrimitives, pure_bind]
        have kindEq : RawCtxMixedOwner.callKind (Sum.inr (Sum.inl input)) = .sealing := rfl
        have h := rest (some (setup.source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext))
        simp only [kindEq, reduceCtorEq, ite_false] at h
        exact ih _ bound h
      · simp only [localPrimitives, pure_bind]
        have kindEq : RawCtxMixedOwner.callKind (Sum.inr (Sum.inr (Sum.inl input))) = .opening := rfl
        have h := rest (RawCtxSourceOpen.baseOpen setup.source.crypto input)
        simp only [kindEq, reduceCtorEq, ite_false] at h
        exact ih _ bound h
      · have hashKind : RawCtxMixedOwner.callKind (Sum.inr (Sum.inr (Sum.inr (Sum.inl bytes)))) = .hash := rfl
        simp only [hashKind, ite_true, not_true_eq_false, false_or] at allowed rest
        simp only [localPrimitives, PqxdhDeploymentRecordCache.hashQuery, bind_map_left, isQueryBoundP_query_bind_iff]
        have sourceHash : sourceKind (KemSK := KemSK) (Sum.inl (Sum.inr (PqxdhRegistrationSchedule.Request.hash bytes))) =
            .inl 7 := rfl
        by_cases same : kind = .inl 7
        · subst same
          refine ⟨Or.inr (by simp [unit, allowed]), fun digest => ?_⟩
          have step := ih (some digest.toList) (bound - 1) (rest (some digest.toList))
          simpa [unit, sourceHash] using step
        · have notHash : ¬ sourceKind (KemSK := KemSK) (Sum.inl (Sum.inr (PqxdhRegistrationSchedule.Request.hash bytes))) =
              kind := by
            rw [sourceHash]
            exact fun equal => same equal.symm
          refine ⟨Or.inl notHash, fun digest => ?_⟩
          have step := ih (some digest.toList) (bound - 1) (rest (some digest.toList))
          simpa [unit, same, notHash] using step
      · simp only [localPrimitives, pure_bind]
        have kindEq : RawCtxMixedOwner.callKind (Sum.inr (Sum.inr (Sum.inr (Sum.inr frame)))) = .writer := rfl
        have h := rest (codec.frameWrite frame)
        simp only [kindEq, reduceCtorEq, ite_false] at h
        exact ih _ bound h

/-- The frame log issues exactly the record program's own primitive calls, so every query cap of the program carries over to the logged program. -/
theorem logged_bound {Result : Type} (predicate : RawCtxMixedOwner.NativeSpec.Domain → Prop) [DecidablePred predicate]
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (bound : Nat) (frames : List PqxdhDeploymentNative.Frame)
    (bounded : work.IsQueryBoundP predicate bound) :
    ((simulateQ PqxdhDeploymentNative.frameLog work).run frames).IsQueryBoundP predicate bound := by
  induction work using OracleComp.inductionOn generalizing bound frames with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      rcases query with request | input | input | bytes | frame
      · simp only [PqxdhDeploymentNative.frameLog, StateT.run_lift, bind_assoc, pure_bind]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨allowed, fun reply => ih reply _ _ (rest reply)⟩
      · simp only [PqxdhDeploymentNative.frameLog, StateT.run_lift, bind_assoc, pure_bind]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨allowed, fun reply => ih reply _ _ (rest reply)⟩
      · simp only [PqxdhDeploymentNative.frameLog, StateT.run_lift, bind_assoc, pure_bind]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨allowed, fun reply => ih reply _ _ (rest reply)⟩
      · simp only [PqxdhDeploymentNative.frameLog, StateT.run_lift, bind_assoc, pure_bind]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨allowed, fun reply => ih reply _ _ (rest reply)⟩
      · change OracleComp.IsQueryBoundP ((fun reply => (reply, frames ++ [frame])) <$>
          (RawCtxMixedOwner.NativeSpec.query (.inr (.inr (.inr (.inr frame)))) : OracleComp RawCtxMixedOwner.NativeSpec _)
            >>= _) _ _
        rw [bind_map_left, isQueryBoundP_query_bind_iff]
        exact ⟨allowed, fun reply => ih reply _ _ (rest reply)⟩

/-- One source14 query, with its reply mapped, costs one query of its own kind. -/
theorem single_bound {Result : Type} (kind : SourceKind) (request : (SourceSpec KemSK).Domain)
    (map : (SourceSpec KemSK).Range request → Result) (bound : Nat)
    (enough : unit kind (sourceKind (KemSK := KemSK) request) ≤ bound) :
    (map <$> (liftM ((SourceSpec KemSK).query request) : OracleComp (SourceSpec KemSK) _)).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) bound := by
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro same
  simp only [unit, same, ite_true] at enough
  omega

/-- A Server record command issues at most one BLAKE2b commitment query. -/
theorem server_hashes (senderId : Unit → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : RawCtxServerRouting.State Unit Unit) :
    ((RawCtxServerMixed.serverImpl senderId route decode query).run state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = .hash) 1 := by
  rcases query with ⟨plaintext, kid⟩ | raw
  · exact RawCtxServerMixed.send_bound senderId plaintext kid state .hash
  · exact RawCtxServerMixed.raw_bound route decode raw state .hash

/-- A Beacon record command issues at most one BLAKE2b commitment query. -/
theorem beacon_hashes {I D K : Type} (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxBeaconLifecycle.State I D K) :
    ((RawCtxBeaconLifecycle.beaconImpl decode query).run state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = .hash) 1 := by
  have bound := RawCtxBeaconLifecycle.step_bound decode query state .hash
  rcases query with plaintext | raw <;> exact bound

/-- The kernel of a Server peer costs at most one Server kernel reveal. -/
theorem peerKernel_bound (kind : SourceKind) (copies : Local) (kid : Std.U64) :
    (PqxdhDeploymentCompile.peerKernel (KemSK := KemSK) copies kid).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (unit kind (.inl 8)) := by
  unfold PqxdhDeploymentCompile.peerKernel
  cases copies.peers kid with
  | some current => trivial
  | none =>
      have bound := single_bound (KemSK := KemSK) kind (.inl (.inr (.reveal kid))) id (unit kind (.inl 8)) (le_refl _)
      simp only [id_map] at bound
      exact bound

/-- The kernel of an owner costs at most one established-kernel read. -/
theorem ownerKernel_bound (kind : SourceKind) (copies : Local) (index : Nat) :
    (PqxdhDeploymentCompile.ownerKernel (KemSK := KemSK) copies index).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (unit kind (.inr 4)) := by
  unfold PqxdhDeploymentCompile.ownerKernel
  cases copies.owners index with
  | some current => trivial
  | none => exact single_bound kind (.inr (index, .kernel)) _ (unit kind (.inr 4)) (le_refl _)

/-- A compiled Server record command costs at most one Server kernel reveal and one BLAKE2b query. -/
theorem serverLocal_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (kind : SourceKind) (query : RawCtxServerMixed.SourceSpec.Domain)
    (copies : Local) :
    ((PqxdhDeploymentCompile.serverLocal setup codec route query).run copies).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (unit kind (.inl 8) + unit kind (.inl 7)) := by
  cases target : PqxdhDeploymentCompile.serverTarget route query with
  | none =>
      rw [PqxdhDeploymentCompileRecords.serverLocal_none setup codec route query copies target, isQueryBoundP_map_iff]
      have bound := local_bound setup codec kind _ 1 (logged_bound _ _ 1 [] (server_hashes (fun _ => setup.serverKeyId)
        route codec.frameRead query (PqxdhDeploymentCompile.localServer codec copies.log 0#u64 none copies.serverRaw)))
      exact bound.mono (by omega)
  | some kid =>
      rw [PqxdhDeploymentCompileRecords.serverLocal_some setup codec route query copies kid target]
      refine isQueryBoundP_bind (peerKernel_bound kind copies kid) fun kernel _ => ?_
      rw [isQueryBoundP_map_iff]
      have bound := local_bound setup codec kind _ 1 (logged_bound _ _ 1 [] (server_hashes (fun _ => setup.serverKeyId)
        route codec.frameRead query (PqxdhDeploymentCompile.localServer codec copies.log kid kernel copies.serverRaw)))
      exact bound.mono (by omega)

/-- A compiled Beacon record command costs at most one established-kernel read and one BLAKE2b query. -/
theorem beaconLocal_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (kind : SourceKind)
    (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) (copies : Local) :
    ((PqxdhDeploymentCompile.beaconLocal setup codec index query).run copies).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (unit kind (.inr 4) + unit kind (.inl 7)) := by
  by_cases inside : index < copies.log.owners.length
  · rw [PqxdhDeploymentCompileRecords.beaconLocal_present setup codec index query copies inside]
    refine isQueryBoundP_bind (ownerKernel_bound kind copies index) fun kernel _ => ?_
    rw [isQueryBoundP_map_iff]
    have bound := local_bound setup codec kind _ 1 (logged_bound _ _ 1 [] (beacon_hashes codec.frameRead query
      (PqxdhDeploymentCompile.localOwner codec copies.log index kernel (copies.ownerRaw index))))
    exact bound.mono (by omega)
  · rw [PqxdhDeploymentCompileRecords.beaconLocal_absent setup codec index query copies inside]
    trivial

/-- Every compiled command issues at most its class's source queries of each kind. -/
theorem step_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (kind : SourceKind) (query : PqxdhDeploymentInterface.Spec.Domain)
    (copies : Local) :
    ((compileImpl setup codec route query).run copies).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (cost kind (commandKind query)) := by
  rcases query with coin | command
  · simp only [compileImpl, StateT.run_lift, bind_pure_comp]
    exact single_bound kind (.inl (.inl coin)) _ _ (le_refl _)
  · cases command with
    | create pin keyId =>
        change (match PqxdhDeploymentInterface.parsePin pin with
          | none => pure (none, copies)
          | some word => do
              let index ← PqxdhDeploymentCompile.forward (KemSK := KemSK) (.create word keyId)
              pure (some index, _)).IsQueryBoundP _ _
        cases PqxdhDeploymentInterface.parsePin pin with
        | none => trivial
        | some word =>
            simp only [PqxdhDeploymentCompile.forward, bind_pure_comp]
            exact single_bound kind _ _ _ (le_refl _)
    | serverSend kid plaintext => exact serverLocal_bound setup codec route kind (.inl (plaintext, kid)) copies
    | serverRaw raw => exact serverLocal_bound setup codec route kind (.inr raw) copies
    | beaconSend index plaintext => exact beaconLocal_bound setup codec kind index (.inl plaintext) copies
    | beaconRaw index raw => exact beaconLocal_bound setup codec kind index (.inr raw) copies
    | hmac key message =>
        simp only [compileImpl, PqxdhDeploymentCompile.forward, StateT.run_lift, bind_pure_comp]
        exact single_bound kind _ _ _ (le_refl _)
    | hash bytes =>
        simp only [compileImpl, PqxdhDeploymentCompile.forward, StateT.run_lift, bind_pure_comp]
        exact single_bound kind _ _ _ (le_refl _)
    | _ =>
        simp only [compileImpl, PqxdhDeploymentCompile.forwardLogged, PqxdhDeploymentCompile.forward, StateT.run,
          bind_pure_comp]
        exact single_bound kind _ _ _ (le_refl _)

/-- Budget transport: if the deployment adversary makes at most `budget c` commands of each class `c`, the compiled program makes at most `∑ c, cost kind c * budget c` source14 queries of each kind. This is the `certified` premise of the KEM and root theorems for the compiled program. -/
theorem compile_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (adversary : OracleComp PqxdhDeploymentInterface.Spec X)
    (budget : Fin 12 → Nat)
    (bounded : ∀ command, adversary.IsQueryBoundP (fun query => commandKind query = command) (budget command))
    (kind : SourceKind) :
    (compile setup codec route adversary).IsQueryBoundP (fun request => sourceKind (KemSK := KemSK) request = kind)
      (∑ command, cost kind command * budget command) :=
  FinitePartitionQueryBounds.weighted_bound commandKind (cost kind) budget (compileImpl setup codec route)
    (fun request => sourceKind (KemSK := KemSK) request = kind) adversary bounded
    (fun query copies => step_bound setup codec route kind query copies) Local.empty

end BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.local_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.logged_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.logged_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.single_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.single_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.server_hashes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.server_hashes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.beacon_hashes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.beacon_hashes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.peerKernel_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.peerKernel_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.ownerKernel_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.ownerKernel_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.serverLocal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.serverLocal_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.beaconLocal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.beaconLocal_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.step_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget.compile_bound
