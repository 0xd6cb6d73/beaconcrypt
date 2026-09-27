import BeaconcryptCore.Computational.RawCtxFamilyStateInvariant

/-!
Private owner labels are installed from the original finite family indices and Server peer routes. They are carried by the original kernel callbacks and cannot be inferred from an associated-data value, key or KDF address. The complete no-install LIVE frontend preserves the label at each original lookup, including inactive phases and rejected requests. A later installation must separately attach its new cryptographic origin; these route labels alone do not identify an installation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxOwnerLabels
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open RawCtxProtocolReveals (Owner)
variable {Kernel State M P I D K Result : Type} {S B : Nat}

abbrev Labelled (Kernel : Type) (S B : Nat) := Owner S B × Kernel

def attach (roles : Roles Kernel M P I D K S B) : Roles (Labelled Kernel S B) M P I D K S B :=
  (fun index =>
    let entry := roles.1 index
    ⟨⟨entry.server.identity, fun peer => (entry.server.peers peer).map
      (mapPeer (fun kernel => (Owner.server index peer, kernel))), entry.server.metadata⟩, entry.rawAttempts⟩,
   fun index => mapBeacon (fun kernel => (Owner.beacon index, kernel)) (roles.2 index))

/-- Labels come from the original successful owner lookup, including the exact Server peer index. -/
theorem selected (owner : Owner S B) (roles : Roles Kernel M P I D K S B) :
    selectedKernel owner (attach roles) = (selectedKernel owner roles).map (fun kernel => (owner, kernel)) := by
  cases owner with
  | server index peer => simp [selectedKernel, attach, mapPeer, Option.map_map, Function.comp_def]
  | beacon index =>
    cases phase : (roles.2 index).beacon.phase <;>
      simp [selectedKernel, attach, mapBeacon, mapPhase, phase]

/-- Erasing route labels recovers every original role field and kernel. -/
theorem forget_attach (roles : Roles Kernel M P I D K S B) :
    mapRoles Prod.snd (attach roles) = roles := by
  apply Prod.ext
  · funext index
    simp only [mapRoles, attach, mapServer, Option.map_map]
    congr 2
    funext peer
    cases found : (roles.1 index).server.peers peer <;> rfl
  · funext index
    cases phase : (roles.2 index).beacon.phase <;>
      simp [mapRoles, attach, mapBeacon, mapPhase, phase]
    all_goals rw [← phase]

def calls {m : Type → Type*} [Monad m]
    (original : Owner S B → RawCtxChainOwner.Calls Kernel m) :
    RawCtxChainOwner.Calls (Labelled Kernel S B) m where
  receive := fun entry target context =>
    (fun result => ((entry.1, result.1), result.2)) <$> (original entry.1).receive entry.2 target context
  send := fun entry context =>
    (fun result => ((entry.1, result.1), result.2)) <$> (original entry.1).send entry.2 context

/-- The exact receive callback preserves its supplied outer owner, independent of the primitive reply or state. -/
theorem receive_owner (original : Owner S B → RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (entry : Labelled Kernel S B) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : State) (result : (Labelled Kernel S B × core.option.Option RawCtxWholeOwner.Decrypted) × State)
    (supported : result ∈ support (((calls original).receive entry target context).run state)) :
    result.1.1.1 = entry.1 := by
  simp only [calls, StateT.run_map, support_map] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  rfl

/-- The exact send callback retains the outer owner even when the optional writer result is absent. -/
theorem send_owner (original : Owner S B → RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (entry : Labelled Kernel S B) (context : RawCtxSourceSend.SealContext)
    (state : State) (result : (Labelled Kernel S B × Option RawCtxSourceSend.Encrypted) × State)
    (supported : result ∈ support (((calls original).send entry context).run state)) :
    result.1.1.1 = entry.1 := by
  simp only [calls, StateT.run_map, support_map] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  rfl

private def rules (original : Owner S B → RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (selected : Owner S B) :
    RawCtxFamilyStateInvariant.Rules (calls original) (fun _ _ => True)
      (fun kernel _ => kernel.1 = selected) where
  refl := fun _ => trivial
  trans := fun _ _ _ _ _ => trivial
  mono := fun _ _ _ _ valid => valid
  receive := fun entry target context state result supported =>
    ⟨trivial, fun valid => (receive_owner original entry target context state result supported).trans valid⟩
  send := fun entry context state result supported =>
    ⟨trivial, fun valid => (send_owner original entry context state result supported).trans valid⟩

/-- Every reached lookup in the complete original no-install LIVE schedule retains its actual route label, with all callback and public state arbitrary. -/
theorem schedule_owner (original : Owner S B → RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (Labelled Kernel S B) S B) (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (roles : Roles Kernel M P I D K S B) (history : RawCtxProtocolReveals.History S B) (state : State)
    (result : (Result × RawCtxGenericFamilyLive.State (Labelled Kernel S B) M P I D K S B) × State)
    (supported : result ∈ support (((simulateQ (RawCtxGenericFamilyLive.impl (calls original)
      publicCalls reader sender route decode) client).run (attach roles, history)).run state))
    (owner : Owner S B) (kernel : Labelled Kernel S B)
    (present : selectedKernel owner result.1.2.1 = some kernel) : kernel.1 = owner := by
  have preserved := (RawCtxFamilyStateInvariant.schedule (calls original) (fun _ _ => True)
    (fun kernel _ => kernel.1 = owner) (rules original owner) publicCalls (fun _ _ _ _ => trivial)
    reader (fun _ _ _ _ => trivial) sender route decode client (attach roles, history) state result supported owner).2
  apply preserved ?_ kernel present
  intro before found
  rw [selected] at found
  obtain ⟨old, _, rfl⟩ := Option.map_eq_some_iff.mp found
  rfl

def reader {m : Type → Type*} (original : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) m) :
    QueryImpl (RawCtxGenericFamilyRead.ReadSpec (Labelled Kernel S B) S B) m :=
  fun query => original (query.1, query.2.map Prod.snd)

/-- The private labels erase from the whole original adaptive source program, including the full role family and exact read history. -/
theorem schedule_source {m : Type → Type*} [Monad m] [LawfulMonad m]
    (original : RawCtxChainOwner.Calls Kernel m)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (originalReader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) m)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (roles : Roles Kernel M P I D K S B) (history : RawCtxProtocolReveals.History S B) :
    (simulateQ (RawCtxGenericFamilyLive.impl original publicCalls originalReader sender route decode) client).run (roles, history) =
    Prod.map id (RawCtxGenericFamilyLive.mapState Prod.snd) <$>
      (simulateQ (RawCtxGenericFamilyLive.impl (calls (fun _ => original)) publicCalls (reader originalReader)
        sender route decode) client).run (attach roles, history) := by
  have same := RawCtxGenericFamilyLive.schedule_map Prod.snd (calls (fun (_ : Owner S B) => original))
    original publicCalls (reader originalReader) originalReader
    (fun entry target context => by simp [calls, Functor.map_map, Prod.map_def])
    (fun entry context => by simp [calls, Functor.map_map, Prod.map_def])
    (fun _ _ => rfl) sender route decode client (attach roles, history)
  simpa only [RawCtxGenericFamilyLive.mapState, forget_attach] using same

/-- Pure route labels preserve every selective underlying query bound; they do not make original callback work free. -/
theorem source_queries {ι : Type} {base : OracleSpec ι}
    (original : RawCtxChainOwner.Calls Kernel (OracleComp base))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp base))
    (originalReader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (OracleComp base))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (roles : Roles Kernel M P I D K S B) (history : RawCtxProtocolReveals.History S B)
    (select : base.Domain → Prop) [DecidablePred select] (bound : Nat) :
    ((simulateQ (RawCtxGenericFamilyLive.impl original publicCalls originalReader sender route decode) client).run
      (roles, history)).IsQueryBoundP select bound ↔
    ((simulateQ (RawCtxGenericFamilyLive.impl (calls (fun _ => original)) publicCalls (reader originalReader)
      sender route decode) client).run (attach roles, history)).IsQueryBoundP select bound := by
  rw [schedule_source original publicCalls originalReader sender route decode client roles history,
    isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxOwnerLabels

/-- info: 'BeaconcryptCore.Computational.RawCtxOwnerLabels.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerLabels.selected

/-- info: 'BeaconcryptCore.Computational.RawCtxOwnerLabels.forget_attach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerLabels.forget_attach

/-- info: 'BeaconcryptCore.Computational.RawCtxOwnerLabels.receive_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerLabels.receive_owner

/-- info: 'BeaconcryptCore.Computational.RawCtxOwnerLabels.send_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerLabels.send_owner

/-- info: 'BeaconcryptCore.Computational.RawCtxOwnerLabels.schedule_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerLabels.schedule_owner

/-- info: 'BeaconcryptCore.Computational.RawCtxOwnerLabels.schedule_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerLabels.schedule_source

/-- info: 'BeaconcryptCore.Computational.RawCtxOwnerLabels.source_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOwnerLabels.source_queries
