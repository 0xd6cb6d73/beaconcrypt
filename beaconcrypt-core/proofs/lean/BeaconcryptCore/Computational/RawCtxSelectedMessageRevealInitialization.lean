import BeaconcryptCore.Computational.RawCtxSelectedMessageReveals

/-!
The selected-message simulator can begin from the complete actual prior family and reveal history by marking all existing material as known. This embedding preserves the original native state for every selected key, even if an old value happens to equal it. Existing disclosures are neither erased nor relabelled hidden; they remain explicit candidates for the CTX prefix probes.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization
open PqxdhSecretInputKdf RawCtxSelectedMessageKey RawCtxSelectedMessageFreshness RawCtxSelectedMessageReveals
open RawCtxMaterialInterpretation
variable {M P I D K : Type} {S B : Nat}

def fromObservation : RawCtxProtocolReveals.Observation S B → RawCtxSelectedMessageFreshness.Observation S B
  | ⟨.sendChain owner, reply⟩ => ⟨.sendChain owner, reply⟩
  | ⟨.receiveChain owner, reply⟩ => ⟨.receiveChain owner, reply⟩
  | ⟨.skippedKey owner sequence, .None⟩ => ⟨.skippedKey owner sequence, .None⟩
  | ⟨.skippedKey owner sequence, .Some material⟩ => ⟨.skippedKey owner sequence, .Some (.known material)⟩

def fromHistory (history : RawCtxProtocolReveals.History S B) : History S B :=
  ⟨history.position, history.observations.map (fun entry => (entry.1, fromObservation entry.2))⟩

/-- Every prior read keeps its original owner, optional native value and nonce even if it aliases the later selected key. -/
theorem observation_roundtrip (key : RootOutput) (observation : RawCtxProtocolReveals.Observation S B) :
    interpretObservation key (fromObservation observation) = observation := by
  rcases observation with ⟨request, reply⟩
  cases request <;> cases reply <;> rfl

/-- The entire original timestamped native history is reconstructed without dropping any disclosure. -/
theorem history_roundtrip (key : RootOutput) (history : RawCtxProtocolReveals.History S B) :
    interpretHistory key (fromHistory history) = history := by
  cases history
  simp only [fromHistory, interpretHistory, List.map_map, Function.comp_def, observation_roundtrip,
    Prod.mk.eta, List.map_id']

def fromKernel (entry : ConcreteRatchetKernel) : Kernel := mapRefined Slot.known entry.refined

def fromState (state : RawCtxProtocolReveals.State M P I D K S B) : RawCtxSelectedMessageReveals.State M P I D K S B :=
  (RawCtxGenericRoleFamily.fromRoles fromKernel state.1, fromHistory state.2)

/-- Every prior cached material and its tag reconstructs the complete original kernel, independently of the later selected key. -/
theorem kernel_roundtrip (key : RootOutput) (entry : ConcreteRatchetKernel) :
    nativeKernel key (fromKernel entry) = entry := by
  cases entry
  simp only [fromKernel, nativeKernel, RawCtxSelectedMessageKey.known_kernel]

/-- The all-known initial representation preserves every actual role, peer, private field, kernel and prior disclosure history. -/
theorem state_roundtrip (key : RootOutput) (state : RawCtxProtocolReveals.State M P I D K S B) :
    nativeState key (fromState state) = state :=
  Prod.ext (RawCtxGenericRoleFamily.roundtrip fromKernel (nativeKernel key) (kernel_roundtrip key) state.1)
    (history_roundtrip key state.2)

/-- Prior native disclosures are all explicit known candidates; coincidental selected-key equality never turns them into hidden-marker reads. -/
theorem observation_fields (observation : RawCtxProtocolReveals.Observation S B) :
    candidates (fromObservation observation) = RawCtxLiveLineage.disclosed observation ∧
      hiddenObservation (fromObservation observation) = false := by
  rcases observation with ⟨request, reply⟩
  cases request <;> cases reply <;> exact ⟨rfl, rfl⟩

/-- Initialization keeps the exact complete prior byte-candidate list and begins with no artificial hidden disclosure. -/
theorem history_fields (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B) :
    known prior (fromHistory history) = RawCtxLiveLineage.known prior history ∧
      hidden (fromHistory history) = false := by
  simp only [known, fromHistory, List.flatMap_map, Function.comp_def, observation_fields,
    RawCtxLiveLineage.known, RawCtxSelectedMessageFreshness.hidden, List.any_map]
  simp

end BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.observation_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.observation_roundtrip
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.history_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.history_roundtrip
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.kernel_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.kernel_roundtrip
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.state_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.state_roundtrip
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.observation_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.observation_fields
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.history_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageRevealInitialization.history_fields
