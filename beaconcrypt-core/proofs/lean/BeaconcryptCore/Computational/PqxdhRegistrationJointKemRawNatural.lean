-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame

/-! Conversions between the tagged program that the real initialized run executes and the Boolean decision program that the raw-ordinal KEM games execute, and the two router facts that the bridge between them uses. The command compilers, the selected-accept exposure and the KEM scan are natural in the client result, so the decision program is the result map of the tagged program at every layer, including the saved continuation of a KEM cut. Under the stopped selected-KEM router, local coins are sampled with the router state unchanged, so finishing a pending KEM cut is one ordinary encapsulation to the requested key followed by the saved continuation; and the router run of a sequential program splits at the bind. No probability is involved and no program is commuted. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural
open PqxdhKemIndCca PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointKemEncapsulation (actual commands)
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointAcceptCutTag (Tag tag decideTag decisionClient)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointAcceptKemCut (hide exposeAt tagged)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R S Result Next : Type}

section Router

variable {κ σ : Type} {spec : OracleSpec κ}

/-- The run of an optional stateful router on a sequential program is the run of the first part followed, from the reached state, by the run of the second part; a stop of the first part stays a stop. -/
theorem router_split (impl : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (work : OracleComp spec Result) (next : Result → OracleComp spec Next) (state : σ) :
    ((simulateQ impl (work >>= next)).run).run state =
      (((simulateQ impl work).run).run state >>= fun reached =>
        reached.1.elim (pure (none, reached.2)) fun value => ((simulateQ impl (next value)).run).run reached.2) := by
  rw [simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply bind_congr
  rintro ⟨_ | value, after⟩ <;> rfl

/-- The run of an optional stateful router is natural in the program result. -/
theorem router_map (impl : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (f : Result → Next) (work : OracleComp spec Result) (state : σ) :
    ((simulateQ impl (f <$> work)).run).run state =
      (fun reached => (reached.1.map f, reached.2)) <$> ((simulateQ impl work).run).run state := by
  rw [simulateQ_map, OptionT.run_map, StateT.run_map]

/-- Every completed result of an optional stateful router run is a result of the original program. -/
theorem router_support (impl : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (work : OracleComp spec Result) (state after : σ) (value : Result)
    (reached : (some value, after) ∈ support (((simulateQ impl work).run).run state)) : value ∈ support work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result =>
    rw [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact (mem_support_pure_iff _ _).mpr rfl
  | query_bind query next ih =>
    rw [router_split, mem_support_bind_iff] at reached
    obtain ⟨⟨_ | answer, middle⟩, _, reached⟩ := reached
    · rw [Option.elim_none, mem_support_pure_iff] at reached
      cases reached
    · rw [Option.elim_some] at reached
      exact (mem_support_bind_iff _ _ _).mpr ⟨answer, mem_support_query query answer, ih answer middle reached⟩

end Router

/-- Under the stopped selected-KEM router, local source coins are sampled exactly, with the router state unchanged and no stop. -/
theorem coins_stopped (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (work : ProbComp Result)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped baseImpl primitives kem selected pairs)
      (PqxdhLiveKemBirth.coins work)).run).run state = (fun value => (some value, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    change ((simulateQ (PqxdhDynamicKemJointRouter.stopped baseImpl primitives kem selected pairs)
      ((PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inl query)) >>= fun answer =>
        PqxdhLiveKemBirth.coins (next answer))).run).run state = _
    rw [router_split]
    simp only [simulateQ_spec_query, PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine,
      OptionT.run_mk, StateT.run, bind_map_left, Option.elim_some, map_bind]
    exact bind_congr fun answer => ih answer

/-- Finishing a pending KEM cut under the stopped selected-KEM router is one ordinary encapsulation to the requested key, through the ambient interpreter and the source reply map, followed by the saved continuation from the reached router state. -/
theorem finish_stopped (setup : Setup baseSpec KemSK) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (request : PqxdhRegistrationJointKemCut.Request)
    (next : PqxdhRegistrationJointKemCut.Reply → OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
      (PqxdhRegistrationJointKemCut.finish setup (.pending request next))).run).run state =
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps request.2) >>=
        fun encapsulated =>
          ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
            (simulateQ (actual setup)
              (next (PqxdhRegistrationJointKemResume.reply encapsulated.1 encapsulated.2)))).run).run state) := by
  change ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
    (PqxdhLiveKemBirth.coins (encapsulate setup request.2) >>= fun answer =>
      simulateQ (actual setup) (next answer))).run).run state = _
  rw [router_split, coins_stopped, bind_map_left]
  simp only [Option.elim_some, encapsulate, simulateQ_map, bind_map_left]
  rfl

/-- Replace the client result of a command outcome, keeping the owners and the native state. -/
def mapOutcome (f : R → S) (outcome : Outcome KemSK R) : Outcome KemSK S :=
  ((f outcome.1.1, outcome.1.2), outcome.2)

/-- The exposed source command compiler is natural in the client result. -/
theorem commands_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (f : R → S) (client : OracleComp (SourceSpec KemSK) R)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    commands setup codec checks identityIndex publicIdentity (f <$> client) owners state =
      mapOutcome f <$> commands setup codec checks identityIndex publicIdentity client owners state := by
  simp only [commands, simulateQ_map, StateT.run_map]
  rfl

/-- The actual source command program is natural in the client result. -/
theorem program_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (f : R → S) (client : OracleComp (SourceSpec KemSK) R)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex publicIdentity (f <$> client)
        owners state =
      mapOutcome f <$> PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex publicIdentity
        client owners state := by
  simp only [PqxdhRegistrationJointKemCommands.program, PqxdhRegistrationJointOpenBackend.compile, simulateQ_map,
    StateT.run_map]
  rfl

/-- The decision program of the KEM games is the result map of the tagged program of the real run under the actual source command compiler. -/
theorem decision_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (decision : X → Bool)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat) (owners : List EncodedEntry) (state : NativeState KemSK) :
    PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex publicIdentity
        (decisionClient decision work index) owners state =
      mapOutcome (decideTag decision) <$> PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex
        publicIdentity (tag work index) owners state :=
  program_map setup codec checks identityIndex publicIdentity (decideTag decision) (tag work index) owners state

/-- Hiding exposed encapsulations is natural in the result. -/
theorem hide_map (setup : Setup baseSpec KemSK) (f : Result → Next)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) :
    hide setup (f <$> work) = f <$> hide setup work := by
  simp only [hide, simulateQ_map]

/-- Exposing only the selected accept is natural in the observation of the tagged result: a composed observation is the result map of the inner one, on every path including completion before the selected accept. -/
theorem exposeAt_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (f : R → S)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat) (owners : List EncodedEntry) (state : NativeState KemSK) :
    exposeAt setup codec checks identityIndex publicIdentity (fun output => f (observe output)) work index owners state =
      mapOutcome f <$> exposeAt setup codec checks identityIndex publicIdentity observe work index owners state := by
  simp only [exposeAt, map_bind]
  apply bind_congr
  rintro ⟨⟨cut, after⟩, native⟩
  cases cut with
  | complete result => rw [map_pure]; rfl
  | pending raw next =>
    dsimp only
    rw [map_bind]
    apply bind_congr
    intro answer
    have same : tagged (fun output => f (observe output)) raw next answer.1 = f <$> tagged observe raw next answer.1 := by
      simp only [tagged, Functor.map_map]
    rw [same, commands_map, hide_map]

/-- Exposing the selected accept with the identity observation interprets, under the actual encapsulator, to the actual source command program of the tagged client itself. -/
theorem exposeAt_tag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    simulateQ (actual setup) (exposeAt setup codec checks identityIndex publicIdentity id work index owners state) =
      PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex publicIdentity (tag work index)
        owners state := by
  rw [PqxdhRegistrationJointAcceptKemCut.exposeAt_actual, id_map]

/-- Replace the client result of an initialized source outcome, keeping the Server, the encoded state and the final source state. -/
def mapInitialized (f : R → S)
    (result : Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK R) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A) :
    Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK S) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A :=
  (result.1.map fun outcome => (outcome.1, f outcome.2.1, outcome.2.2), result.2)

/-- The monitored source commands after the actual initializer are natural in the client result. -/
theorem initialization_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (f : R → S)
    (client : OracleComp (SourceSpec KemSK) R) (joint : PqxdhDynamicIdentityPool.SourceState) (runtime : A)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) :
    PqxdhRegistrationJointKemInitialization.commands setup codec checks created (f <$> client) joint runtime
        selected pairs =
      mapInitialized f <$> PqxdhRegistrationJointKemInitialization.commands setup codec checks created client joint
        runtime selected pairs := by
  simp only [PqxdhRegistrationJointKemInitialization.commands, program_map, router_map, Functor.map_map]
  congr 1
  funext reached
  rcases reached with ⟨_ | outcome, after⟩ <;> rfl

/-- The selected-key-first source game is natural in the client result. -/
theorem selectedFirst_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (f : R → S)
    (client : OracleComp (SourceSpec KemSK) R) (state : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (count : Nat) (selected : Fin (count + 1)) :
    PqxdhRegistrationJointKemInitialization.selectedFirst setup codec checks ensureInit supplied (f <$> client) state
        count selected =
      mapInitialized f <$> PqxdhRegistrationJointKemInitialization.selectedFirst setup codec checks ensureInit supplied
        client state count selected := by
  simp only [PqxdhRegistrationJointKemInitialization.selectedFirst, map_bind]
  apply bind_congr
  intro chosen
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · rw [map_pure]
    rfl
  · simp only [map_bind]
    apply bind_congr
    intro others
    exact initialization_map setup codec checks created f client after.1.1 after.2 selected.val _

/-- Replace the result of a KEM cut: a completion maps its result, and a pending cut keeps its request and maps the result of its saved continuation. -/
def cutMap (f : Result → Next) : PqxdhRegistrationJointKemCut.Cut KemSK Result → PqxdhRegistrationJointKemCut.Cut KemSK Next
  | .complete result => .complete (f result)
  | .pending request next => .pending request fun reply => f <$> next reply

/-- The KEM scan is natural in the program result, including the saved continuation of a pending cut. -/
theorem scan_map (setup : Setup baseSpec KemSK) (f : Result → Next)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) (index : Nat) :
    PqxdhRegistrationJointKemCut.scan setup (f <$> work) index =
      cutMap f <$> PqxdhRegistrationJointKemCut.scan setup work index := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure result => rfl
  | query_bind query next ih =>
    rw [map_bind]
    cases query with
    | inl request =>
      rw [PqxdhRegistrationJointKemCut.scan_other, PqxdhRegistrationJointKemCut.scan_other, map_bind]
      exact bind_congr fun answer => ih answer index
    | inr request =>
      cases index with
      | zero =>
        rw [PqxdhRegistrationJointKemCut.scan_target, PqxdhRegistrationJointKemCut.scan_target, map_pure]
        rfl
      | succ index =>
        rw [PqxdhRegistrationJointKemCut.scan_prior, PqxdhRegistrationJointKemCut.scan_prior, map_bind]
        exact bind_congr fun answer => ih answer index

/-- The scanned program of the raw-ordinal KEM prechallenge is the result map of the KEM scan of the identity-observation exposure: the KEM games scan the decision program at exactly the cut and with exactly the saved continuation of the tagged program. -/
theorem rawScan_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) :
    PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision work index created =
      cutMap (mapOutcome (decideTag decision)) <$> PqxdhRegistrationJointKemCut.scan setup
        (exposeAt setup codec checks created.server.server.metadata.identityIndex created.publicIdentity id work index []
          (PqxdhRegistrationJointInitializedAccept.initial created)) 0 := by
  rw [← scan_map, ← exposeAt_map]
  rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.router_split' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.router_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.router_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.router_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.router_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.router_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.coins_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.coins_stopped

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.finish_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.finish_stopped

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.commands_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.commands_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.program_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.decision_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.decision_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.hide_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.hide_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.exposeAt_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.exposeAt_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.exposeAt_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.exposeAt_tag

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.initialization_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.initialization_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.selectedFirst_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.selectedFirst_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.scan_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.scan_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.rawScan_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural.rawScan_map
