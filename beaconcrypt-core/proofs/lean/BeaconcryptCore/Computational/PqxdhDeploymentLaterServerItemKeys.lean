-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemHybrid

/-! LQ-F upstream, unit A2: theorem T7 and stage S7 of item 2 over the logged source, and the U-L1 targets (LQ-F upstream design-v2, section 4.4, module `…ItemKeys`). The frozen targets of unit D1 (`PqxdhDeploymentLaterServerItemTargets`) are proved here exactly as stated there:

- `opaqueBranchL_slots_two` and `opaqueBranchSlotsTwoTargetL_holds : OpaqueBranchSlotsTwoTargetL`: for every logged-source program within a logged source budget and under `SourceFullCorrect`, the logged opaque KEM-ideal branch and the logged two-slot world `laterSlotGame … 2` are distinguishable with advantage at most `slotLossL … budget`, the logged form of the right side of `PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_slots_two`.
- `laterSlotsTwoTarget_holds : LaterSlotsTwoTarget` (by `laterSlotsTwo_of_generic`, which meets the logged source budget of the compiled LQ-F program with `compile_server_certified`) and its explicit form `later_slots_two`: the same bound at `compileServer … first second` for a run-phase adversary within its budget and a post-run adversary within its post budget, at the transported caps, whose guessing term is `(qAccept + qFinish + qHmac + qHmac₂)/2^256` (`slotLossL_transported`).

The chain is the classical one with two slots: stage S1c over the logged source (`PqxdhDeploymentLaterServerItemSplit.opaqueBranchL_split`), stage S2 with stage T (`PqxdhDeploymentLaterServerItemOnce.opaqueBranchL_uniform_two`), stage S3b (`PqxdhDeploymentLaterServerItemFactor.uniformGameL_entry`), the generic hybrid of stage S7 (`PqxdhDeploymentLaterServerItemHybrid.slotOf_telescope`) at the logged factored root client with its two value requests (`entryClientL_two`). On the way it proves theorem T7 over the logged source (`opaqueBranchL_idealKeys_two`) and stage S7 with every hidden entry ideal (`opaqueBranchL_allIdeal_two`).

Decorrelation caveat (route R1, sharpened for LQ-F; LQ-F upstream design-v2, section 5): the first term of every bound here is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle. In LQ-F the post-run adversary knows every revealed Beacon secret, the Server seed and every generated ephemeral, hence both hidden entries' 128-byte DH coordinates `m` exactly; each hidden entry is the R1 table at `padFF32 ‖ m ‖ u` with only the shared 32-byte ML-KEM output `u` unknown. The unpredictability of the two entries given `m` and their mutual independence rest on R1 alone. Classically `m` also contains honest-honest DH values the adversary cannot compute; item 2 never uses them, but in LQ-F no such second line of defence exists. The premises (R1, the HMAC-SHA-512 PRF game, the Extract game on `uniform32`, `SourceFullCorrect`, the logged source budget) are those of the classical T7; no assumption is added. LQ-F claims confidentiality only: nothing here cites T5, theorem A2 or T8, and no definition of unit A2 references a DH-keyed component. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (hmacPrfRealGame hmacPrfRandomGame)
open PqxdhFullSecretInputKdf (SourceFullCorrect)
open PqxdhCorrelatedExpandHybrid (uniformGame indexedReduction)
open PqxdhRegistrationJointKemEntryFactor (Output)
open PqxdhRegistrationJointKemSecondEntry (keyScheduleBound keySchedule_hop lazyImpl)
open PqxdhRegistrationJointKemIdealKeys (advantage_left)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec Handle)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerCompileBudget (laterTransported)
open PqxdhDeploymentLaterServerOpaque (opaqueBranch)
open PqxdhDeploymentLaterServerItemTargets (rootClientL entryClientL entryDL entryDkL hybridOf laterSlotGame slotLossL
  OpaqueBranchSlotsTwoTargetL LaterSlotsTwoTarget laterSlotsTwo_of_generic)
open PqxdhDeploymentLaterServerItemFactor (uniformGameL_entry)
open PqxdhDeploymentLaterServerItemOnce (entryClientL_two opaqueBranchL_uniform_two)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### Entry 0 and theorem T7 over the logged source -/

/-- The distinguisher of entry 0 of the logged branch in the generic hybrid is stage S3b's `entryDL`. -/
theorem entryDkL_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    entryDkL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index 0 =
      entryDL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index :=
  PqxdhDeploymentLaterServerItemHybrid.entryDkOf_zero setup.source _

/-- The uniform-root world on the logged root client has the output distribution of the 0-th hybrid of the logged factored root client. -/
theorem uniform_hybridL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    𝒟[uniformGame (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)] =
      𝒟[hybridOf setup.source (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work
        runtime count selected index) 0] :=
  PqxdhDeploymentLaterServerItemHybrid.uniform_hybridOf setup.source _ _
    (uniformGameL_entry setup codec checks ensureInit supplied decision work runtime count selected index)

/-- Stages S3b and S4b over the logged source: the uniform-root world on the logged root client and the ideal-key world on `entryDL` (entry 0's 108 bytes uniform) are distinguishable with advantage at most G2's four key-schedule advantages on `entryDL`. -/
theorem uniform_idealKeysL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (correct : SourceFullCorrect setup.source setup.hmac) :
    (uniformGame (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)).boolDistAdvantage
      (PqxdhServerAuthKeySchedule.uniformGame (entryDL (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index)) ≤
      keyScheduleBound setup.source setup.hmac (entryDL (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index) := by
  rw [advantage_left (uniformGameL_entry setup codec checks ensureInit supplied decision work runtime count selected
    index)]
  exact keySchedule_hop setup.source setup.hmac correct _

/-- Theorem T7 over the logged source, with stage T (T7-L). The logged opaque KEM-ideal branch and the ideal-key world on entry 0's distinguisher `entryDL` (entry 0's 108 bytes uniform, every other hidden entry the key-schedule output of a fresh uniform root, no KEM candidate drawn) are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256`, plus the sum of two one-query HMAC-SHA-512 PRF advantages of reductions built from the candidate-free logged root client, plus G2's four key-schedule advantages on `entryDL` (`keyScheduleBound`). The first term is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1). In LQ-F the post-run adversary knows both hidden entries' 128-byte DH coordinates exactly, and their unpredictability and mutual independence rest on R1 alone; classically the coordinates also contain honest-honest DH values that item 2 never uses, and in LQ-F no such second line of defence exists. This is a two-sided transfer of the registration segment, not a secrecy theorem. -/
theorem opaqueBranchL_idealKeys_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ kind, work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some kind) (budget kind))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (PqxdhServerAuthKeySchedule.uniformGame (entryDL (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index)) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range 2,
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) +
        keyScheduleBound setup.source setup.hmac (entryDL (Reader := Reader) setup codec checks ensureInit supplied
          decision work runtime count selected index) :=
  (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add
    (opaqueBranchL_uniform_two setup codec checks ensureInit supplied decision work runtime count selected index budget
      certified)
    (uniform_idealKeysL setup codec checks ensureInit supplied decision work runtime count selected index correct))

/-! ### Stage S7 over the logged source -/

/-- The logged two-slot world is the game with every hidden entry of the logged branch ideal: the logged factored root client makes at most two value requests (stage T), so the first-touch allocator and the persistent lazy table on two slots are the lazy uniform table. -/
theorem laterSlotGame_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    laterSlotGame (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        2 =
      (simulateQ lazyImpl (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
        count selected index)).run' (∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache) :=
  PqxdhDeploymentLaterServerItemHybrid.slotGameOf_all _ 2
    (entryClientL_two setup codec checks ensureInit supplied decision work runtime count selected index)

/-- The uniform-root world on the logged root client and the logged two-slot world are distinguishable with advantage at most the key-schedule bounds of the first two fresh hidden entries of the logged branch (the generic hybrid at the logged factored root client). -/
theorem uniform_slotsL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (correct : SourceFullCorrect setup.source setup.hmac) :
    (uniformGame (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)).boolDistAdvantage
      (laterSlotGame (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index 2) ≤
      ∑ k ∈ Finset.range 2, keyScheduleBound setup.source setup.hmac
        (entryDkL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
          k) :=
  PqxdhDeploymentLaterServerItemHybrid.slotOf_telescope setup.source _ setup.hmac correct _
    (uniformGameL_entry setup codec checks ensureInit supplied decision work runtime count selected index) 2
    (entryClientL_two setup codec checks ensureInit supplied decision work runtime count selected index)

/-- Stage S7 over the logged source, with stage T. The logged opaque KEM-ideal branch and the game in which every hidden entry of the logged branch holds 108 uniform bytes are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` (route R1), plus the sum of two one-query HMAC-SHA-512 PRF advantages, plus, for each of the first two fresh hidden entries, G2's four key-schedule advantages on that entry's distinguisher. Decorrelation caveat (route R1): as for `opaqueBranchL_idealKeys_two`. -/
theorem opaqueBranchL_allIdeal_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ kind, work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some kind) (budget kind))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      ((simulateQ lazyImpl (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
        count selected index)).run' (∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache)) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range 2,
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) +
        ∑ k ∈ Finset.range 2, keyScheduleBound setup.source setup.hmac
          (entryDkL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
            k) := by
  rw [← laterSlotGame_two]
  exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add
    (opaqueBranchL_uniform_two setup codec checks ensureInit supplied decision work runtime count selected index budget
      certified)
    (uniform_slotsL setup codec checks ensureInit supplied decision work runtime count selected index correct))

/-! ### The U-L1 targets -/

/-- U-L1, generic form: the logged counterpart of `PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_slots_two`. For every logged-source program within a logged source budget (caps per source14 kind through `LaterServerReserve.laterKind`; the Server read has no kind and needs no cap) and under `SourceFullCorrect`, the logged opaque KEM-ideal branch and the logged two-slot world differ by at most `slotLossL`: the guessing term `(qAccept + qFinish + qHmac) / 2^256` (route R1), two one-query HMAC-SHA-512 PRF advantages of `rootClientL`'s reductions, and G2's four key-schedule advantages on each of `entryDkL 0` and `entryDkL 1`. Decorrelation caveat (route R1): in LQ-F the post-run adversary knows both hidden entries' 128-byte DH coordinates exactly, and their unpredictability and mutual independence rest on R1 alone (module docstring). -/
theorem opaqueBranchL_slots_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ kind, work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some kind) (budget kind))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (laterSlotGame (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index 2) ≤
      slotLossL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        budget :=
  (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add
    (opaqueBranchL_uniform_two setup codec checks ensureInit supplied decision work runtime count selected index budget
      certified)
    (uniform_slotsL setup codec checks ensureInit supplied decision work runtime count selected index correct))

/-- The frozen generic U-L1 target of unit D1 holds. -/
theorem opaqueBranchSlotsTwoTargetL_holds : OpaqueBranchSlotsTwoTargetL :=
  fun setup codec checks ensureInit supplied decision work runtime count selected index budget certified correct =>
    opaqueBranchL_slots_two setup codec checks ensureInit supplied decision work runtime count selected index budget
      certified correct

/-- The frozen U-L1 target of unit D1 at the compiled LQ-F program holds: the generic target gives it through `laterSlotsTwo_of_generic`. -/
theorem laterSlotsTwoTarget_holds : LaterSlotsTwoTarget :=
  laterSlotsTwo_of_generic opaqueBranchSlotsTwoTargetL_holds

/-- U-L1 at the compiled LQ-F program (`LaterSlotsTwoTarget` with its arguments). For a run-phase adversary `first` within its budget and a post-run adversary `second` within its post budget on every input, the logged opaque KEM-ideal branch of the per-target decision `LaterServerTransfer.decision` (the branch that remains after `kem_transfer_server`) and the logged two-slot world differ by at most `slotLossL` at the transported caps `laterTransported bounds budget post`, whose first term is `(qAccept + qFinish + qHmac + qHmac₂)/2^256` (`slotLossL_transported`): the post-run HMAC queries are charged in the same guessing term with coefficient one. Decorrelation caveat (route R1, sharpened for LQ-F): the post-run adversary knows every revealed Beacon secret, the Server seed and every generated ephemeral, hence both hidden entries' 128-byte DH coordinates `m` exactly; each hidden entry is the R1 table at `padFF32 ‖ m ‖ u` with only the 32-byte ML-KEM output `u` unknown, and their unpredictability given `m` and their mutual independence rest on R1 alone. The premises are those of the classical T7 with the logged source budget met by `compile_server_certified`. LQ-F claims confidentiality only. -/
theorem later_slots_two {Out : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) (correct : SourceFullCorrect setup.source setup.hmac)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : PqxdhDeploymentKemTransfer.Observed Out → Bool)
    (claim : PqxdhDeploymentKemTransfer.Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit none
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
        budget.create (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val false).boolDistAdvantage
      (laterSlotGame (Reader := Reader) setup codec checks ensureInit none
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
        budget.create (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2) ≤
      slotLossL (Reader := Reader) setup codec checks ensureInit none
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
        budget.create (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val (laterTransported bounds budget post) :=
  laterSlotsTwoTarget_holds setup codec route checks correct ensureInit bounds mode first second budget respects post
    postRespects event claim g runtime

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.entryDkL_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.entryDkL_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.uniform_hybridL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.uniform_hybridL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.uniform_idealKeysL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.uniform_idealKeysL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.opaqueBranchL_idealKeys_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.opaqueBranchL_idealKeys_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.laterSlotGame_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.laterSlotGame_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.uniform_slotsL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.uniform_slotsL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.opaqueBranchL_allIdeal_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.opaqueBranchL_allIdeal_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.opaqueBranchL_slots_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.opaqueBranchL_slots_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.opaqueBranchSlotsTwoTargetL_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.opaqueBranchSlotsTwoTargetL_holds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.laterSlotsTwoTarget_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.laterSlotsTwoTarget_holds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.later_slots_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys.later_slots_two
