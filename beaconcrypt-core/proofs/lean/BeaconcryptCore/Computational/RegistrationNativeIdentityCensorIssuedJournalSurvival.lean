-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietPath
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstCallback
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorCanonicalJournal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedOwner
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
import BeaconcryptCore.Computational.RegistrationNativeStageTraceCut
import BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
/-! The actual original issued first-signing callback selects its genuine row and target, and its entire canonical continuation reaches the same accepted packet at the unchanged all-attempt ordinal. Every earlier public stop is discharged from the original causal witness. Distribution transport is supplied separately; this module makes no support-to-probability inference. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeIdentityBundlePhase (Keeps Closed)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


variable {V : Type}
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)

local notation "canonical" => RegistrationNativeIdentityCensorCanonicalSource.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve

omit primitives in
private theorem split_map {A B C : Type} (f : A → C) (g : B → C)
    (leadingOriginal : List B) (call : B) (suffix : List B) (current : List A)
    (same : current.map f=(leadingOriginal++call::suffix).map g) :
    ∃ leading chosen trailing,current=leading++chosen::trailing ∧ leading.map f=leadingOriginal.map g ∧
      f chosen=g call ∧ trailing.map f=suffix.map g := by
  induction leadingOriginal generalizing current with
  | nil=>
      cases current with
      | nil=>cases same
      | cons head rest=>
          simp only [List.nil_append,List.map_cons,List.cons.injEq] at same
          exact ⟨[],head,rest,rfl,rfl,same.1,same.2⟩
  | cons head rest ih=>
      cases current with
      | nil=>cases same
      | cons first later=>
          simp only [List.cons_append,List.map_cons,List.cons.injEq] at same
          obtain ⟨leading,chosen,trailing,split,front,atCall,tail⟩ := ih later same.2
          exact ⟨first::leading,chosen,trailing,by rw [split]; rfl,by simp only [List.map_cons,same.1,front],atCall,tail⟩

omit primitives in
private theorem main_row {A : Type} (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (seed : PqxdhJointIdentity.IdentitySeed)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source A)
    (before : FullState) (result : A × FullState) (found : before.2.pool.seeds[selected]?=some seed)
    (supported : result∈support ((RegistrationNativeIdentityCensorEdOutgoingSource.interpret joint selected placeholder false work).run before)) :
    result.2.2.pool.seeds[selected]?=some seed := by
  simp only [RegistrationNativeIdentityCensorEdOutgoingSource.interpret,StateT.run,bind_pure_comp,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact RegistrationNativeIdentityCensorSelectedInvariant.row_program joint selected placeholder false seed _ before.2 found inner called

/-- The same actual projected first-signing callback selects its wanted target, retains its genuine row and survives the public stop; all three facts are derived from its original first history crossing. -/
theorem first_callback (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (original : Call TypedSpec (Whole n KemSK Platform source)) (split : attempt.leading=leading++original::trailing)
    (index : Nat) (queryEq : original.query=.inr (.bundle index)) (originalCalled : Executed actual original)
    (fresh : PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages attempt.finalOwner.identity.handle original.before.2)
    (signed : PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages attempt.finalOwner.identity.handle original.after.2)
    (position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (seed : PqxdhJointIdentity.IdentitySeed)
    (current : Call TypedSpec FullState)
    (same : RegistrationNativeObservedStageTrace.mapCall RegistrationNativeIdentityCensorActualHashSource.project current=
      RegistrationNativeObservedStageTrace.mapCall (RegistrationNativeIdentityCensorNormalizedJournal.project placeholder) original)
    (ordinal : current.before.1.2.bundles=position) (missing : current.before.1.2.target=none)
    (synced : current.before.1.2.target=current.before.2.target) (found : current.before.2.pool.seeds[attempt.finalOwner.identity.handle]?=some seed)
    (called : Executed (canonical attempt.finalOwner.identity.handle position placeholder) current) :
    RegistrationNativeIdentityCensorAdaptivePostselection.Selected attempt.finalOwner.identity.handle
      (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime) seed current.after ∧
    RegistrationNativeIdentityCensorAdaptivePostselection.published current.query current.reply current.after=false := by
  rcases original with ⟨originalQuery,originalBefore,originalReply,originalAfter⟩
  rcases current with ⟨currentQuery,currentBefore,currentReply,currentAfter⟩
  simp only [RegistrationNativeObservedStageTrace.mapCall,Call.mk.injEq] at same
  obtain ⟨queries,beforeSame,replies,afterSame⟩ := same
  subst currentQuery
  dsimp only at queryEq
  subst originalQuery
  have replyEq : currentReply=originalReply := eq_of_heq replies
  subst currentReply
  have poolBefore : currentBefore.2.pool=originalBefore.2.1 := congrArg (fun state=>state.2.1) beforeSame
  have poolAfter : currentAfter.2.pool=originalAfter.2.1 := congrArg (fun state=>state.2.1) afterSame
  have freshAt : PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages
      attempt.finalOwner.identity.handle currentBefore.2.pool := by rw [poolBefore]; exact fresh
  have signedAt : PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages
      attempt.finalOwner.identity.handle currentAfter.2.pool := by rw [poolAfter]; exact signed
  have role : RegistrationNativeIdentitySigningRole.oneTime (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime)=true := by
    simp [RegistrationNativeIdentitySigningRole.oneTime,PqxdhEd25519EufCma.oneTimeMessage]
  have target := RegistrationNativeIdentityCensorFirstCallback.target setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve attempt.finalOwner.identity.handle index position placeholder
      _ role currentBefore currentAfter originalReply ordinal missing synced freshAt signedAt called
  have row := main_row setup.joint attempt.finalOwner.identity.handle placeholder seed
    (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve placeholder (.inr (.bundle index)))
    (RegistrationNativeIdentityCensorAdaptivePostselection.entered position (.inr (.bundle index)) currentBefore)
    (originalReply,currentAfter) found called
  have quiet := RegistrationNativeIdentityCensorFirstCallback.quiet setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve serverKeyId bounds mode work budget before empty result reached attempt issued
      leading trailing index originalReply originalBefore originalAfter split originalCalled fresh signed currentAfter
  exact ⟨⟨target.1,target.2,row⟩,quiet⟩

omit primitives in
private theorem count_append {S : Type} (left right : List (Call TypedSpec S)) :
    RegistrationNativeIdentityCensorVisitorFold.count (left++right)=
      RegistrationNativeIdentityCensorVisitorFold.count left+RegistrationNativeIdentityCensorVisitorFold.count right := by
  simp only [RegistrationNativeIdentityCensorVisitorFold.count,RegistrationNativeIdentityUnissuedCutTrace.count,List.map_append,List.sum_append]

omit primitives in
private theorem marked_query {S : Type} (call : Call TypedSpec S) (packet : registration.InitPacket) (session : Nat)
    (marked : RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply=some (.accept packet (some session))) :
    call.query=.inr (.accept packet) := by
  rcases call with ⟨query,before,reply,after⟩
  cases query with
  | inl coin=>cases marked
  | inr command=>
      cases command <;> simp_all [RegistrationNativeRawRegistrationJournal.typedMark]


/-- The entire canonical continuation beginning at the actual first signing callback reaches the same original accepted packet. Its selection, public stops and all-attempt ordinal are derived from the original issued witness and exact projected journal. -/
theorem survives (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before,[])))
    (attempt : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt setup.joint wire budget result.2.2.2 result.2.2.1)
    (issued : RegistrationNativePlatformIdentityCtxFiniteCover.Issued attempt)
    (position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (seed : PqxdhJointIdentity.IdentitySeed)
    {first last : FullState} {calls : List (Call TypedSpec FullState)}
    (path : Path (canonical attempt.finalOwner.identity.handle position placeholder) first calls last)
    (same : calls.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativeIdentityCensorActualHashSource.project)=
      (issued.cut.call::(issued.cut.trailing++attempt.call::attempt.trailing)).map
        (RegistrationNativeObservedStageTrace.mapCall (RegistrationNativeIdentityCensorNormalizedJournal.project placeholder)))
    (ordinal : first.1.2.bundles=position) (missing : first.1.2.target=none)
    (synced : first.1.2.target=first.2.target) (found : first.2.pool.seeds[attempt.finalOwner.identity.handle]?=some seed) :
    RegistrationNativeIdentityCensorVisitorJournal.fold RegistrationNativeIdentityCensorVisitorCanonicalJournal.getTarget
      RegistrationNativeIdentityCensorAdaptivePostselection.published
      (RegistrationNativePlatformIdentityCtxFiniteCover.acceptanceOrdinal attempt).val
      (RegistrationNativeIdentityCensorVisitorFold.count issued.cut.leading) calls=
        some (PqxdhEd25519EufCma.oneTimeMessage attempt.decoded.oneTime,attempt.packet) := by
  obtain ⟨_originalPrefix,originalCalled,_originalSuffix⟩ := RegistrationNativePlatformIdentityCtxFiniteCover.full_cut_paths
    setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      serverKeyId bounds mode work budget before result reached attempt issued.cut
  cases path with
  | nil=>cases same
  | cons current called rest last following=>
    simp only [List.map_cons,List.cons.injEq] at same
    have selected := first_callback setup checks route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve serverKeyId bounds mode work budget before empty result reached attempt issued
        issued.cut.leading issued.cut.trailing issued.cut.call issued.cut.split issued.cut.index issued.cut.queryEq originalCalled issued.cut.fresh issued.cut.signed
        position placeholder seed current same.1 ordinal missing synced found called
    obtain ⟨leading,acceptCall,trailing,split,front,atAccept,_tail⟩ := split_map
      (RegistrationNativeObservedStageTrace.mapCall RegistrationNativeIdentityCensorActualHashSource.project)
      (RegistrationNativeObservedStageTrace.mapCall (RegistrationNativeIdentityCensorNormalizedJournal.project placeholder))
        issued.cut.trailing attempt.call attempt.trailing rest same.2
    have earlier : ∀ original∈issued.cut.trailing,original∈attempt.leading := by
      intro original member
      rw [issued.cut.split]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
    have sameCount : RegistrationNativeIdentityCensorVisitorFold.count leading=
        RegistrationNativeIdentityCensorVisitorFold.count issued.cut.trailing := by
      have counts := congrArg RegistrationNativeIdentityCensorVisitorFold.count front
      simpa only [RegistrationNativeIdentityCensorVisitorFold.count_map] using counts
    have acceptQuery : acceptCall.query=.inr (.accept attempt.packet) := by
      have queries := congrArg (fun entry=>entry.query) atAccept
      exact queries.trans (marked_query attempt.call attempt.packet attempt.session attempt.marked)
    have counted : RegistrationNativeIdentityCensorVisitorFold.count attempt.leading=
        RegistrationNativeIdentityCensorVisitorFold.count issued.cut.leading+
          RegistrationNativeIdentityCensorVisitorFold.count issued.cut.trailing := by
      rw [issued.cut.split,count_append]
      simp only [RegistrationNativeIdentityCensorVisitorFold.count,RegistrationNativeIdentityUnissuedCutTrace.count,
        List.map_cons,List.sum_cons,issued.cut.queryEq,RegistrationNativeIdentityUnissuedCutCounter.cost,Nat.zero_add]
    have acceptOrdinal : RegistrationNativeIdentityCensorVisitorFold.count issued.cut.leading+
        RegistrationNativeIdentityCensorVisitorFold.count leading=
          (RegistrationNativePlatformIdentityCtxFiniteCover.acceptanceOrdinal attempt).val := by
      rw [sameCount,←counted,RegistrationNativeIdentityCensorVisitorFold.count_original]
      rfl
    have survived := RegistrationNativeIdentityCensorQuietPath.survives setup checks route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve serverKeyId bounds mode work budget before empty result reached attempt issued
        position placeholder seed following selected.1 leading trailing acceptCall split issued.cut.trailing front earlier
        (RegistrationNativePlatformIdentityCtxFiniteCover.acceptanceOrdinal attempt).val
        (RegistrationNativeIdentityCensorVisitorFold.count issued.cut.leading) acceptOrdinal acceptQuery
    have currentQuery : current.query=.inr (.bundle issued.cut.index) := by
      have queries := congrArg (fun entry=>entry.query) same.1
      exact queries.trans issued.cut.queryEq
    rcases current with ⟨currentQuery',currentBefore,currentReply,currentAfter⟩
    dsimp only at currentQuery
    subst currentQuery'
    simpa only [RegistrationNativeIdentityCensorVisitorJournal.fold,
      RegistrationNativeIdentityCensorAdaptivePostselection.attempt,selected.2,Bool.false_eq_true,ite_false,
      RegistrationNativeIdentityCensorPublicClient.IsAccept,ite_false,Nat.add_zero] using survived

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival.first_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival.first_callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival.survives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival.survives
