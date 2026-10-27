-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple
import BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent

/-! The initial-response-origin event CE-A1 of the common deployment experiment (CE-8), on the registration view of a transcript. `regsOf` keeps exactly the registration entries of a transcript, in order: every create whose pin parses (with its word, key ID and returned owner handle), and every bundle, accept, build and finish with its reply; `regsOfSource` reads the same view from the journal of a source14 program. `summarizeReg` folds the view into unit A's public summary (`summarize_regs`: it is the summary of the transcript). `accepted c` scans the view with the summary and returns the registration entries strictly before owner `c`'s accepting finish (the first successful finish of `c` while the summary has `c` in InitSent) together with that finish's raw input. A session `i` matches owner `c` before its acceptance (`MatchedAt`) when, before the acceptance, an accept returned `i` on bytes whose raw candidate the source attached verification accepts with exactly the identity key and key tuple read, without a signature check, from `c`'s first published bundle (`publishedKeys`), and a build of `i` returned a response whose decoded record (`PqxdhServerAuthRecordPublicationEvent.frame`) is the decoded record of the raw input `c` accepted. `Unmatched binding c` is the A1 failure at `c`: `c` accepted, its creation before the acceptance carried `binding`, no bundle call of `c` in Fresh was rejected before the acceptance, and no session matches it. Only public bytes, the public attached verification of `Pqxdh.Crypto`, the codec readers and the parsers are used; no secret, root, partner or ghost. The event is fixed once `c` stops (`Stop`: `c` accepted or a bundle call of `c` in Fresh was rejected): appending entries after the stop does not change it (`unmatched_stop`), so it is the same on a transcript and on its prefix up to the stop (`unmatched_untilStop`). No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (Entry parsePin)
open PqxdhDeploymentTranscript (PublicPhase Summary candidateOf acceptedKeys)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A registration entry: a create with its parsed pin, key ID and returned owner handle, or a bundle, accept, build or finish with its reply. -/
inductive Reg where
  | create (pin : Word32) (keyId : Std.U64) (owner : Nat)
  | bundle (owner : Nat) (reply : Option Pqxdh.Bytes)
  | accept (raw : Pqxdh.Bytes) (reply : Option Nat)
  | build (session : Nat) (payload : Option Pqxdh.Bytes) (reply : Option PqxdhServerRegistrationPublication.Response)
  | finish (owner : Nat) (raw : Pqxdh.Bytes) (reply : Option Pqxdh.Bytes)

/-- The registration entry of a transcript entry: a create whose pin parses and that returned an owner handle, or any bundle, accept, build or finish. -/
def regOfEntry : Entry → Option Reg
  | ⟨.inl (.inr (.create pin keyId)), some owner⟩ => (parsePin pin).map fun word => .create word keyId owner
  | ⟨.inl (.inr (.bundle owner)), reply⟩ => some (.bundle owner reply)
  | ⟨.inl (.inr (.accept raw)), reply⟩ => some (.accept raw reply)
  | ⟨.inl (.inr (.build session payload)), reply⟩ => some (.build session payload reply)
  | ⟨.inl (.inr (.finish owner raw)), reply⟩ => some (.finish owner raw reply)
  | _ => none

/-- The registration view of a transcript, oldest first. -/
def regsOf (transcript : List Entry) : List Reg := transcript.filterMap regOfEntry

/-- One entry of the journal of a source14 program with explicit field reads. -/
abbrev SourceEntry (KemSK : Type) :=
  (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) ×
    (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query

/-- The registration entry of a source14 journal entry. -/
def regOfSource : SourceEntry KemSK → Option Reg
  | ⟨.inl (.inr (.create pin keyId)), owner⟩ => some (.create pin keyId owner)
  | ⟨.inl (.inr (.bundle owner)), reply⟩ => some (.bundle owner reply)
  | ⟨.inl (.inr (.accept raw)), reply⟩ => some (.accept raw reply)
  | ⟨.inl (.inr (.build session payload)), reply⟩ => some (.build session payload reply)
  | ⟨.inl (.inr (.finish owner raw)), reply⟩ => some (.finish owner raw reply)
  | _ => none

/-- The registration view of a source14 journal, oldest first. -/
def regsOfSource (journal : List (SourceEntry KemSK)) : List Reg := journal.filterMap regOfSource

/-- Unit A's summary step, on a registration entry. -/
def stepReg (summary : Summary) : Reg → Summary
  | .create pin keyId owner =>
      { summary with
        owners := summary.owners ++ [(pin, keyId)]
        phases := Function.update summary.phases owner .fresh }
  | .bundle owner (some _) =>
      if summary.phases owner = .fresh then { summary with phases := Function.update summary.phases owner .initSent }
      else summary
  | .bundle owner none =>
      if summary.phases owner = .fresh then { summary with failures := Function.update summary.failures owner true }
      else summary
  | .finish owner _ (some _) =>
      if summary.phases owner = .initSent then
        { summary with phases := Function.update summary.phases owner .established }
      else summary
  | .finish owner _ none =>
      if summary.phases owner = .initSent then { summary with phases := Function.update summary.phases owner .aborted }
      else summary
  | .accept _ _ => summary
  | .build _ _ _ => summary

/-- The summary of a registration view. -/
def summarizeReg (regs : List Reg) : Summary := regs.foldl stepReg Summary.empty

/-- Scan for owner `c`'s accepting finish from a summary and the entries already passed. -/
def acceptedFrom (c : Nat) (summary : Summary) (before : List Reg) : List Reg → Option (List Reg × Pqxdh.Bytes)
  | [] => none
  | reg :: rest =>
      match reg with
      | .finish owner raw (some _) =>
          if owner = c ∧ summary.phases c = .initSent then some (before, raw)
          else acceptedFrom c (stepReg summary reg) (before ++ [reg]) rest
      | _ => acceptedFrom c (stepReg summary reg) (before ++ [reg]) rest

/-- The registration entries strictly before owner `c`'s accepting finish, with that finish's raw input: its first successful finish while the summary has it in InitSent. -/
def accepted (c : Nat) (regs : List Reg) : Option (List Reg × Pqxdh.Bytes) := acceptedFrom c Summary.empty [] regs

/-- The bytes of the first successful bundle of an owner in a registration view. -/
def bundleOfReg (regs : List Reg) (owner : Nat) : Option Pqxdh.Bytes :=
  regs.findSome? fun reg => match reg with
    | .bundle index (some bytes) => if index = owner then some bytes else none
    | _ => none

/-- The identity key and key tuple of published bundle bytes, read without a signature check. -/
def keysOfBundle (codec : Codec Reader Response) (bundle : Option Pqxdh.Bytes) :
    Option (PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple) := do
  let bytes ← bundle
  let published ← candidateOf codec bytes
  let identity ← PqxdhEd25519EufCma.parseIdentity published.identityKey
  let keys ← PqxdhDeploymentPublishedTuple.candidateTuple published
  pure (identity, keys)

/-- The identity key and key tuple of an owner's first published bundle, read from public bytes without a signature check. -/
def publishedKeys (codec : Codec Reader Response) (regs : List Reg) (owner : Nat) :
    Option (PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple) :=
  keysOfBundle codec (bundleOfReg regs owner)

/-- Session `session` matches owner `owner` in the entries before its acceptance: an accept returned `session` on bytes whose raw candidate the source attached verification accepts with the owner's published identity key and key tuple, and a build of `session` returned a response whose decoded record is the decoded record of the accepted raw input. -/
def MatchedAt (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (owner session : Nat) (before : List Reg)
    (raw : Pqxdh.Bytes) : Prop :=
  ∃ acceptRaw candidate keys payload reply record,
    Reg.accept acceptRaw (some session) ∈ before ∧ candidateOf codec acceptRaw = some candidate ∧
    acceptedKeys crypto candidate = some keys ∧ publishedKeys codec before owner = some keys ∧
    Reg.build session payload (some reply) ∈ before ∧
    PqxdhServerAuthRecordPublicationEvent.frame codec raw = some record ∧
    PqxdhServerAuthRecordPublicationEvent.frame codec reply.serialized = some record

/-- Some session matches the owner before its acceptance. -/
def Matched (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (owner : Nat) (before : List Reg)
    (raw : Pqxdh.Bytes) : Prop :=
  ∃ session, MatchedAt crypto codec owner session before raw

/-- The A1 failure at owner `c` under `binding`: `c` accepted; before the acceptance, the `c`-th created owner carried `binding` and no bundle call of `c` in Fresh was rejected; and no session matches `c`. -/
def Unmatched (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (binding : Word32 × Std.U64) (c : Nat)
    (regs : List Reg) : Prop :=
  ∃ before raw, accepted c regs = some (before, raw) ∧ (summarizeReg before).owners[c]? = some binding ∧
    (summarizeReg before).failures c = false ∧ ¬ Matched crypto codec c before raw

/-- Owner `c` has stopped: it accepted, or a bundle call of `c` in Fresh was rejected. -/
def Stop (c : Nat) (regs : List Reg) : Prop := (accepted c regs).isSome ∨ (summarizeReg regs).failures c = true

instance (c : Nat) (regs : List Reg) : Decidable (Stop c regs) := by
  unfold Stop
  infer_instance

/-- The shortest prefix satisfying a predicate, or the whole list. -/
def untilFrom {α : Type} (stop : List α → Prop) [DecidablePred stop] (passed : List α) : List α → List α
  | [] => passed
  | entry :: rest => if stop (passed ++ [entry]) then passed ++ [entry] else untilFrom stop (passed ++ [entry]) rest

/-- The shortest prefix of a list satisfying a predicate, or the whole list when no prefix does (the empty prefix is not tested). -/
def untilStop {α : Type} (stop : List α → Prop) [DecidablePred stop] (list : List α) : List α := untilFrom stop [] list

/-- The binding of the protected Server: its identity key as a 32-byte word and its key ID. -/
def protectedBinding (setup : Setup baseSpec KemSK) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) :
    Word32 × Std.U64 :=
  (PqxdhRootTableInitialization.rootArray created.publicIdentity.ed25519, setup.serverKeyId)

/-- CE-A1's event at creation index `c` on an outcome of the deployment experiment: a Server was constructed and owner `c`, created with the protected binding, accepted with no matching session and no rejected bundle call in Fresh before its acceptance. -/
def A1At {X A : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (c : Nat) (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.State KemSK) × A) : Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    Unmatched setup.source.crypto codec (protectedBinding setup created) c (regsOf final.1.transcript)

/-! ## The summary of the registration view -/

/-- One transcript entry changes the summary as its registration entry does. -/
theorem step_reg (summary : Summary) (entry : Entry) :
    PqxdhDeploymentTranscript.step summary entry = (regOfEntry entry).elim summary (stepReg summary) := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command with
    | create pin keyId =>
        cases reply with
        | none => rfl
        | some owner =>
            cases parsed : parsePin pin <;>
              simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, regOfEntry, parsed, stepReg]
    | bundle owner => cases reply <;> rfl
    | finish owner raw => cases reply <;> rfl
    | accept raw => rfl
    | build session payload => rfl
    | hmac key message => rfl
    | hash bytes => rfl
    | serverSend keyId plaintext => rfl
    | serverRaw raw => rfl
    | beaconSend owner plaintext => rfl
    | beaconRaw owner raw => rfl
  · rfl

/-- Folding transcript entries and folding their registration entries give the same summary. -/
theorem foldl_regs (summary : Summary) (transcript : List Entry) :
    transcript.foldl PqxdhDeploymentTranscript.step summary = (regsOf transcript).foldl stepReg summary := by
  induction transcript generalizing summary with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.foldl_cons, regsOf, List.filterMap_cons]
      rw [step_reg]
      cases found : regOfEntry entry with
      | none => exact ih summary
      | some reg => exact ih (stepReg summary reg)

/-- The summary of a transcript is the summary of its registration view. -/
theorem summarize_regs (transcript : List Entry) :
    PqxdhDeploymentTranscript.summarize transcript = summarizeReg (regsOf transcript) :=
  foldl_regs Summary.empty transcript

/-! ## Monotonicity and the stop -/

/-- A failure flag is never cleared. -/
theorem failures_step (summary : Summary) (reg : Reg) (owner : Nat) (failed : summary.failures owner = true) :
    (stepReg summary reg).failures owner = true := by
  cases reg with
  | bundle index reply =>
      cases reply with
      | some bytes =>
          simp only [stepReg]
          split_ifs <;> exact failed
      | none =>
          simp only [stepReg]
          split_ifs
          · by_cases same : owner = index
            · subst same
              simp
            · simp [Function.update_of_ne same, failed]
          · exact failed
  | finish index raw reply =>
      cases reply <;> (simp only [stepReg]; split_ifs <;> exact failed)
  | create pin keyId index => exact failed
  | accept raw reply => exact failed
  | build session payload reply => exact failed

/-- A failure flag survives every later registration entry. -/
theorem failures_foldl (summary : Summary) (regs : List Reg) (owner : Nat) (failed : summary.failures owner = true) :
    (regs.foldl stepReg summary).failures owner = true := by
  induction regs generalizing summary with
  | nil => exact failed
  | cons reg rest ih => exact ih (stepReg summary reg) (failures_step summary reg owner failed)

/-- The summary of a concatenation continues the fold. -/
theorem summarizeReg_append (first second : List Reg) :
    summarizeReg (first ++ second) = second.foldl stepReg (summarizeReg first) := by
  simp only [summarizeReg, List.foldl_append]

/-- A failure flag of a prefix survives in every extension. -/
theorem failures_append (first second : List Reg) (owner : Nat) (failed : (summarizeReg first).failures owner = true) :
    (summarizeReg (first ++ second)).failures owner = true := by
  rw [summarizeReg_append]
  exact failures_foldl _ second owner failed

/-- The scan's passed entries are a prefix of its result's entries, and an accepting scan keeps its result on every extension. -/
theorem acceptedFrom_append (c : Nat) (summary : Summary) (before regs extra : List Reg)
    (result : List Reg × Pqxdh.Bytes) (found : acceptedFrom c summary before regs = some result) :
    acceptedFrom c summary before (regs ++ extra) = some result := by
  induction regs generalizing summary before with
  | nil => simp [acceptedFrom] at found
  | cons reg rest ih =>
      cases reg with
      | finish owner raw reply =>
          cases reply with
          | some payload =>
              simp only [acceptedFrom, List.cons_append] at found ⊢
              split at found
              · rw [ite_eq_left (by assumption)]
                exact found
              · rw [ite_eq_right (by assumption)]
                exact ih _ _ found
          | none => exact ih _ _ found
      | create pin keyId owner => exact ih _ _ found
      | bundle owner reply => exact ih _ _ found
      | accept raw reply => exact ih _ _ found
      | build session payload reply => exact ih _ _ found

/-- An acceptance found in a prefix is the acceptance of every extension. -/
theorem accepted_append (c : Nat) (regs extra : List Reg) (result : List Reg × Pqxdh.Bytes)
    (found : accepted c regs = some result) : accepted c (regs ++ extra) = some result :=
  acceptedFrom_append c Summary.empty [] regs extra result found

/-- The scan keeps its summary equal to the summary of the passed entries and returns a list that extends them by entries of the scanned list. -/
theorem acceptedFrom_prefix (c : Nat) (before regs : List Reg) (result : List Reg × Pqxdh.Bytes)
    (found : acceptedFrom c (summarizeReg before) before regs = some result) :
    ∃ passed, result.1 = before ++ passed ∧ passed <+: regs := by
  induction regs generalizing before with
  | nil => simp [acceptedFrom] at found
  | cons reg rest ih =>
      have step : stepReg (summarizeReg before) reg = summarizeReg (before ++ [reg]) := by
        rw [summarizeReg_append]
        rfl
      have recurse : acceptedFrom c (stepReg (summarizeReg before) reg) (before ++ [reg]) rest = some result →
          ∃ passed, result.1 = before ++ passed ∧ passed <+: reg :: rest := by
        intro inner
        rw [step] at inner
        obtain ⟨passed, same, prefixed⟩ := ih (before ++ [reg]) inner
        exact ⟨reg :: passed, by rw [same, List.append_assoc]; rfl, List.cons_prefix_cons.mpr ⟨rfl, prefixed⟩⟩
      cases reg with
      | finish owner raw reply =>
          cases reply with
          | some payload =>
              simp only [acceptedFrom] at found
              split at found
              · cases found
                exact ⟨[], (List.append_nil _).symm, List.nil_prefix⟩
              · exact recurse found
          | none => exact recurse found
      | create pin keyId owner => exact recurse found
      | bundle owner reply => exact recurse found
      | accept raw reply => exact recurse found
      | build session payload reply => exact recurse found

/-- The entries before an acceptance are a prefix of the registration view. -/
theorem accepted_prefix (c : Nat) (regs : List Reg) (before : List Reg) (raw : Pqxdh.Bytes)
    (found : accepted c regs = some (before, raw)) : before <+: regs := by
  obtain ⟨passed, same, prefixed⟩ := acceptedFrom_prefix c [] regs (before, raw) found
  simp only [List.nil_append] at same
  rw [same]
  exact prefixed

/-- An acceptance of an extension that the prefix does not have lies after the whole prefix. -/
theorem acceptedFrom_late (c : Nat) (before regs extra : List Reg) (result : List Reg × Pqxdh.Bytes)
    (missing : acceptedFrom c (summarizeReg before) before regs = none)
    (found : acceptedFrom c (summarizeReg before) before (regs ++ extra) = some result) :
    before ++ regs <+: result.1 := by
  induction regs generalizing before with
  | nil =>
      simp only [List.nil_append] at found
      obtain ⟨passed, same, _⟩ := acceptedFrom_prefix c before extra result found
      rw [same, List.append_nil]
      exact List.prefix_append _ _
  | cons reg rest ih =>
      have step : stepReg (summarizeReg before) reg = summarizeReg (before ++ [reg]) := by
        rw [summarizeReg_append]
        rfl
      have recurse : acceptedFrom c (stepReg (summarizeReg before) reg) (before ++ [reg]) rest = none →
          acceptedFrom c (stepReg (summarizeReg before) reg) (before ++ [reg]) (rest ++ extra) = some result →
          before ++ reg :: rest <+: result.1 := by
        intro inner outer
        rw [step] at inner outer
        simpa [List.append_assoc] using ih (before ++ [reg]) inner outer
      cases reg with
      | finish owner raw reply =>
          cases reply with
          | some payload =>
              simp only [acceptedFrom, List.cons_append] at missing found
              split at missing
              · cases missing
              · rw [ite_eq_right (by assumption)] at found
                exact recurse missing found
          | none => exact recurse missing found
      | create pin keyId owner => exact recurse missing found
      | bundle owner reply => exact recurse missing found
      | accept raw reply => exact recurse missing found
      | build session payload reply => exact recurse missing found

/-- The registration view of a journal extended by one entry. -/
theorem regsOfSource_append (journal : List (SourceEntry KemSK)) (entry : SourceEntry KemSK) :
    regsOfSource (journal ++ [entry]) = regsOfSource journal ++ (regOfSource entry).toList := by
  simp only [regsOfSource, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases regOfSource entry <;> rfl

/-- The summary of a view extended by one entry. -/
theorem summarizeReg_snoc (regs : List Reg) (reg : Reg) : summarizeReg (regs ++ [reg]) = stepReg (summarizeReg regs) reg := by
  rw [summarizeReg_append]
  rfl

/-- Whether one more entry is owner `c`'s accepting finish after the given summary and passed entries. -/
def acceptCheck (c : Nat) (summary : Summary) (before : List Reg) : Reg → Option (List Reg × Pqxdh.Bytes)
  | .finish owner raw (some _) => if owner = c ∧ summary.phases c = .initSent then some (before, raw) else none
  | _ => none

/-- The scan over a list extended by one entry checks that entry only when the list has no acceptance. -/
theorem acceptedFrom_snoc (c : Nat) (summary : Summary) (before regs : List Reg) (reg : Reg) :
    acceptedFrom c summary before (regs ++ [reg]) =
      (acceptedFrom c summary before regs).or (acceptCheck c (regs.foldl stepReg summary) (before ++ regs) reg) := by
  induction regs generalizing summary before with
  | nil =>
      cases reg with
      | finish owner raw reply =>
          cases reply with
          | some payload =>
              simp only [List.nil_append, acceptedFrom, acceptCheck, List.foldl_nil, List.append_nil, Option.none_or]
          | none => rfl
      | create pin keyId owner => rfl
      | bundle owner reply => rfl
      | accept raw reply => rfl
      | build session payload reply => rfl
  | cons head rest ih =>
      have step : ∀ (summary : Summary) (before : List Reg),
          acceptedFrom c (stepReg summary head) (before ++ [head]) (rest ++ [reg]) =
            (acceptedFrom c (stepReg summary head) (before ++ [head]) rest).or
              (acceptCheck c ((head :: rest).foldl stepReg summary) (before ++ head :: rest) reg) := by
        intro summary before
        rw [ih]
        simp [List.foldl_cons, List.append_assoc]
      cases head with
      | finish owner raw reply =>
          cases reply with
          | some payload =>
              simp only [List.cons_append, acceptedFrom]
              split
              · rfl
              · exact step summary before
          | none => exact step summary before
      | create pin keyId owner => exact step summary before
      | bundle owner reply => exact step summary before
      | accept raw reply => exact step summary before
      | build session payload reply => exact step summary before

/-- The acceptance of a view extended by one entry. -/
theorem accepted_snoc (c : Nat) (regs : List Reg) (reg : Reg) :
    accepted c (regs ++ [reg]) = (accepted c regs).or (acceptCheck c (summarizeReg regs) regs reg) := by
  simpa [accepted, summarizeReg] using acceptedFrom_snoc c Summary.empty [] regs reg

/-- After a stop, the A1 failure at `c` is decided: it holds on every extension exactly when it holds on the stopped view. -/
theorem unmatched_stop (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (binding : Word32 × Std.U64)
    (c : Nat) (regs extra : List Reg) (stopped : Stop c regs) :
    Unmatched crypto codec binding c (regs ++ extra) ↔ Unmatched crypto codec binding c regs := by
  cases found : accepted c regs with
  | some result =>
      rw [Unmatched, Unmatched, accepted_append c regs extra result found, found]
  | none =>
      have failed : (summarizeReg regs).failures c = true := by
        rcases stopped with someAccepted | failed
        · rw [found] at someAccepted
          cases someAccepted
        · exact failed
      constructor
      · rintro ⟨before, raw, late, _, noFailure, _⟩
        have prefixed := acceptedFrom_late c [] regs extra (before, raw) found late
        simp only [List.nil_append] at prefixed
        obtain ⟨tail, rfl⟩ := prefixed
        rw [failures_append regs tail c failed] at noFailure
        cases noFailure
      · rintro ⟨before, raw, early, _⟩
        rw [found] at early
        cases early

/-- The prefix computed from passed entries extends them. -/
theorem untilFrom_spec {α : Type} (stop : List α → Prop) [DecidablePred stop] (passed list : List α) :
    (stop (untilFrom stop passed list) ∧ ∃ rest, passed ++ list = untilFrom stop passed list ++ rest) ∨
      untilFrom stop passed list = passed ++ list := by
  induction list generalizing passed with
  | nil => exact Or.inr (by simp [untilFrom])
  | cons entry rest ih =>
      simp only [untilFrom]
      split
      · exact Or.inl ⟨by assumption, rest, by simp⟩
      · rcases ih (passed ++ [entry]) with ⟨holds, tail, same⟩ | same
        · exact Or.inl ⟨holds, tail, by simpa using same⟩
        · exact Or.inr (by simpa using same)

/-- A list is its stopped prefix followed by the remaining entries, and the stopped prefix satisfies the predicate unless it is the whole list. -/
theorem untilStop_spec {α : Type} (stop : List α → Prop) [DecidablePred stop] (list : List α) :
    (stop (untilStop stop list) ∧ ∃ rest, list = untilStop stop list ++ rest) ∨ untilStop stop list = list := by
  simpa [untilStop] using untilFrom_spec stop [] list

/-- The A1 failure at `c` holds on a registration view exactly when it holds on the view's prefix up to the stop of `c`. -/
theorem unmatched_untilStop (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (binding : Word32 × Std.U64)
    (c : Nat) (regs : List Reg) :
    Unmatched crypto codec binding c (untilStop (Stop c) regs) ↔ Unmatched crypto codec binding c regs := by
  rcases untilStop_spec (Stop c) regs with ⟨stopped, rest, same⟩ | same
  · conv_rhs => rw [same]
    exact (unmatched_stop crypto codec binding c _ rest stopped).symm
  · rw [same]

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.step_reg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.step_reg

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.foldl_regs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.foldl_regs

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.summarize_regs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.summarize_regs

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.failures_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.failures_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.failures_foldl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.failures_foldl

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.summarizeReg_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.summarizeReg_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.failures_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.failures_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.acceptedFrom_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.acceptedFrom_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.accepted_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.accepted_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.acceptedFrom_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.acceptedFrom_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.accepted_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.accepted_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.acceptedFrom_late' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.acceptedFrom_late

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.regsOfSource_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.regsOfSource_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.summarizeReg_snoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.summarizeReg_snoc

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.acceptedFrom_snoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.acceptedFrom_snoc

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.accepted_snoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.accepted_snoc

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.unmatched_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.unmatched_stop

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.untilFrom_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.untilFrom_spec

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.untilStop_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.untilStop_spec

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.unmatched_untilStop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent.unmatched_untilStop
