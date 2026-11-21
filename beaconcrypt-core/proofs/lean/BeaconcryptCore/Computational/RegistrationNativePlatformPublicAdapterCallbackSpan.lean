-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing
/-! Actual callback logs are a sequence of one opening, source stages and one closing. A given block in that sequence identifies its exact executed callback, strict earlier log and complete prefix/suffix paths, even when equal-valued blocks occur repeatedly. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan
open RegistrationNativeStageTrace (Call Path Executed)
variable {Q S E A :Type} {spec :OracleSpec Q}
variable (tag :E→Nat)

theorem strip_no_open (front after leading :List E) (opened :E) (trailing :List E)
    (quiet :∀item∈front,tag item≠1) (opening :tag opened=1)
    (same :front++after=leading++opened::trailing) :
    ∃between,leading=front++between ∧after=between++opened::trailing :=by
  induction front generalizing leading with
  | nil=>exact ⟨leading,rfl,same⟩
  | cons head rest ih=>
    cases leading with
    | nil=>
      have equal :head=opened:=(List.cons.inj same).1
      exact False.elim (quiet head (List.mem_cons.mpr (Or.inl rfl)) (equal ▸opening))
    | cons first tail=>
      obtain ⟨equal,following⟩:=List.cons.inj same
      subst first
      obtain ⟨between,split,kept⟩:=ih tail (fun item member=>quiet item (List.mem_cons_of_mem _ member)) following
      exact ⟨between,by rw [split];rfl,kept⟩

theorem close_split (left right :List E) (leftClose rightClose :E) (leftTail rightTail :List E)
    (leftStages :∀item∈left,tag item=0) (rightStages :∀item∈right,tag item=0)
    (leftClosing :tag leftClose=2) (rightClosing :tag rightClose=2)
    (same :left++leftClose::leftTail=right++rightClose::rightTail) :
    left=right ∧leftClose=rightClose ∧leftTail=rightTail :=by
  induction left generalizing right with
  | nil=>
    cases right with
    | nil=>exact ⟨rfl,(List.cons.inj same).1,(List.cons.inj same).2⟩
    | cons head tail=>
      have equal :leftClose=head:=(List.cons.inj same).1
      have zero:=rightStages head (List.mem_cons.mpr (Or.inl rfl))
      rw [←equal,leftClosing] at zero
      cases zero
  | cons head rest ih=>
    cases right with
    | nil=>
      have equal :head=rightClose:=(List.cons.inj same).1
      have zero:=leftStages head (List.mem_cons.mpr (Or.inl rfl))
      rw [equal,rightClosing] at zero
      cases zero
    | cons first tail=>
      obtain ⟨equal,following⟩:=List.cons.inj same
      subst first
      obtain ⟨stages,closing,later⟩:=ih tail
        (fun item member=>leftStages item (List.mem_cons_of_mem _ member))
        (fun item member=>rightStages item (List.mem_cons_of_mem _ member)) following
      exact ⟨congrArg (List.cons head) stages,closing,later⟩

variable (implementation :QueryImpl spec (StateT S ProbComp)) (events :S→List E)
variable (opened closed :Call spec S→E)
variable (block :∀call,Executed implementation call→∃middle :List E,
  (∀item∈middle,tag item=0) ∧events call.after=events call.before++opened call::(middle++[closed call]))

include block in
theorem appends {before after :S} {calls :List (Call spec S)}
    (actual :Path implementation before calls after) :
    ∃suffix,events after=events before++suffix :=by
  induction actual with
  | nil=>exact ⟨[],(List.append_nil _).symm⟩
  | cons call called rest last following ih=>
    obtain ⟨middle,_stages,current⟩:=block call called
    obtain ⟨later,kept⟩:=ih
    exact ⟨opened call::(middle++closed call::later),by rw [kept,current];simp only [List.append_assoc,List.cons_append,List.nil_append]⟩

variable (closing :∀call,tag (closed call)=2)

include block closing in
theorem span {before after :S} {calls :List (Call spec S)}
    (actual :Path implementation before calls after) (leading middle trailing :List E) (startMark endMark :E)
    (startTag :tag startMark=1) (endTag :tag endMark=2) (middleTags :∀item∈middle,tag item=0)
    (observed :events after=events before++(leading++startMark::(middle++endMark::trailing))) :
    ∃(prior later :List (Call spec S)) (call :Call spec S),calls=prior++call::later ∧
      Path implementation before prior call.before ∧Executed implementation call ∧Path implementation call.after later after ∧
      events call.before=events before++leading ∧opened call=startMark ∧closed call=endMark ∧
      events call.after=events before++(leading++startMark::(middle++[endMark])) :=by
  induction actual generalizing leading with
  | nil state=>
    have sizes:=congrArg List.length observed
    simp only [List.length_append,List.length_cons] at sizes
    omega
  | cons call called rest last following ih=>
    obtain ⟨actualStages,stageTags,emitted⟩:=block call called
    obtain ⟨tailEvents,kept⟩:=appends tag implementation events opened closed block following
    have expanded :events last=events call.before++(opened call::(actualStages++closed call::tailEvents)) :=by
      rw [kept,emitted]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    have split :opened call::(actualStages++closed call::tailEvents)=leading++startMark::(middle++endMark::trailing):=
      List.append_cancel_left (expanded.symm.trans observed)
    cases leading with
    | nil=>
      obtain ⟨sameOpen,sameTail⟩:=List.cons.inj split
      obtain ⟨sameStages,sameClose,_sameFollowing⟩:=close_split tag actualStages middle (closed call) endMark tailEvents trailing
        stageTags middleTags (closing call) endTag sameTail
      refine ⟨[],rest,call,rfl,.nil _,called,following,(List.append_nil _).symm,sameOpen,sameClose,?_⟩
      simpa only [List.nil_append,sameOpen,sameStages,sameClose] using emitted
    | cons head restLeading=>
      obtain ⟨sameHead,sameTail⟩:=List.cons.inj split
      have quiet :∀item∈actualStages++[closed call],tag item≠1 :=by
        intro item member
        rcases List.mem_append.mp member with stage|lastItem
        · rw [stageTags item stage]
          decide
        · have equal :item=closed call :=by simpa only [List.mem_singleton] using lastItem
          subst item
          rw [closing call]
          decide
      have splitQuiet :(actualStages++[closed call])++tailEvents=restLeading++startMark::(middle++endMark::trailing):=by
        rw [List.append_assoc]
        exact sameTail
      obtain ⟨between,leadingEq,laterEq⟩:=strip_no_open tag (actualStages++[closed call]) tailEvents restLeading startMark
        (middle++endMark::trailing) quiet startTag splitQuiet
      have followingObserved :events last=events call.after++(between++startMark::(middle++endMark::trailing)):=by
        rw [kept,laterEq]
      obtain ⟨prior,later,next,callsEq,previous,executed,after,atBefore,atOpen,atClose,atAfter⟩:=ih between followingObserved
      have beforeEq :events call.after++between=events call.before++(head::restLeading) :=by
        rw [emitted,leadingEq,←sameHead]
        simp only [List.append_assoc,List.cons_append,List.nil_append]
      refine ⟨call::prior,later,next,?_,.cons call called _ _ previous,executed,after,atBefore.trans beforeEq,atOpen,atClose,?_⟩
      · rw [callsEq]
        rfl
      · rw [←List.append_assoc,beforeEq] at atAfter
        simpa only [List.append_assoc] using atAfter

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan.strip_no_open' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan.strip_no_open
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan.close_split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan.close_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan.appends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan.appends
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan.span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan.span
