-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconFrame
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementPost
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier (Objects TokenTable)
variable {n : Nat} {KemSK Platform R : Type} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

def acceptUpdate (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (word : AdapterPublicServerAgreementReceipt.Word R)
    (snapshot : RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source) :
    Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R :=
  { before with
    server := word.2.1
    rng := word.2.2
    snapshot := snapshot
    tokens := match word.1 with | .None => before.tokens | .Some token => Function.update before.tokens before.nextSession (some token)
    nextSession := match word.1 with | .None => before.nextSession | .Some _ => before.nextSession+1 }

omit material platform ed in
private theorem append_tokens (tokens : Nat→Option beaconcrypt_public_wrapper.server.RegistrationOutput)
    (sessions : List (Option peer.ConsumedRegistration)) (prior : TokenTable tokens sessions)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (consumed : peer.ConsumedRegistration)
    (related : AdapterPublicWrapperState.Token token consumed) :
    TokenTable (Function.update tokens sessions.length (some token)) (sessions++[some consumed]) := by
  intro index
  by_cases same:index=sessions.length
  · subst index
    simp only [List.getElem?_append,lt_self_iff_false,ite_false,Nat.sub_self,List.getElem?_cons_zero,Function.update_self]
    exact ⟨token,rfl,related⟩
  · rw [Function.update_of_ne same]
    by_cases earlier:index<sessions.length
    · rw [List.getElem?_append_left earlier]
      exact prior index
    · have later:sessions.length < index:=Nat.lt_of_le_of_ne (Nat.le_of_not_gt earlier) (Ne.symm same)
      have outside:sessions.length + 1 ≤ index:=later
      rw [List.getElem?_eq_none_iff.mpr (by simpa only [List.length_append,List.length_singleton] using outside)]
      have absent:sessions[index]?=none:=List.getElem?_eq_none_iff.mpr (Nat.le_of_lt later)
      simpa only [absent] using prior index

theorem tokens_returned (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (oldSessions : List (Option peer.ConsumedRegistration)) (prior : TokenTable before.tokens oldSessions)
    (count : before.nextSession=oldSessions.length) (word : AdapterPublicServerAgreementReceipt.Word R)
    (reply : Option Nat) (after : Native)
    (shape : RegistrationNativePlatformSdkAcceptSessions.Shape oldSessions (.ok reply) after.server.sessions)
    (returned : AdapterPublicServerAgreementPost.Returned view views created credential word (.ok reply,after))
    (snapshot : RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source) :
    TokenTable (acceptUpdate before word snapshot).tokens after.server.sessions := by
  rcases word with ⟨optional,self,rng⟩
  cases optional with
  | none=>
    cases reply with
    | none=>
      change after.server.sessions=oldSessions at shape
      change TokenTable before.tokens after.server.sessions
      rw [shape]
      exact prior
    | some index=>exact returned.2.elim
  | some token=>
    cases reply with
    | none=>exact returned.2.elim
    | some index=>
      change index=oldSessions.length ∧∃consumed,after.server.sessions=oldSessions++[some consumed] at shape
      obtain ⟨same,consumed,sessions⟩:=shape
      obtain ⟨actual,tokenMaterial,stored⟩:=returned.2
      have found : after.server.sessions[index]?=some (some consumed) := by
        rw [same,sessions]
        simp
      have actualEq:actual=consumed:=Option.some.inj (Option.some.inj (stored.symm.trans found))
      cases actualEq
      change TokenTable (Function.update before.tokens before.nextSession (some token)) after.server.sessions
      rw [count,sessions]
      exact append_tokens before.tokens oldSessions prior token consumed tokenMaterial

theorem count_returned (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (oldSessions : List (Option peer.ConsumedRegistration)) (count : before.nextSession=oldSessions.length)
    (word : AdapterPublicServerAgreementReceipt.Word R) (reply : Option Nat) (after : Native)
    (shape : RegistrationNativePlatformSdkAcceptSessions.Shape oldSessions (.ok reply) after.server.sessions)
    (returned : AdapterPublicServerAgreementPost.Returned view views created credential word (.ok reply,after))
    (snapshot : RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source) :
    (acceptUpdate before word snapshot).nextSession=after.server.sessions.length := by
  rcases word with ⟨optional,self,rng⟩
  cases optional with
  | none=>cases reply with
    | none=>
      change after.server.sessions=oldSessions at shape
      change before.nextSession=after.server.sessions.length
      rw [shape]
      exact count
    | some index=>exact returned.2.elim
  | some token=>cases reply with
    | none=>exact returned.2.elim
    | some index=>
      change index=oldSessions.length ∧∃consumed,after.server.sessions=oldSessions++[some consumed] at shape
      obtain ⟨_same,consumed,sessions⟩:=shape
      change before.nextSession+1=after.server.sessions.length
      simp only [sessions,List.length_append,List.length_singleton,count]

noncomputable def acceptPut (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (current : Native×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (word : AdapterPublicServerAgreementReceipt.Word R) (reply : Option Nat) (after : Native) (next : Platform)
    (returned : AdapterPublicServerAgreementPost.Returned view views created credential word (.ok reply,after))
    (shape : RegistrationNativePlatformSdkAcceptSessions.Shape current.1.server.sessions (.ok reply) after.server.sessions)
    (same : RegistrationNativePlatformSdkBeaconFrame.image after=RegistrationNativePlatformSdkBeaconFrame.image current.1)
    (snapshot : RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source)
    (backend : RegistrationNativePlatformSdkReification.persistent snapshot.committed=RegistrationNativePlatformSdkReification.persistent (after,next)) :
    RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential (after,next) := by
  have kept:=RegistrationNativePlatformSdkBeaconFrame.material view joint before.objects.beacons current.1 after same before.beacons before.indexed before.allocated
  refine { objects := acceptUpdate before.objects word snapshot
           server := returned.1
           beacons := kept.1
           tokens := tokens_returned view views created credential before.objects current.1.server.sessions before.tokens before.sessionCount word reply after shape returned snapshot
           sessionCount := count_returned view views created credential before.objects current.1.server.sessions before.sessionCount word reply after shape returned snapshot
           ownerCount := ?_
           allocated := kept.2.2
           indexed := kept.2.1
           backend := backend }
  have owners:after.beacons=current.1.beacons:=congrArg Prod.fst same
  exact before.ownerCount.trans (congrArg List.length owners).symm

theorem acceptPut_objects (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (current : Native×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (word : AdapterPublicServerAgreementReceipt.Word R) (reply : Option Nat) (after : Native) (next : Platform)
    (returned : AdapterPublicServerAgreementPost.Returned view views created credential word (.ok reply,after))
    (shape : RegistrationNativePlatformSdkAcceptSessions.Shape current.1.server.sessions (.ok reply) after.server.sessions)
    (same : RegistrationNativePlatformSdkBeaconFrame.image after=RegistrationNativePlatformSdkBeaconFrame.image current.1)
    (snapshot : RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source)
    (backend : RegistrationNativePlatformSdkReification.persistent snapshot.committed=RegistrationNativePlatformSdkReification.persistent (after,next)) :
    (acceptPut view views joint created credential current before word reply after next returned shape same snapshot backend).objects=
      acceptUpdate before.objects word snapshot := rfl

def buildUpdate (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (self : beaconcrypt_public_wrapper.server.Server)
    (snapshot : RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source) :
    Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R :=
  {before with server:=self,snapshot:=snapshot}

noncomputable def buildPut (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (current : Native×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (self : beaconcrypt_public_wrapper.server.Server) (after : Native) (next : Platform)
    (returned : AdapterPublicWrapperState.Server view views created credential self after.server)
    (sessions : after.server.sessions=current.1.server.sessions)
    (same : RegistrationNativePlatformSdkBeaconFrame.image after=RegistrationNativePlatformSdkBeaconFrame.image current.1)
    (snapshot : RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source)
    (backend : RegistrationNativePlatformSdkReification.persistent snapshot.committed=RegistrationNativePlatformSdkReification.persistent (after,next)) :
    RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential (after,next) := by
  have kept:=RegistrationNativePlatformSdkBeaconFrame.material view joint before.objects.beacons current.1 after same before.beacons before.indexed before.allocated
  refine { objects := buildUpdate before.objects self snapshot
           server := returned
           beacons := kept.1
           tokens := ?_
           sessionCount := ?_
           ownerCount := ?_
           allocated := kept.2.2
           indexed := kept.2.1
           backend := backend }
  · change TokenTable before.objects.tokens after.server.sessions
    rw [sessions]
    exact before.tokens
  · change before.objects.nextSession=after.server.sessions.length
    rw [sessions]
    exact before.sessionCount
  · have owners:after.beacons=current.1.beacons:=congrArg Prod.fst same
    exact before.ownerCount.trans (congrArg List.length owners).symm

theorem buildPut_objects (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (current : Native×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (self : beaconcrypt_public_wrapper.server.Server) (after : Native) (next : Platform)
    (returned : AdapterPublicWrapperState.Server view views created credential self after.server)
    (sessions : after.server.sessions=current.1.server.sessions)
    (same : RegistrationNativePlatformSdkBeaconFrame.image after=RegistrationNativePlatformSdkBeaconFrame.image current.1)
    (snapshot : RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source)
    (backend : RegistrationNativePlatformSdkReification.persistent snapshot.committed=RegistrationNativePlatformSdkReification.persistent (after,next)) :
    (buildPut view views joint created credential current before self after next returned sessions same snapshot backend).objects=
      buildUpdate before.objects self snapshot := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.tokens_returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.tokens_returned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.count_returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.count_returned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.acceptPut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.acceptPut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.acceptPut_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.acceptPut_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.buildPut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.buildPut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.buildPut_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer.buildPut_objects
