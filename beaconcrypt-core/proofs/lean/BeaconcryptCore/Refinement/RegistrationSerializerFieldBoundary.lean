-- SPDX-License-Identifier: 0BSD
/-! Function-boundary algebra used by the checked serializer source preparation.
The complete result and mutable output remain in the arbitrary effect; captured
Boolean values and the borrowed payload are passed unchanged. The source manifest
checks the identical helper body and exact argument list. This algebra does not
identify primitive codec operations or assert a complete public codec law. -/
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary
universe u v
variable {m : Type u → Type v} {P S R : Type u}

theorem helper_eta (work : P → S → Bool → Bool → m (R × S))
    (payload : P) (output : S) (low high : Bool) :
    ((fun captured state lo hi => work captured state lo hi) payload output low high) =
      work payload output low high := rfl

theorem continuation_preserved [Monad m] {B : Type u}
    (work : P → S → Bool → Bool → m (R × S))
    (payload : P) (output : S) (low high : Bool) (next : R → S → m B) :
    (((fun captured state lo hi => work captured state lo hi) payload output low high) >>=
      fun result => next result.1 result.2) =
    (work payload output low high >>= fun result => next result.1 result.2) := rfl
end BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary
/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta
/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.continuation_preserved' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.continuation_preserved
