-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope
/-! Literal forwarded public prefixes pass through the first-selector transformer unchanged, retaining their original reply-dependent continuation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope
open RegistrationNativeIdentityTemplateSelectionCut.Original (Old Cut stop)
open RegistrationNativeIdentityTemplatePublicPrefix (Allowed)
variable {A B : Type}

/-- A genuine forwarded prefix reaches no selector or private marker. -/
theorem stop_forwarded (work : OracleComp Old A) (allowed : work.AllQueriesSatisfy Allowed) :
    stop work=Cut.returned <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value=>rfl
  | query_bind query next ih=>
      obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      rw [RegistrationNativeIdentityTemplateSelectionCut.Original.step]
      rcases query with (((protocol|selection)|scanned)|described)|marker
      · simp only [map_bind]
        exact bind_congr (fun reply=>ih reply (later reply))
      · exact False.elim first
      · simp only [map_bind]
        exact bind_congr (fun reply=>ih reply (later reply))
      · simp only [map_bind]
        exact bind_congr (fun reply=>ih reply (later reply))
      · exact False.elim first

/-- The complete same public prefix precedes the first selector of its unchanged original suffix. -/
theorem stop_bind_forwarded (work : OracleComp Old A) (next : A → OracleComp Old B)
    (allowed : work.AllQueriesSatisfy Allowed) :
    stop (work >>= next)=work >>= fun value=>stop (next value) := by
  rw [RegistrationNativeIdentityTemplateSelectionCut.Original.bind,stop_forwarded work allowed,bind_map_left]

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.stop_forwarded' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.stop_forwarded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.stop_bind_forwarded' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.stop_bind_forwarded
