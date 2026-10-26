# Exact final source prefixes

`PqxdhRecordFactsOriginOrdinalFinalPrefix` contains three structural statements connecting existing literal execution witnesses. They preserve the complete private state, actual typed callback replies, attempted sealing history, residual program and exact chronological sealing-cut list. They add no primitive contract or probability assumption.

`path_prefix` takes one complete supported `Path` and exposes its final boundary as a `Prefix` ending at the actual returned value and state. The earlier cut list is exactly the original path's list. The proof reuses every literal step, so it does not substitute a different execution with the same final output.

`reach_prefix` decorates an existing exact `Reach` witness with a cut list while retaining its original program, current residual work, complete current state and attempted-label history. This supplies the chronology required by the marker-prefix consumer when the selected ordinal scanner gives a supported source prefix.

`source_final_entry` combines `path_prefix` with the existing initialized-source entry provenance theorem. A retained dictionary entry selects a cut from this same complete execution, its actual supported full reply, matching material, empty before-dictionary, source-derived fresh point, and attempted ordinal strictly below `budget.sends`. Its earlier and later prefixes concatenate to exactly the input cut list, including failed writers and all source sealing constructors. The result assumes the existing source budget only to obtain that ordinal cap.

The last theorem places the creation before the final boundary. It does not itself place creation before a particular earlier accepted receive. A consumer requiring that stronger chronological fact must use the corresponding receive prefix or independently discharge the supported marked-continuation event obligation. No future-cut-to-past-acceptance inference, writer-success conditioning, final event cover, forgery probability, or completed origin claim is introduced here.

Validation is a direct Lean module check with three exact axiom guards allowing only `propext`, `Classical.choice`, and `Quot.sound`. Existing source and reduction resource bills remain unchanged.
