# Installed receive-handle classification

`PqxdhRecordFactsOriginMarkerLocation` proves that every successful literal Server or Beacon receive uses a kernel already installed before that command. This classification holds for arbitrary typed service replies: the proof reads only the actual source lookup and rejection branches. The installed kernel is either caller-known or associated with a hidden session slot.

`stored_location` classifies an exact kernel lookup. `server_location` and `beacon_location` derive this lookup classification from successful source command support, excluding missing peers and inactive owners. `location_mono` transports the installed classification under the actual forward control transition and separate caller-known persistence. `slot_before` then derives the earlier hidden slot from a later hidden slot only after this prior installation has been proved. It excludes caller-known-to-hidden conversion using known-handle persistence; it does not reverse the forward transition relation for arbitrary handles.

These five structural statements supply the marked receive ledger proof with before-command handle provenance. They add no cryptographic assumption and assert no probability bound.
