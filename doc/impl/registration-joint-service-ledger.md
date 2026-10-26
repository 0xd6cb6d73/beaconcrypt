# Global registration service-query ledger

`PqxdhRegistrationJointServiceCosts` and `PqxdhRegistrationJointServiceLedger` contain sixteen guarded statements. They give all-reply structural query bounds for the complete executable client introduced by `PqxdhRegistrationJointServiceSchedule`. Every bound counts attempts, including optional service failures, missing owner addresses, writer failures, inactive phases and repeated requests. The bounds hold for every encoded owner registry; they do not require generated ownership, acceptance, freshness or an honest selected key.

Let the original nine source-attempt caps be `qCoin`, `qCreate`, `qBundle`, `qAccept`, `qBuild`, `qFinish`, `qHmac`, `qHash` and `qRead`. The client's emitted backend requests satisfy the following complete partition.

| Emitted backend capability | Global allowance |
| --- | --- |
| Joint identity creation | `qCreate` |
| Signing | `3 * qBundle` |
| Joint identity DH | `qFinish` |
| KEM creation | `qCreate` |
| Logical KEM decapsulation | `qFinish` |
| Local uniform query | `qCoin + 32 * qCreate + 32 * qBundle` |
| Original native finish-tail callback | `56 * qFinish` |
| Original native Server accept | `qAccept` |
| Original native Server build | `qBuild` |
| Original public HMAC callback | `qHmac` |
| Original public hash callback | `qHash` |
| Original current Server kernel read | `qRead` |
| Every other backend capability | `0` |

The last class includes private identity/KEM reveal capabilities and the dynamic identity service's separate local-uniform interface. Those capabilities exist in the backend type but the current client never emits them. A later live-field reveal extension will change this ledger explicitly. A failed callback remains a counted call even when it returns None. The matrix is an upper bound, so an inactive phase or early failure may use less than its allowance.

In `ServiceCosts`, `coins_queries` retains the actual one-for-one local draw allowance. `creation_queries` separates identity creation, the 32-byte prekey draw and KEM creation. `signing_queries` checks the actual ordered signing program and excludes every unrelated service class. `writing_queries` proves that the original optional codec writer emits no backend call; its real local codec work remains present. `after_queries` retains the complete optional source publication continuation. `bundle_queries` joins the Fresh draw, retained-coin phase and terminal phases without sampling extra randomness.

In `ServiceLedger`, `pool_queries` and `finish_queries` preserve selective query counts under the actual routing functions. `finish_partition` relates the finer global partition to the existing complete finish component ledger. `finish_bound` consequently bounds decapsulation and joint DH by one each, native-tail calls by 56 and unrelated calls by zero. `create_bound`, `bundle_bound` and `finish_owner_bound` include actual owner lookup, optional result and owner installation. `query_bound` checks the sparse source-to-service matrix for every public handler. `cost_total` expands all nine matrix coordinates to the displayed allowances. `program_bound` applies the existing finite weighted structural composition to an arbitrary adaptive source program and its complete client owner state. The certificate covers every possible typed reply, so no successful branch or actual adversary schedule is selected to obtain a smaller count.

These are emitted logical calls, not a claim that their implementations consume one machine operation or one random query. The previously checked `ServiceSchedule.program_uniform` still charges all actual native Server/public/tail work and every KEM direct/base draw: `qCoin + (64 + G) * qCreate + 32 * qBundle + (96 + E) * qAccept + 64 * qBuild + 69 * max(64, D) * qFinish + 64 * qHmac + 64 * qHash`. Native identity creation includes its own seed draw, KEM operations include their stated internal oracle bills, and the initial typed Server setup retains its separate allowance. The deterministic optional writer consumes local computation but no backend oracle request. No ambient continuation is declared free.

The scope is the existing one-Server/many-Beacon typed registration schedule. These results establish no primitive security advantage, target/session selection factor, freshness property or computational/symbolic composition hop. Current-live-field reveal extension, Server internal joint-use compilation, multi-Server imported pending handles, raw initialization and the global reduction consumer remain open. The existing downstream restricted consumers keep their restrictions. Primitive, codec and source interpreter contracts are unchanged; no snapshot/persistence reasoning or Rust/ProVerif change is included.

Both modules pass direct Lean 4.34.0 checks under the shared one-thread lock. Every public statement has an exact standard-axiom guard. Independent review and the separately reviewed central import/inventory integration remain publication requirements.
