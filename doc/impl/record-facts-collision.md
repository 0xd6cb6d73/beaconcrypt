# Adaptive digest collision accounting

`PqxdhRecordFactsCollision` proves a statistical bound for an explicit independent uniform-digest service. It is a counting tool for the record binding proof. It does not assume or prove that the production binding event is already an event of this service.

The client chooses each request adaptively from all previous replies. A digest request is tagged as a target draw or an ordinary draw before that draw is sampled. Every digest is returned to the client. Arbitrary finite uniform-coin queries are also available. The state retains the full value lists and an absorbing collision flag. A collision is an equality involving at least one target draw; equality between two ordinary draws alone does not set the flag.

`uniform_finset` and `uniform_list` bound a fresh uniform value's chance of hitting an explicit finite candidate collection. Repeated candidates reduce the probability. `bind_le_bad_add`, `uniform_bind_list`, and `bind_le` average continuation bounds over the actual prefix distribution. They do not condition on an adversarially chosen successful publication or discard the adaptive continuation.

`run_bound` permits any clean initial history and all-reply query caps of `S` target draws and `H` ordinary draws. If the initial lists have lengths `A` and `B`, the bound is `(S(A+B+S+H)+HA)/|Digest|`. A target draw pays for comparisons with both prior lists; an ordinary draw pays only for comparisons with prior targets. `target_potential` and `ordinary_potential` justify these charges. This counts each target–ordinary pair once, in whichever order its values were drawn.

`empty_bound` specializes to initially empty lists and gives `S(S+H)/|Digest|`. `ctxDigest_bound` uses the existing checked cardinality of the actual 64-byte `CtxDigest` type to give `S(S+H)/2^512`. This is a union bound, so it may exceed one. No primitive security advantage or computational assumption enters it.

The query premise bounds digest draws, not every source call. Coins are retained but do not create a digest-collision opportunity. An application must prove how source and reduction query counts map to this service; this module declares no ambient work free. In particular, shared-cache hits are not fresh draws, and a private lookup before a seal cannot simply be assumed absent. The source application must preserve those correlations or justify postponing an unobserved lookup through a complete-continuation law, then account for the original interpreter's draws separately.

Ten public theorems have exact axiom guards using only Lean's ordinary axioms. The direct module check uses the private output prefix over central `959b715460dbc271ff2c617df9dd64f1d0f73234`. The global `BindingStatement`, its source event inclusion, and its full query accounting remain separate obligations. No Rust or ProVerif change is part of this module.
