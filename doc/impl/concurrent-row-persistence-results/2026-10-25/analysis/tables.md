# Concurrent persistence analysis

Five explicit primary axes are used: PostgreSQL 1/100/1000 and SQLite 1/100. The first four are individually retained complete reports from two incomplete/stopped campaigns; only the final PostgreSQL campaign has a complete collection index. SQLite 1000 was stopped at the user's direction and is excluded. No campaign completion is fabricated and no timing-based attempt selection is performed.

Snapshot uses one serial owner and one database connection. Row and cached-row use stable peer lanes with independent owners/connections and equal total queue bounds. Snapshot/row ratios include this ownership difference; row/cached-row comparisons share the owner topology.

All offered requests drain successfully. Planned-arrival response time includes scheduler backlog, blocked admission, owner-queue wait, dispatch, native API service, and completion overhead. No automatic retries or discarded overload are accepted.

Periodic work is paced. Its full-batch completion rate can be arrival-limited; use deadlines, response latency and backlog to assess it rather than calling a near-equal batch duration equal capacity. Burst MB/s uses all offered plaintext bytes and full drain time.

All percentiles are computed within one trial. A response-p95 ratio divides the two arms' per-trial p95 values; it is not a p95 of per-callback ratios. Across-trial aggregates summarize trial statistics or within-trial paired ratios; they never pool request latencies across trials. Ratios whose denominator is zero are null with explicit counts, not silently replaced.

source_backlog_ns is computed per callback as scheduler_lag_ns + enqueue_backpressure_ns before taking percentiles. Percentiles of stages cannot be added to obtain a response percentile.

queue_wait_ns includes waiting for the serial owner. owner_wait_ns is dequeue-to-native dispatch overhead, not a separate contended owner mutex. Native API service includes database work; database client spans and overlap are not pure crypto or physical database CPU/write concurrency.

Overlapping interval durations are reported as unions by the validated summarizer, never added as wall time. Logical SQL counters and plaintext bytes are not physical I/O. No significance, cross-window causal comparison, or Mythic end-to-end speedup is inferred.

Old PostgreSQL 1/100 use source e26909a; SQLite 1/100 and PostgreSQL 1000 use 77d5633d. The change raises only SQLite busy waiting from 5 to 600 seconds, with its settings test/documentation. PostgreSQL and common/library implementation are unchanged. Preserve both builds and separate collection windows.

The final PostgreSQL 1000 window permits outside VM CPU below 1 core per process and 2 cores aggregate; earlier retained windows used 0.25 and 0.5. Host steal remains recorded only. These policy differences preclude claiming a controlled cross-window scaling experiment or an isolated physical host.

Per-trial values below use milliseconds; throughput uses decimal MB/s. Complete numeric values and all cohort breakdowns are in the CSV files.

## postgres: 1 registered peers, 1 active / small_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 2/2 | 2/2 | 2.235/2.585/2.585 | 0.109 | 0.041 | 2.434 | 1/1 | 1/1 | 2.585 | — |
| 1 | row | 2/2 | 2/2 | 2.331/2.687/2.687 | 0.088 | 0.065 | 2.532 | 1/1 | 2/2 | 2.687 | — |
| 1 | cached_row | 2/2 | 2/2 | 2.422/2.667/2.667 | 0.142 | 0.072 | 2.451 | 1/1 | 1/1 | 2.422 | — |
| 2 | snapshot | 2/2 | 2/2 | 2.467/2.587/2.587 | 0.115 | 0.056 | 2.418 | 1/1 | 1/1 | 2.467 | — |
| 2 | row | 2/2 | 2/2 | 2.653/3.189/3.189 | 0.105 | 0.088 | 3.056 | 1/1 | 2/2 | 2.653 | — |
| 2 | cached_row | 2/2 | 2/2 | 2.242/2.302/2.302 | 0.092 | 0.042 | 2.177 | 1/1 | 1/1 | 2.302 | — |
| 3 | snapshot | 2/2 | 2/2 | 2.131/2.283/2.283 | 0.158 | 0.052 | 2.107 | 1/1 | 1/1 | 2.283 | — |
| 3 | row | 2/2 | 2/2 | 2.233/2.520/2.520 | 0.133 | 0.076 | 2.308 | 1/1 | 2/2 | 2.520 | — |
| 3 | cached_row | 2/2 | 2/2 | 1.875/2.609/2.609 | 0.129 | 0.074 | 2.404 | 1/1 | 1/1 | 2.609 | — |

## postgres: 1 registered peers, 1 active / mixed_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 2/2 | 2/2 | 3.682/4.435/4.435 | 0.104 | 0.053 | 4.288 | 1/1 | 1/1 | 3.682 | — |
| 1 | row | 2/2 | 2/2 | 3.371/5.850/5.850 | 0.108 | 0.065 | 5.675 | 1/1 | 2/2 | 5.850 | — |
| 1 | cached_row | 2/2 | 2/2 | 2.255/3.583/3.583 | 0.089 | 0.122 | 3.369 | 1/1 | 1/1 | 3.583 | — |
| 2 | snapshot | 2/2 | 2/2 | 2.717/2.969/2.969 | 0.107 | 0.056 | 2.825 | 1/1 | 1/1 | 2.969 | — |
| 2 | row | 2/2 | 2/2 | 3.082/4.112/4.112 | 0.119 | 0.047 | 3.962 | 1/1 | 2/2 | 3.082 | — |
| 2 | cached_row | 2/2 | 2/2 | 3.099/3.294/3.294 | 0.096 | 0.073 | 3.144 | 1/1 | 1/1 | 3.099 | — |
| 3 | snapshot | 2/2 | 2/2 | 2.831/3.224/3.224 | 0.125 | 0.054 | 3.067 | 1/1 | 1/1 | 3.224 | — |
| 3 | row | 2/2 | 2/2 | 2.491/2.965/2.965 | 0.104 | 0.110 | 2.749 | 1/1 | 2/2 | 2.965 | — |
| 3 | cached_row | 2/2 | 2/2 | 2.391/5.211/5.211 | 0.085 | 0.047 | 5.078 | 1/1 | 1/1 | 5.211 | — |

## postgres: 1 registered peers, 1 active / small_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 20/20 | 20/20 | 3.583/6.603/8.194 | 0.128 | 0.057 | 6.426 | 1/1 | 1/1 | 3.599 | — |
| 1 | row | 20/20 | 20/20 | 3.774/6.052/7.826 | 0.117 | 0.084 | 5.890 | 1/1 | 2/2 | 4.977 | — |
| 1 | cached_row | 20/20 | 20/20 | 3.643/4.555/4.865 | 0.126 | 0.075 | 4.393 | 1/1 | 1/1 | 4.452 | — |
| 2 | snapshot | 20/20 | 20/20 | 3.070/5.249/5.373 | 0.127 | 0.052 | 5.069 | 1/1 | 1/1 | 3.070 | — |
| 2 | row | 20/20 | 20/20 | 3.843/8.025/8.389 | 0.110 | 0.064 | 7.895 | 1/1 | 2/2 | 2.472 | — |
| 2 | cached_row | 20/20 | 20/20 | 3.879/7.098/9.239 | 0.130 | 0.060 | 6.944 | 1/1 | 1/1 | 2.614 | — |
| 3 | snapshot | 20/20 | 20/20 | 2.386/3.398/3.447 | 0.134 | 0.062 | 3.245 | 1/1 | 1/1 | 3.287 | — |
| 3 | row | 20/20 | 20/20 | 2.407/4.461/5.354 | 0.120 | 0.064 | 4.318 | 1/1 | 2/2 | 2.386 | — |
| 3 | cached_row | 20/20 | 20/20 | 2.393/3.336/3.608 | 0.111 | 0.077 | 3.207 | 1/1 | 1/1 | 2.293 | — |

## postgres: 1 registered peers, 1 active / mixed_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 20/20 | 20/20 | 3.632/9.186/9.305 | 0.110 | 0.081 | 9.022 | 1/1 | 1/1 | 3.167 | — |
| 1 | row | 20/20 | 20/20 | 3.683/5.224/7.491 | 0.121 | 0.063 | 5.080 | 1/1 | 2/2 | 2.665 | — |
| 1 | cached_row | 20/20 | 20/20 | 2.475/4.080/5.883 | 0.222 | 0.101 | 3.922 | 1/1 | 1/1 | 5.883 | — |
| 2 | snapshot | 20/20 | 20/20 | 2.366/4.685/7.439 | 0.128 | 0.080 | 4.482 | 1/1 | 1/1 | 3.372 | — |
| 2 | row | 20/20 | 20/20 | 2.615/4.152/4.167 | 0.143 | 0.067 | 3.982 | 1/1 | 2/2 | 2.447 | — |
| 2 | cached_row | 20/20 | 20/20 | 2.419/3.576/7.374 | 0.111 | 0.097 | 3.366 | 1/1 | 1/1 | 7.374 | — |
| 3 | snapshot | 20/20 | 20/20 | 3.072/4.335/5.015 | 0.145 | 0.062 | 4.157 | 1/1 | 1/1 | 2.082 | — |
| 3 | row | 20/20 | 20/20 | 2.471/4.059/4.147 | 0.107 | 0.053 | 3.922 | 1/1 | 2/2 | 2.390 | — |
| 3 | cached_row | 20/20 | 20/20 | 2.392/3.534/5.018 | 0.118 | 0.057 | 3.369 | 1/1 | 1/1 | 2.189 | — |

## postgres: 1 registered peers, 1 active / small_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 200/200 | 200/200 | 1.785/3.659/4.406 | 0.103 | 0.057 | 3.556 | 1/1 | 1/1 | 1.692 | — |
| 1 | row | 200/200 | 200/200 | 2.165/4.685/5.710 | 0.100 | 0.059 | 4.537 | 1/1 | 2/2 | 1.624 | — |
| 1 | cached_row | 200/200 | 200/200 | 1.867/3.955/4.449 | 0.099 | 0.057 | 3.802 | 1/1 | 1/1 | 1.591 | — |
| 2 | snapshot | 200/200 | 200/200 | 1.729/3.888/6.145 | 0.103 | 0.050 | 3.744 | 1/1 | 1/1 | 2.483 | — |
| 2 | row | 200/200 | 200/200 | 2.025/4.482/6.672 | 0.098 | 0.057 | 4.256 | 1/1 | 2/2 | 6.462 | — |
| 2 | cached_row | 200/200 | 200/200 | 1.806/3.387/4.334 | 0.101 | 0.055 | 3.283 | 1/1 | 1/1 | 3.349 | — |
| 3 | snapshot | 200/200 | 200/200 | 1.756/4.110/4.968 | 0.106 | 0.053 | 3.996 | 1/1 | 1/1 | 3.681 | — |
| 3 | row | 200/200 | 200/200 | 1.880/3.248/6.695 | 0.102 | 0.046 | 3.134 | 1/1 | 2/2 | 1.839 | — |
| 3 | cached_row | 200/200 | 200/200 | 1.776/3.190/4.202 | 0.102 | 0.054 | 3.079 | 1/1 | 1/1 | 2.807 | — |

## postgres: 1 registered peers, 1 active / mixed_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 200/200 | 200/200 | 1.803/2.959/4.762 | 0.107 | 0.057 | 2.847 | 1/1 | 1/1 | 1.669 | — |
| 1 | row | 200/200 | 200/200 | 2.728/4.283/7.083 | 0.105 | 0.056 | 4.132 | 1/1 | 2/2 | 1.669 | — |
| 1 | cached_row | 200/200 | 200/200 | 1.846/2.990/4.881 | 0.105 | 0.055 | 2.859 | 1/1 | 1/1 | 1.863 | — |
| 2 | snapshot | 200/200 | 200/200 | 1.951/3.956/5.104 | 0.107 | 0.060 | 3.800 | 1/1 | 1/1 | 2.669 | — |
| 2 | row | 200/200 | 200/200 | 1.984/3.607/5.004 | 0.116 | 0.058 | 3.428 | 1/1 | 2/2 | 2.010 | — |
| 2 | cached_row | 200/200 | 200/200 | 1.815/3.074/3.662 | 0.130 | 0.055 | 2.903 | 1/1 | 1/1 | 2.090 | — |
| 3 | snapshot | 200/200 | 200/200 | 1.870/3.796/4.234 | 0.118 | 0.054 | 3.660 | 1/1 | 1/1 | 1.882 | — |
| 3 | row | 200/200 | 200/200 | 2.732/4.619/7.855 | 0.099 | 0.058 | 4.513 | 1/1 | 2/2 | 2.950 | — |
| 3 | cached_row | 200/200 | 200/200 | 2.113/4.621/6.031 | 0.121 | 0.059 | 4.493 | 1/1 | 1/1 | 1.642 | — |

## postgres: 1 registered peers, 1 active / small_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 400/400 | 400/400 | 1.686/3.641/8.538 | 0.097 | 0.056 | 3.346 | 1/1 | 1/1 | 1.610 | — |
| 1 | row | 400/400 | 400/400 | 1.878/3.197/4.599 | 0.109 | 0.063 | 3.028 | 1/1 | 2/2 | 1.786 | — |
| 1 | cached_row | 400/400 | 400/400 | 1.737/2.897/4.034 | 0.107 | 0.057 | 2.739 | 1/1 | 1/1 | 2.681 | — |
| 2 | snapshot | 400/400 | 400/400 | 1.624/3.354/5.254 | 0.101 | 0.045 | 3.158 | 1/1 | 1/1 | 1.544 | — |
| 2 | row | 400/400 | 400/400 | 2.593/5.945/8.665 | 0.094 | 0.818 | 5.483 | 1/1 | 2/2 | 8.328 | — |
| 2 | cached_row | 400/400 | 400/400 | 2.532/6.264/10.074 | 0.105 | 1.149 | 4.890 | 1/1 | 1/1 | 6.409 | — |
| 3 | snapshot | 400/400 | 400/400 | 2.502/4.413/7.313 | 0.109 | 0.054 | 4.009 | 1/1 | 1/1 | 2.646 | — |
| 3 | row | 400/400 | 400/400 | 2.972/7.825/10.687 | 0.108 | 2.615 | 5.017 | 1/1 | 2/2 | 8.645 | — |
| 3 | cached_row | 400/400 | 400/400 | 1.743/3.679/6.427 | 0.102 | 0.039 | 3.400 | 1/1 | 1/1 | 2.552 | — |

## postgres: 1 registered peers, 1 active / mixed_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 400/400 | 400/400 | 1.693/3.304/4.516 | 0.104 | 0.044 | 3.167 | 1/1 | 1/1 | 1.547 | — |
| 1 | row | 400/400 | 400/400 | 1.793/3.276/4.575 | 0.110 | 0.053 | 3.129 | 1/1 | 2/2 | 1.738 | — |
| 1 | cached_row | 400/400 | 400/400 | 2.020/4.213/6.730 | 0.106 | 0.054 | 3.969 | 1/1 | 1/1 | 1.677 | — |
| 2 | snapshot | 400/400 | 400/400 | 1.622/3.104/11.563 | 0.100 | 0.057 | 2.864 | 1/1 | 1/1 | 1.612 | — |
| 2 | row | 400/400 | 400/400 | 1.869/3.470/4.310 | 0.107 | 0.041 | 3.290 | 1/1 | 2/2 | 1.734 | — |
| 2 | cached_row | 400/400 | 400/400 | 1.695/3.378/6.192 | 0.108 | 0.056 | 2.917 | 1/1 | 1/1 | 1.533 | — |
| 3 | snapshot | 400/400 | 400/400 | 2.475/4.037/7.108 | 0.107 | 0.053 | 3.816 | 1/1 | 1/1 | 1.486 | — |
| 3 | row | 400/400 | 400/400 | 2.201/4.305/6.302 | 0.105 | 0.051 | 4.050 | 1/1 | 2/2 | 1.674 | — |
| 3 | cached_row | 400/400 | 400/400 | 1.902/3.706/4.589 | 0.096 | 0.056 | 3.530 | 1/1 | 1/1 | 1.551 | — |

## postgres: 1 registered peers, 1 active / heterogeneous_mixed

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 2/2 | 2/2 | 2.083/3.422/3.422 | 0.115 | 0.047 | 3.285 | 1/1 | 1/1 | 3.422 | — |
| 1 | row | 2/2 | 2/2 | 2.502/2.760/2.760 | 0.169 | 0.087 | 2.502 | 1/1 | 2/2 | 2.760 | — |
| 1 | cached_row | 2/2 | 2/2 | 2.584/2.683/2.683 | 0.091 | 0.068 | 2.535 | 1/1 | 1/1 | 2.683 | — |
| 2 | snapshot | 2/2 | 2/2 | 1.898/6.958/6.958 | 0.141 | 0.050 | 6.766 | 1/1 | 1/1 | 6.958 | — |
| 2 | row | 2/2 | 2/2 | 3.141/3.156/3.156 | 0.097 | 0.053 | 3.017 | 1/1 | 2/2 | 3.156 | — |
| 2 | cached_row | 2/2 | 2/2 | 2.662/3.371/3.371 | 0.106 | 0.064 | 3.219 | 1/1 | 1/1 | 2.662 | — |
| 3 | snapshot | 2/2 | 2/2 | 2.502/3.095/3.095 | 0.104 | 0.073 | 2.946 | 1/1 | 1/1 | 2.502 | — |
| 3 | row | 2/2 | 2/2 | 2.097/2.449/2.449 | 0.101 | 0.041 | 2.305 | 1/1 | 2/2 | 2.449 | — |
| 3 | cached_row | 2/2 | 2/2 | 2.569/7.831/7.831 | 0.126 | 0.070 | 7.657 | 1/1 | 1/1 | 2.569 | — |

## postgres: 1 registered peers, 1 active / regular_large

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 2/2 | 2/2 | 2.353/4.957/4.957 | 0.120 | 0.053 | 4.815 | 1/1 | 1/1 | 2.353 | — |
| 1 | row | 2/2 | 2/2 | 3.084/7.124/7.124 | 0.107 | 0.068 | 6.948 | 1/1 | 2/2 | 7.124 | — |
| 1 | cached_row | 2/2 | 2/2 | 2.643/2.709/2.709 | 0.084 | 0.080 | 2.590 | 1/1 | 1/1 | 2.643 | — |
| 2 | snapshot | 2/2 | 2/2 | 2.663/3.149/3.149 | 0.083 | 0.066 | 3.036 | 1/1 | 1/1 | 2.663 | — |
| 2 | row | 2/2 | 2/2 | 2.884/3.357/3.357 | 0.138 | 0.057 | 3.161 | 1/1 | 2/2 | 2.884 | — |
| 2 | cached_row | 2/2 | 2/2 | 3.029/3.701/3.701 | 0.108 | 0.076 | 3.528 | 1/1 | 1/1 | 3.029 | — |
| 3 | snapshot | 2/2 | 2/2 | 2.456/4.071/4.071 | 0.092 | 0.044 | 3.956 | 1/1 | 1/1 | 2.456 | — |
| 3 | row | 2/2 | 2/2 | 2.493/3.934/3.934 | 0.108 | 0.057 | 3.767 | 1/1 | 2/2 | 3.934 | — |
| 3 | cached_row | 2/2 | 2/2 | 2.749/4.896/4.896 | 0.114 | 0.112 | 4.736 | 1/1 | 1/1 | 2.749 | — |

## postgres: 1 registered peers, 1 active / burst_64

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 78.279/142.160/149.190 | 68.484 | 77.076 | 3.232 | 1/1 | 1/1 | 149.190 | 219.640 |
| 1 | row | 64/64 | 64/64 | 86.380/172.136/180.293 | 72.431 | 99.009 | 4.194 | 1/1 | 2/2 | 180.293 | 181.748 |
| 1 | cached_row | 64/64 | 64/64 | 84.860/159.171/166.396 | 75.921 | 83.021 | 4.703 | 1/1 | 1/1 | 166.396 | 196.928 |
| 2 | snapshot | 64/64 | 64/64 | 69.489/132.952/139.514 | 60.938 | 70.047 | 3.106 | 1/1 | 1/1 | 139.514 | 234.873 |
| 2 | row | 64/64 | 64/64 | 74.823/141.134/147.063 | 64.980 | 74.654 | 3.259 | 1/1 | 2/2 | 147.063 | 222.815 |
| 2 | cached_row | 64/64 | 64/64 | 75.137/140.436/146.002 | 66.136 | 73.647 | 3.408 | 1/1 | 1/1 | 146.002 | 224.436 |
| 3 | snapshot | 64/64 | 64/64 | 70.827/135.391/140.996 | 62.582 | 70.940 | 3.018 | 1/1 | 1/1 | 140.996 | 232.404 |
| 3 | row | 64/64 | 64/64 | 78.103/145.512/153.486 | 68.130 | 76.564 | 3.378 | 1/1 | 2/2 | 153.486 | 213.492 |
| 3 | cached_row | 64/64 | 64/64 | 81.284/150.378/156.167 | 72.166 | 78.855 | 3.431 | 1/1 | 1/1 | 156.167 | 209.827 |

## postgres: 1 registered peers, 1 active / burst_256

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 256/256 | 256/256 | 288.440/679.220/713.022 | 572.384 | 123.043 | 4.442 | 1/1 | 1/1 | 719.537 | 182.162 |
| 1 | row | 256/256 | 256/256 | 464.470/868.905/911.321 | 748.860 | 120.193 | 5.437 | 1/1 | 2/2 | 924.391 | 141.793 |
| 1 | cached_row | 256/256 | 256/256 | 299.085/567.030/590.183 | 489.474 | 77.409 | 3.273 | 1/1 | 1/1 | 594.399 | 220.512 |
| 2 | snapshot | 256/256 | 256/256 | 287.875/557.164/579.005 | 481.750 | 78.662 | 3.281 | 1/1 | 1/1 | 584.061 | 224.415 |
| 2 | row | 256/256 | 256/256 | 312.080/594.590/620.472 | 510.640 | 82.599 | 3.314 | 1/1 | 2/2 | 624.651 | 209.832 |
| 2 | cached_row | 256/256 | 256/256 | 309.553/606.769/629.275 | 512.822 | 91.137 | 4.078 | 1/1 | 1/1 | 634.187 | 206.677 |
| 3 | snapshot | 256/256 | 256/256 | 354.106/712.696/738.676 | 604.863 | 104.500 | 4.522 | 1/1 | 1/1 | 745.874 | 175.729 |
| 3 | row | 256/256 | 256/256 | 330.732/678.514/707.281 | 577.340 | 105.149 | 4.583 | 1/1 | 2/2 | 714.743 | 183.383 |
| 3 | cached_row | 256/256 | 256/256 | 357.184/697.140/740.086 | 589.039 | 106.284 | 4.634 | 1/1 | 1/1 | 744.033 | 176.164 |

## postgres: 1 registered peers, 1 active / burst_512

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 512/512 | 285/512 | 897.945/1750.965/1919.077 | 1624.063 | 133.955 | 7.252 | 1/1 | 1/1 | 1951.636 | 134.320 |
| 1 | row | 512/512 | 407/512 | 619.476/1199.357/1249.061 | 1117.365 | 84.910 | 3.462 | 1/1 | 2/2 | 1260.647 | 207.944 |
| 1 | cached_row | 512/512 | 420/512 | 624.846/1151.124/1195.403 | 1075.678 | 84.519 | 3.385 | 1/1 | 1/1 | 1206.037 | 217.360 |
| 2 | snapshot | 512/512 | 436/512 | 595.304/1118.312/1167.445 | 1041.093 | 81.903 | 3.251 | 1/1 | 1/1 | 1178.265 | 222.483 |
| 2 | row | 512/512 | 335/512 | 714.814/1487.268/1544.797 | 1380.183 | 120.108 | 5.418 | 1/1 | 2/2 | 1558.433 | 168.210 |
| 2 | cached_row | 512/512 | 423/512 | 609.075/1151.966/1201.837 | 1074.316 | 80.892 | 3.400 | 1/1 | 1/1 | 1212.989 | 216.114 |
| 3 | snapshot | 512/512 | 407/512 | 593.305/1244.144/1312.937 | 1153.035 | 105.736 | 4.484 | 1/1 | 1/1 | 1326.389 | 197.637 |
| 3 | row | 512/512 | 401/512 | 650.476/1222.619/1271.327 | 1141.193 | 95.121 | 3.566 | 1/1 | 2/2 | 1283.829 | 204.189 |
| 3 | cached_row | 512/512 | 423/512 | 572.885/1171.359/1224.435 | 1085.207 | 89.805 | 3.564 | 1/1 | 1/1 | 1236.887 | 211.939 |

## postgres: 100 registered peers, 32 active / small_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 4.412/5.673/5.827 | 0.124 | 0.069 | 5.530 | 1/1 | 1/1 | 5.371 | — |
| 1 | row | 64/64 | 64/64 | 3.408/5.406/8.991 | 0.108 | 0.068 | 5.278 | 1/1 | 2/2 | 3.392 | — |
| 1 | cached_row | 64/64 | 64/64 | 2.353/4.748/10.992 | 0.120 | 0.067 | 4.583 | 1/1 | 1/1 | 2.108 | — |
| 2 | snapshot | 64/64 | 64/64 | 4.431/5.903/8.679 | 0.117 | 0.055 | 5.747 | 1/1 | 1/1 | 4.105 | — |
| 2 | row | 64/64 | 64/64 | 2.393/5.212/5.819 | 0.130 | 0.063 | 5.059 | 1/1 | 2/2 | 4.287 | — |
| 2 | cached_row | 64/64 | 64/64 | 2.182/3.936/7.627 | 0.119 | 0.073 | 3.786 | 1/1 | 1/1 | 2.117 | — |
| 3 | snapshot | 64/64 | 64/64 | 5.514/7.496/10.867 | 0.111 | 0.062 | 7.336 | 1/1 | 1/1 | 5.222 | — |
| 3 | row | 64/64 | 64/64 | 3.395/5.455/6.962 | 0.118 | 0.066 | 5.297 | 1/1 | 2/2 | 3.439 | — |
| 3 | cached_row | 64/64 | 64/64 | 2.048/3.120/3.724 | 0.111 | 0.069 | 2.976 | 1/1 | 1/1 | 2.841 | — |

## postgres: 100 registered peers, 32 active / mixed_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 5.142/7.261/7.577 | 0.113 | 0.069 | 7.147 | 1/1 | 1/1 | 5.034 | — |
| 1 | row | 64/64 | 64/64 | 2.270/3.764/4.647 | 0.111 | 0.063 | 3.635 | 1/1 | 2/2 | 1.930 | — |
| 1 | cached_row | 64/64 | 64/64 | 2.070/3.527/8.471 | 0.120 | 0.080 | 3.421 | 1/1 | 1/1 | 2.107 | — |
| 2 | snapshot | 64/64 | 64/64 | 4.269/5.677/6.985 | 0.114 | 0.065 | 5.538 | 1/1 | 1/1 | 4.080 | — |
| 2 | row | 64/64 | 64/64 | 2.304/3.493/4.144 | 0.111 | 0.075 | 3.376 | 1/1 | 2/2 | 2.157 | — |
| 2 | cached_row | 64/64 | 64/64 | 2.370/3.960/4.711 | 0.110 | 0.066 | 3.805 | 1/1 | 1/1 | 2.050 | — |
| 3 | snapshot | 64/64 | 64/64 | 5.569/8.555/10.771 | 0.128 | 0.054 | 8.395 | 1/1 | 1/1 | 6.031 | — |
| 3 | row | 64/64 | 64/64 | 3.709/6.420/9.792 | 0.110 | 0.077 | 6.295 | 1/1 | 2/2 | 3.953 | — |
| 3 | cached_row | 64/64 | 64/64 | 3.579/5.008/10.282 | 0.111 | 0.067 | 4.870 | 1/1 | 1/1 | 4.404 | — |

## postgres: 100 registered peers, 32 active / small_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 640/640 | 640/640 | 214.188/438.708/459.778 | 0.105 | 435.216 | 4.772 | 1/1 | 1/1 | 464.738 | — |
| 1 | row | 640/640 | 640/640 | 3.307/8.212/13.643 | 0.105 | 0.054 | 8.103 | 6/6 | 2/2 | 3.750 | — |
| 1 | cached_row | 640/640 | 640/640 | 3.019/5.199/8.243 | 0.107 | 0.054 | 5.083 | 5/5 | 1/1 | 2.672 | — |
| 2 | snapshot | 640/640 | 515/640 | 636.007/1172.083/1223.104 | 0.105 | 1167.477 | 6.512 | 1/1 | 1/1 | 1237.349 | — |
| 2 | row | 640/640 | 640/640 | 3.600/7.725/11.641 | 0.105 | 0.053 | 7.595 | 6/6 | 2/2 | 2.719 | — |
| 2 | cached_row | 640/640 | 640/640 | 3.504/7.528/11.749 | 0.101 | 0.054 | 7.409 | 7/7 | 1/1 | 3.402 | — |
| 3 | snapshot | 640/640 | 572/640 | 626.068/1041.837/1075.664 | 0.105 | 1036.223 | 7.396 | 1/1 | 1/1 | 1082.283 | — |
| 3 | row | 640/640 | 640/640 | 3.624/8.381/11.121 | 0.107 | 0.055 | 8.263 | 5/5 | 2/2 | 3.100 | — |
| 3 | cached_row | 640/640 | 640/640 | 3.389/6.334/9.383 | 0.106 | 0.054 | 6.218 | 5/5 | 1/1 | 3.558 | — |

## postgres: 100 registered peers, 32 active / mixed_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 640/640 | 435/640 | 726.518/1374.959/1425.641 | 0.116 | 1368.355 | 7.468 | 1/1 | 1/1 | 1437.213 | — |
| 1 | row | 640/640 | 640/640 | 2.041/4.707/8.696 | 0.105 | 0.053 | 4.567 | 4/4 | 2/2 | 2.875 | — |
| 1 | cached_row | 640/640 | 640/640 | 1.779/3.550/6.959 | 0.106 | 0.054 | 3.456 | 4/4 | 1/1 | 1.479 | — |
| 2 | snapshot | 640/640 | 640/640 | 429.815/650.036/681.825 | 0.106 | 644.573 | 5.796 | 1/1 | 1/1 | 686.539 | — |
| 2 | row | 640/640 | 640/640 | 3.590/7.868/12.466 | 0.112 | 0.056 | 7.745 | 5/5 | 2/2 | 7.392 | — |
| 2 | cached_row | 640/640 | 640/640 | 3.421/8.902/14.077 | 0.109 | 0.054 | 8.770 | 6/6 | 1/1 | 2.686 | — |
| 3 | snapshot | 640/640 | 640/640 | 239.359/441.571/468.952 | 0.105 | 437.892 | 5.028 | 1/1 | 1/1 | 475.343 | — |
| 3 | row | 640/640 | 640/640 | 1.954/4.058/5.621 | 0.106 | 0.054 | 3.947 | 3/3 | 2/2 | 1.727 | — |
| 3 | cached_row | 640/640 | 640/640 | 1.792/3.910/5.672 | 0.108 | 0.055 | 3.777 | 3/3 | 1/1 | 1.582 | — |

## postgres: 100 registered peers, 32 active / small_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 6400/6400 | 263/6400 | 11771.820/23346.250/24372.685 | 22287.171 | 1274.096 | 5.520 | 1/1 | 1/1 | 24543.965 | — |
| 1 | row | 6400/6400 | 6400/6400 | 298.412/632.832/670.426 | 508.629 | 120.831 | 4.634 | 8/8 | 2/2 | 682.672 | — |
| 1 | cached_row | 6400/6400 | 6400/6400 | 378.483/671.035/692.516 | 570.231 | 127.187 | 5.485 | 8/8 | 1/1 | 699.133 | — |
| 2 | snapshot | 6400/6400 | 282/6400 | 11786.914/22360.619/23334.221 | 21382.026 | 1141.925 | 5.390 | 1/1 | 1/1 | 23488.071 | — |
| 2 | row | 6400/6400 | 6400/6400 | 300.358/598.908/616.461 | 496.241 | 116.062 | 4.489 | 8/8 | 2/2 | 620.450 | — |
| 2 | cached_row | 6400/6400 | 4195/6400 | 749.469/1219.560/1239.430 | 1106.052 | 152.433 | 6.251 | 8/8 | 1/1 | 1245.655 | — |
| 3 | snapshot | 6400/6400 | 274/6400 | 13184.723/25763.804/26486.457 | 24617.221 | 1356.598 | 6.058 | 1/1 | 1/1 | 26718.481 | — |
| 3 | row | 6400/6400 | 6400/6400 | 301.264/680.016/734.387 | 540.091 | 134.357 | 5.536 | 8/8 | 2/2 | 747.948 | — |
| 3 | cached_row | 6400/6400 | 5886/6400 | 361.029/1056.276/1129.278 | 896.239 | 160.239 | 6.137 | 8/8 | 1/1 | 1142.844 | — |

## postgres: 100 registered peers, 32 active / mixed_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 6400/6400 | 260/6400 | 12301.861/22910.298/23952.553 | 21907.173 | 1126.017 | 5.526 | 1/1 | 1/1 | 24045.136 | — |
| 1 | row | 6400/6400 | 6400/6400 | 279.220/607.714/645.362 | 493.543 | 121.482 | 4.618 | 8/8 | 2/2 | 651.242 | — |
| 1 | cached_row | 6400/6400 | 6130/6400 | 412.287/989.869/1037.735 | 853.262 | 142.846 | 6.189 | 8/8 | 1/1 | 1054.605 | — |
| 2 | snapshot | 6400/6400 | 268/6400 | 12496.282/23772.851/24804.697 | 22782.116 | 1277.164 | 5.951 | 1/1 | 1/1 | 24917.072 | — |
| 2 | row | 6400/6400 | 6400/6400 | 454.735/729.057/757.870 | 624.759 | 125.528 | 5.124 | 8/8 | 2/2 | 764.161 | — |
| 2 | cached_row | 6400/6400 | 6400/6400 | 441.261/841.231/863.076 | 736.382 | 151.332 | 5.980 | 8/8 | 1/1 | 868.062 | — |
| 3 | snapshot | 6400/6400 | 290/6400 | 11624.388/22701.464/23639.181 | 21700.563 | 1160.526 | 5.566 | 1/1 | 1/1 | 23798.945 | — |
| 3 | row | 6400/6400 | 3995/6400 | 921.421/1183.105/1205.089 | 1079.478 | 169.524 | 6.229 | 8/8 | 2/2 | 1208.601 | — |
| 3 | cached_row | 6400/6400 | 6400/6400 | 285.752/521.804/558.829 | 411.778 | 112.462 | 3.788 | 8/8 | 1/1 | 563.571 | — |

## postgres: 100 registered peers, 32 active / small_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 12800/12800 | 259/12800 | 25774.671/51219.003/53282.852 | 50040.217 | 1326.732 | 6.048 | 1/1 | 1/1 | 53781.995 | — |
| 1 | row | 12800/12800 | 1897/12800 | 3462.321/5250.111/5365.405 | 5144.484 | 194.842 | 6.536 | 8/8 | 2/2 | 5394.102 | — |
| 1 | cached_row | 12800/12800 | 3992/12800 | 1615.123/2962.403/3086.386 | 2861.152 | 110.541 | 3.866 | 8/8 | 1/1 | 3115.111 | — |
| 2 | snapshot | 12800/12800 | 235/12800 | 24098.665/46416.790/48341.523 | 45438.138 | 1141.761 | 5.366 | 1/1 | 1/1 | 48838.846 | — |
| 2 | row | 12800/12800 | 4184/12800 | 1832.714/3360.755/3486.783 | 3257.614 | 146.131 | 5.653 | 8/8 | 2/2 | 3515.692 | — |
| 2 | cached_row | 12800/12800 | 3971/12800 | 1624.112/3473.838/3664.201 | 3326.758 | 137.127 | 5.562 | 8/8 | 1/1 | 3713.596 | — |
| 3 | snapshot | 12800/12800 | 205/12800 | 27119.557/53161.344/55339.449 | 52074.000 | 1507.432 | 6.482 | 1/1 | 1/1 | 55747.390 | — |
| 3 | row | 12800/12800 | 3801/12800 | 1659.592/3269.940/3404.093 | 3161.885 | 129.630 | 5.294 | 8/8 | 2/2 | 3443.262 | — |
| 3 | cached_row | 12800/12800 | 3902/12800 | 1601.841/3904.379/4171.603 | 3711.519 | 178.713 | 6.072 | 8/8 | 1/1 | 4239.960 | — |

## postgres: 100 registered peers, 32 active / mixed_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 12800/12800 | 219/12800 | 25720.224/49273.834/51266.134 | 48270.435 | 1245.992 | 5.971 | 1/1 | 1/1 | 51833.706 | — |
| 1 | row | 12800/12800 | 3977/12800 | 1627.037/3650.028/3823.322 | 3505.375 | 138.064 | 6.012 | 8/8 | 2/2 | 3862.988 | — |
| 1 | cached_row | 12800/12800 | 3144/12800 | 1884.996/3429.204/3612.423 | 3309.732 | 148.835 | 5.516 | 8/8 | 1/1 | 3654.018 | — |
| 2 | snapshot | 12800/12800 | 265/12800 | 25997.475/49507.512/51648.133 | 48512.935 | 1286.079 | 5.987 | 1/1 | 1/1 | 52092.351 | — |
| 2 | row | 12800/12800 | 3747/12800 | 1724.210/3583.544/3801.993 | 3443.706 | 144.236 | 5.729 | 8/8 | 2/2 | 3843.291 | — |
| 2 | cached_row | 12800/12800 | 3031/12800 | 2096.168/3775.125/3921.344 | 3653.495 | 143.192 | 5.962 | 8/8 | 1/1 | 3954.881 | — |
| 3 | snapshot | 12800/12800 | 244/12800 | 25440.378/47863.336/49879.057 | 46852.966 | 1163.482 | 5.637 | 1/1 | 1/1 | 50276.712 | — |
| 3 | row | 12800/12800 | 4032/12800 | 1579.958/3213.644/3349.930 | 3109.100 | 122.295 | 4.866 | 8/8 | 2/2 | 3382.850 | — |
| 3 | cached_row | 12800/12800 | 3880/12800 | 1884.386/4039.434/4167.335 | 3925.207 | 157.625 | 6.095 | 8/8 | 1/1 | 4196.980 | — |

## postgres: 100 registered peers, 32 active / heterogeneous_mixed

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 4976/4976 | 288/4976 | 8920.400/16989.581/17671.170 | 16009.311 | 1118.716 | 5.490 | 1/1 | 1/1 | 17844.389 | — |
| 1 | row | 4976/4976 | 4976/4976 | 49.720/59.761/62.144 | 0.087 | 56.539 | 4.354 | 8/8 | 2/2 | 51.022 | — |
| 1 | cached_row | 4976/4976 | 4976/4976 | 64.841/555.746/560.689 | 444.050 | 222.237 | 8.563 | 8/8 | 1/1 | 563.622 | — |
| 2 | snapshot | 4976/4976 | 283/4976 | 8990.598/18893.376/19725.307 | 17607.075 | 1341.275 | 6.095 | 1/1 | 1/1 | 19854.120 | — |
| 2 | row | 4976/4976 | 4976/4976 | 343.578/687.694/720.719 | 545.298 | 148.997 | 6.844 | 8/8 | 2/2 | 727.900 | — |
| 2 | cached_row | 4976/4976 | 4976/4976 | 85.120/135.558/151.503 | 3.007 | 123.993 | 5.788 | 8/8 | 1/1 | 155.311 | — |
| 3 | snapshot | 4976/4976 | 225/4976 | 9168.645/17616.647/18401.359 | 16637.715 | 1233.627 | 5.902 | 1/1 | 1/1 | 18426.616 | — |
| 3 | row | 4976/4976 | 4976/4976 | 86.448/99.614/103.162 | 0.084 | 96.298 | 4.970 | 8/8 | 2/2 | 85.079 | — |
| 3 | cached_row | 4976/4976 | 4976/4976 | 166.038/553.917/617.488 | 394.647 | 173.628 | 6.712 | 8/8 | 1/1 | 626.772 | — |

## postgres: 100 registered peers, 32 active / regular_large

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 4.527/8.809/12.464 | 0.107 | 0.060 | 8.669 | 1/1 | 1/1 | 4.112 | — |
| 1 | row | 64/64 | 64/64 | 2.913/7.403/10.470 | 0.128 | 0.066 | 7.272 | 1/1 | 2/2 | 1.896 | — |
| 1 | cached_row | 64/64 | 64/64 | 2.508/5.571/14.013 | 0.111 | 0.063 | 5.453 | 1/1 | 1/1 | 2.020 | — |
| 2 | snapshot | 64/64 | 64/64 | 4.221/6.175/7.849 | 0.114 | 0.058 | 6.062 | 1/1 | 1/1 | 4.011 | — |
| 2 | row | 64/64 | 64/64 | 2.486/4.387/5.775 | 0.113 | 0.080 | 4.227 | 1/1 | 2/2 | 3.290 | — |
| 2 | cached_row | 64/64 | 64/64 | 2.294/4.062/5.037 | 0.112 | 0.077 | 3.939 | 1/1 | 1/1 | 5.037 | — |
| 3 | snapshot | 64/64 | 64/64 | 4.337/5.743/10.934 | 0.107 | 0.058 | 5.609 | 1/1 | 1/1 | 4.644 | — |
| 3 | row | 64/64 | 64/64 | 2.899/4.089/4.645 | 0.182 | 0.106 | 3.948 | 1/1 | 2/2 | 2.290 | — |
| 3 | cached_row | 64/64 | 64/64 | 2.365/3.898/5.505 | 0.114 | 0.061 | 3.763 | 1/1 | 1/1 | 2.258 | — |

## postgres: 100 registered peers, 32 active / burst_64

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 138.171/272.498/289.775 | 121.469 | 147.855 | 5.983 | 1/1 | 1/1 | 289.775 | 113.081 |
| 1 | row | 64/64 | 64/64 | 16.084/26.300/29.012 | 9.820 | 14.705 | 4.537 | 8/8 | 2/2 | 29.012 | 1129.475 |
| 1 | cached_row | 64/64 | 64/64 | 15.467/26.557/27.871 | 10.381 | 14.043 | 4.191 | 8/8 | 1/1 | 27.871 | 1175.705 |
| 2 | snapshot | 64/64 | 64/64 | 142.203/271.445/284.090 | 121.604 | 145.388 | 5.325 | 1/1 | 1/1 | 284.090 | 115.344 |
| 2 | row | 64/64 | 64/64 | 14.164/26.423/26.444 | 11.538 | 13.993 | 5.107 | 8/8 | 2/2 | 26.444 | 1239.159 |
| 2 | cached_row | 64/64 | 64/64 | 17.786/33.243/33.250 | 14.138 | 18.660 | 6.566 | 8/8 | 1/1 | 33.250 | 985.500 |
| 3 | snapshot | 64/64 | 64/64 | 144.810/280.427/293.430 | 126.609 | 151.749 | 6.293 | 1/1 | 1/1 | 293.430 | 111.672 |
| 3 | row | 64/64 | 64/64 | 17.999/31.335/33.217 | 13.756 | 17.819 | 5.749 | 8/8 | 2/2 | 33.217 | 986.483 |
| 3 | cached_row | 64/64 | 64/64 | 16.084/30.434/30.523 | 12.470 | 15.868 | 4.754 | 8/8 | 1/1 | 30.523 | 1073.555 |

## postgres: 100 registered peers, 32 active / burst_256

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 256/256 | 185/256 | 647.630/1325.859/1380.898 | 1176.298 | 267.389 | 9.690 | 1/1 | 1/1 | 1392.409 | 94.133 |
| 1 | row | 256/256 | 256/256 | 53.536/103.770/108.888 | 85.369 | 15.339 | 4.729 | 8/8 | 2/2 | 110.168 | 1189.751 |
| 1 | cached_row | 256/256 | 256/256 | 75.547/153.721/162.260 | 122.816 | 29.122 | 8.773 | 8/8 | 1/1 | 166.250 | 788.405 |
| 2 | snapshot | 256/256 | 203/256 | 618.889/1210.013/1272.757 | 1054.031 | 188.508 | 7.098 | 1/1 | 1/1 | 1285.114 | 101.993 |
| 2 | row | 256/256 | 256/256 | 59.067/113.815/119.959 | 90.734 | 19.237 | 6.288 | 8/8 | 2/2 | 124.302 | 1054.463 |
| 2 | cached_row | 256/256 | 256/256 | 55.912/111.661/122.819 | 92.738 | 18.357 | 5.560 | 8/8 | 1/1 | 125.587 | 1043.675 |
| 3 | snapshot | 256/256 | 217/256 | 576.466/1119.440/1165.664 | 970.304 | 162.716 | 6.034 | 1/1 | 1/1 | 1173.720 | 111.672 |
| 3 | row | 256/256 | 256/256 | 58.622/105.585/109.343 | 89.181 | 15.568 | 4.919 | 8/8 | 2/2 | 112.505 | 1165.030 |
| 3 | cached_row | 256/256 | 256/256 | 53.400/99.047/103.860 | 82.907 | 13.222 | 4.114 | 8/8 | 1/1 | 103.874 | 1261.841 |

## postgres: 100 registered peers, 32 active / burst_512

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 512/512 | 172/512 | 1431.198/2664.147/2773.064 | 2498.566 | 222.086 | 8.321 | 1/1 | 1/1 | 2799.407 | 93.643 |
| 1 | row | 512/512 | 512/512 | 111.256/211.331/217.730 | 192.788 | 15.690 | 4.808 | 8/8 | 2/2 | 223.296 | 1173.975 |
| 1 | cached_row | 512/512 | 512/512 | 115.263/206.892/214.527 | 191.857 | 16.634 | 5.477 | 8/8 | 1/1 | 218.354 | 1200.547 |
| 2 | snapshot | 512/512 | 199/512 | 1277.582/2672.165/2808.409 | 2453.788 | 218.147 | 8.560 | 1/1 | 1/1 | 2838.603 | 92.350 |
| 2 | row | 512/512 | 512/512 | 113.963/256.410/274.469 | 230.201 | 26.293 | 6.805 | 8/8 | 2/2 | 282.590 | 927.649 |
| 2 | cached_row | 512/512 | 512/512 | 121.857/244.410/268.075 | 221.955 | 23.678 | 6.653 | 8/8 | 1/1 | 278.673 | 940.687 |
| 3 | snapshot | 512/512 | 189/512 | 1333.446/2697.575/2836.490 | 2482.222 | 218.423 | 8.745 | 1/1 | 1/1 | 2860.018 | 91.658 |
| 3 | row | 512/512 | 512/512 | 165.558/308.312/317.470 | 284.075 | 26.435 | 7.320 | 8/8 | 2/2 | 320.092 | 818.965 |
| 3 | cached_row | 512/512 | 512/512 | 136.429/276.083/299.136 | 259.101 | 27.876 | 7.310 | 8/8 | 1/1 | 307.332 | 852.966 |

## sqlite: 1 registered peers, 1 active / small_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 2/2 | 2/2 | 7.716/18.806/18.806 | 0.160 | 0.062 | 18.642 | 1/1 | 0/4 | 7.716 | — |
| 1 | row | 2/2 | 2/2 | 8.052/15.575/15.575 | 0.106 | 0.048 | 15.433 | 1/1 | 0/5 | 8.052 | — |
| 1 | cached_row | 2/2 | 2/2 | 7.780/15.961/15.961 | 0.103 | 0.041 | 15.817 | 1/1 | 0/4 | 7.780 | — |
| 2 | snapshot | 2/2 | 2/2 | 11.332/12.636/12.636 | 0.101 | 0.069 | 12.464 | 1/1 | 0/4 | 12.636 | — |
| 2 | row | 2/2 | 2/2 | 8.904/11.758/11.758 | 0.127 | 0.113 | 11.559 | 1/1 | 0/5 | 8.904 | — |
| 2 | cached_row | 2/2 | 2/2 | 5.496/12.000/12.000 | 0.104 | 0.052 | 11.842 | 1/1 | 0/4 | 5.496 | — |
| 3 | snapshot | 2/2 | 2/2 | 7.803/13.091/13.091 | 0.092 | 0.057 | 12.945 | 1/1 | 0/4 | 7.803 | — |
| 3 | row | 2/2 | 2/2 | 7.905/14.156/14.156 | 0.135 | 0.042 | 14.007 | 1/1 | 0/5 | 7.905 | — |
| 3 | cached_row | 2/2 | 2/2 | 8.819/14.320/14.320 | 0.099 | 0.052 | 14.178 | 1/1 | 0/4 | 8.819 | — |

## sqlite: 1 registered peers, 1 active / mixed_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 2/2 | 2/2 | 7.291/20.692/20.692 | 0.114 | 0.048 | 20.578 | 1/1 | 0/4 | 7.291 | — |
| 1 | row | 2/2 | 2/2 | 8.012/22.788/22.788 | 0.141 | 0.080 | 22.601 | 1/1 | 0/5 | 8.012 | — |
| 1 | cached_row | 2/2 | 2/2 | 8.137/16.185/16.185 | 0.112 | 0.070 | 16.044 | 1/1 | 0/4 | 8.137 | — |
| 2 | snapshot | 2/2 | 2/2 | 7.314/11.904/11.904 | 0.087 | 0.075 | 11.758 | 1/1 | 0/4 | 7.314 | — |
| 2 | row | 2/2 | 2/2 | 5.644/12.549/12.549 | 0.093 | 0.045 | 12.427 | 1/1 | 0/5 | 5.644 | — |
| 2 | cached_row | 2/2 | 2/2 | 5.694/14.548/14.548 | 0.101 | 0.071 | 14.385 | 1/1 | 0/4 | 5.694 | — |
| 3 | snapshot | 2/2 | 2/2 | 5.748/17.210/17.210 | 0.117 | 0.045 | 17.055 | 1/1 | 0/4 | 5.748 | — |
| 3 | row | 2/2 | 2/2 | 11.655/14.191/14.191 | 0.101 | 0.082 | 14.006 | 1/1 | 0/5 | 14.191 | — |
| 3 | cached_row | 2/2 | 2/2 | 5.728/12.825/12.825 | 0.112 | 0.046 | 12.687 | 1/1 | 0/4 | 5.728 | — |

## sqlite: 1 registered peers, 1 active / small_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 20/20 | 20/20 | 6.854/9.504/13.032 | 0.115 | 0.075 | 9.361 | 1/1 | 0/4 | 7.448 | — |
| 1 | row | 20/20 | 20/20 | 6.696/8.212/13.990 | 0.130 | 0.064 | 8.051 | 1/1 | 0/5 | 6.922 | — |
| 1 | cached_row | 20/20 | 20/20 | 8.497/16.338/17.133 | 0.150 | 0.071 | 16.142 | 1/1 | 0/4 | 16.338 | — |
| 2 | snapshot | 20/20 | 20/20 | 6.570/8.561/11.642 | 0.114 | 0.064 | 8.431 | 1/1 | 0/4 | 5.682 | — |
| 2 | row | 20/20 | 20/20 | 6.328/9.696/12.988 | 0.095 | 0.061 | 9.575 | 1/1 | 0/5 | 6.884 | — |
| 2 | cached_row | 20/20 | 20/20 | 6.695/9.166/12.076 | 0.107 | 0.070 | 9.021 | 1/1 | 0/4 | 6.868 | — |
| 3 | snapshot | 20/20 | 20/20 | 7.813/9.428/16.395 | 0.162 | 0.070 | 9.241 | 1/1 | 0/4 | 7.470 | — |
| 3 | row | 20/20 | 20/20 | 6.815/8.445/11.499 | 0.121 | 0.061 | 8.299 | 1/1 | 0/5 | 7.062 | — |
| 3 | cached_row | 20/20 | 20/20 | 7.158/11.293/12.221 | 0.123 | 0.066 | 11.153 | 1/1 | 0/4 | 9.652 | — |

## sqlite: 1 registered peers, 1 active / mixed_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 20/20 | 20/20 | 6.532/8.361/11.788 | 0.113 | 0.051 | 8.223 | 1/1 | 0/4 | 6.532 | — |
| 1 | row | 20/20 | 20/20 | 6.786/11.221/12.624 | 0.137 | 0.066 | 11.045 | 1/1 | 0/5 | 6.786 | — |
| 1 | cached_row | 20/20 | 20/20 | 5.946/14.143/14.539 | 0.111 | 0.067 | 13.984 | 1/1 | 0/4 | 5.842 | — |
| 2 | snapshot | 20/20 | 20/20 | 6.601/8.386/11.422 | 0.116 | 0.055 | 8.230 | 1/1 | 0/4 | 6.612 | — |
| 2 | row | 20/20 | 20/20 | 6.855/8.186/13.439 | 0.169 | 0.062 | 8.037 | 1/1 | 0/5 | 6.589 | — |
| 2 | cached_row | 20/20 | 20/20 | 6.529/9.198/11.733 | 0.116 | 0.072 | 9.027 | 1/1 | 0/4 | 7.627 | — |
| 3 | snapshot | 20/20 | 20/20 | 6.627/6.954/15.041 | 0.108 | 0.060 | 6.812 | 1/1 | 0/4 | 6.818 | — |
| 3 | row | 20/20 | 20/20 | 7.823/12.431/12.806 | 0.107 | 0.060 | 12.293 | 1/1 | 0/5 | 8.293 | — |
| 3 | cached_row | 20/20 | 20/20 | 6.548/7.451/10.969 | 0.105 | 0.059 | 7.303 | 1/1 | 0/4 | 6.658 | — |

## sqlite: 1 registered peers, 1 active / small_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 200/200 | 200/200 | 6.336/10.791/15.861 | 0.106 | 0.709 | 9.344 | 1/1 | 0/4 | 5.778 | — |
| 1 | row | 200/200 | 200/200 | 6.160/6.976/8.989 | 0.100 | 0.057 | 6.670 | 1/1 | 0/5 | 6.606 | — |
| 1 | cached_row | 200/200 | 200/200 | 6.308/8.656/10.389 | 0.106 | 0.057 | 8.509 | 1/1 | 0/4 | 6.349 | — |
| 2 | snapshot | 200/200 | 200/200 | 6.201/7.879/9.282 | 0.107 | 0.057 | 7.763 | 1/1 | 0/4 | 5.255 | — |
| 2 | row | 200/200 | 200/200 | 6.150/7.101/8.128 | 0.100 | 0.053 | 6.945 | 1/1 | 0/5 | 5.304 | — |
| 2 | cached_row | 200/200 | 200/200 | 6.148/7.170/10.422 | 0.106 | 0.059 | 7.028 | 1/1 | 0/4 | 6.195 | — |
| 3 | snapshot | 200/200 | 200/200 | 6.341/8.895/13.122 | 0.110 | 0.057 | 8.699 | 1/1 | 0/4 | 6.509 | — |
| 3 | row | 200/200 | 200/200 | 6.580/9.865/12.779 | 0.111 | 0.058 | 9.387 | 1/1 | 0/5 | 8.125 | — |
| 3 | cached_row | 200/200 | 200/200 | 6.155/8.590/12.575 | 0.107 | 0.059 | 8.132 | 1/1 | 0/4 | 5.705 | — |

## sqlite: 1 registered peers, 1 active / mixed_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 200/200 | 200/200 | 6.107/8.224/11.221 | 0.101 | 0.059 | 8.015 | 1/1 | 0/4 | 6.475 | — |
| 1 | row | 200/200 | 200/200 | 6.170/7.452/11.737 | 0.102 | 0.048 | 6.937 | 1/1 | 0/5 | 6.170 | — |
| 1 | cached_row | 200/200 | 200/200 | 6.371/8.499/11.497 | 0.107 | 0.073 | 8.380 | 1/1 | 0/4 | 8.284 | — |
| 2 | snapshot | 200/200 | 200/200 | 6.156/7.239/9.905 | 0.108 | 0.055 | 7.070 | 1/1 | 0/4 | 6.391 | — |
| 2 | row | 200/200 | 200/200 | 6.244/8.466/11.168 | 0.106 | 0.063 | 8.064 | 1/1 | 0/5 | 6.341 | — |
| 2 | cached_row | 200/200 | 200/200 | 6.060/6.955/10.342 | 0.105 | 0.057 | 6.764 | 1/1 | 0/4 | 5.549 | — |
| 3 | snapshot | 200/200 | 200/200 | 6.163/7.732/9.893 | 0.105 | 0.057 | 7.558 | 1/1 | 0/4 | 7.675 | — |
| 3 | row | 200/200 | 200/200 | 6.141/7.608/11.361 | 0.103 | 0.058 | 7.490 | 1/1 | 0/5 | 5.209 | — |
| 3 | cached_row | 200/200 | 200/200 | 6.107/6.625/9.089 | 0.103 | 0.056 | 6.446 | 1/1 | 0/4 | 6.436 | — |

## sqlite: 1 registered peers, 1 active / small_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 400/400 | 400/400 | 164.569/399.828/429.365 | 0.096 | 392.314 | 8.245 | 1/1 | 0/4 | 436.861 | — |
| 1 | row | 400/400 | 400/400 | 248.858/400.177/430.141 | 0.098 | 393.518 | 7.928 | 1/1 | 0/5 | 441.028 | — |
| 1 | cached_row | 400/400 | 400/400 | 186.688/339.959/351.926 | 0.098 | 334.558 | 7.191 | 1/1 | 0/4 | 354.645 | — |
| 2 | snapshot | 400/400 | 400/400 | 119.302/269.455/281.484 | 0.107 | 264.375 | 7.072 | 1/1 | 0/4 | 286.716 | — |
| 2 | row | 400/400 | 400/400 | 252.156/542.088/564.728 | 0.100 | 534.548 | 8.464 | 1/1 | 0/5 | 571.261 | — |
| 2 | cached_row | 400/400 | 400/400 | 162.096/304.752/315.269 | 0.109 | 299.662 | 6.771 | 1/1 | 0/4 | 318.647 | — |
| 3 | snapshot | 400/400 | 400/400 | 361.915/516.159/530.175 | 0.103 | 511.025 | 9.424 | 1/1 | 0/4 | 532.369 | — |
| 3 | row | 400/400 | 400/400 | 146.098/551.497/611.016 | 0.101 | 544.381 | 10.476 | 1/1 | 0/5 | 631.889 | — |
| 3 | cached_row | 400/400 | 400/400 | 258.405/664.740/692.132 | 0.107 | 657.180 | 9.151 | 1/1 | 0/4 | 694.498 | — |

## sqlite: 1 registered peers, 1 active / mixed_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 400/400 | 400/400 | 219.153/676.379/731.315 | 0.102 | 667.804 | 9.778 | 1/1 | 0/4 | 741.922 | — |
| 1 | row | 400/400 | 400/400 | 155.601/329.850/342.068 | 0.104 | 323.737 | 7.216 | 1/1 | 0/5 | 345.247 | — |
| 1 | cached_row | 400/400 | 400/400 | 141.653/315.744/334.973 | 0.096 | 309.611 | 7.341 | 1/1 | 0/4 | 369.855 | — |
| 2 | snapshot | 400/400 | 400/400 | 208.959/418.142/431.830 | 0.091 | 411.418 | 8.421 | 1/1 | 0/4 | 434.025 | — |
| 2 | row | 400/400 | 400/400 | 286.831/600.732/634.422 | 0.101 | 595.644 | 8.699 | 1/1 | 0/5 | 636.939 | — |
| 2 | cached_row | 400/400 | 400/400 | 182.287/388.878/397.309 | 0.107 | 379.738 | 7.932 | 1/1 | 0/4 | 399.400 | — |
| 3 | snapshot | 400/400 | 336/400 | 646.054/1116.971/1199.550 | 0.103 | 1108.409 | 12.172 | 1/1 | 0/4 | 1219.917 | — |
| 3 | row | 400/400 | 400/400 | 555.687/790.985/801.728 | 0.105 | 784.939 | 9.300 | 1/1 | 0/5 | 804.503 | — |
| 3 | cached_row | 400/400 | 400/400 | 189.284/330.777/344.296 | 0.103 | 324.644 | 7.087 | 1/1 | 0/4 | 346.859 | — |

## sqlite: 1 registered peers, 1 active / heterogeneous_mixed

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 2/2 | 2/2 | 6.985/11.433/11.433 | 0.117 | 0.059 | 11.281 | 1/1 | 0/4 | 6.985 | — |
| 1 | row | 2/2 | 2/2 | 6.707/14.919/14.919 | 0.131 | 0.053 | 14.781 | 1/1 | 0/5 | 6.707 | — |
| 1 | cached_row | 2/2 | 2/2 | 6.558/11.716/11.716 | 0.096 | 0.061 | 11.564 | 1/1 | 0/4 | 6.558 | — |
| 2 | snapshot | 2/2 | 2/2 | 5.701/11.433/11.433 | 0.084 | 0.050 | 11.298 | 1/1 | 0/4 | 5.701 | — |
| 2 | row | 2/2 | 2/2 | 6.767/11.794/11.794 | 0.115 | 0.054 | 11.631 | 1/1 | 0/5 | 6.767 | — |
| 2 | cached_row | 2/2 | 2/2 | 6.185/12.067/12.067 | 0.137 | 0.071 | 11.870 | 1/1 | 0/4 | 6.185 | — |
| 3 | snapshot | 2/2 | 2/2 | 6.052/14.658/14.658 | 0.105 | 0.102 | 14.483 | 1/1 | 0/4 | 6.052 | — |
| 3 | row | 2/2 | 2/2 | 6.960/13.990/13.990 | 0.115 | 0.077 | 13.825 | 1/1 | 0/5 | 6.960 | — |
| 3 | cached_row | 2/2 | 2/2 | 7.842/11.458/11.458 | 0.121 | 0.074 | 11.299 | 1/1 | 0/4 | 7.842 | — |

## sqlite: 1 registered peers, 1 active / regular_large

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 2/2 | 2/2 | 6.021/14.357/14.357 | 0.088 | 0.051 | 14.247 | 1/1 | 0/4 | 6.021 | — |
| 1 | row | 2/2 | 2/2 | 6.793/13.949/13.949 | 0.127 | 0.062 | 13.778 | 1/1 | 0/5 | 6.793 | — |
| 1 | cached_row | 2/2 | 2/2 | 8.694/21.222/21.222 | 0.103 | 0.037 | 21.091 | 1/1 | 0/4 | 8.694 | — |
| 2 | snapshot | 2/2 | 2/2 | 6.665/15.973/15.973 | 0.110 | 0.419 | 15.830 | 1/1 | 0/4 | 6.665 | — |
| 2 | row | 2/2 | 2/2 | 11.946/13.140/13.140 | 0.127 | 0.053 | 13.001 | 1/1 | 0/5 | 13.140 | — |
| 2 | cached_row | 2/2 | 2/2 | 6.831/11.518/11.518 | 0.105 | 0.080 | 11.371 | 1/1 | 0/4 | 6.831 | — |
| 3 | snapshot | 2/2 | 2/2 | 6.665/13.274/13.274 | 0.105 | 0.052 | 13.137 | 1/1 | 0/4 | 6.665 | — |
| 3 | row | 2/2 | 2/2 | 6.837/11.841/11.841 | 0.118 | 0.042 | 11.715 | 1/1 | 0/5 | 6.837 | — |
| 3 | cached_row | 2/2 | 2/2 | 5.591/13.781/13.781 | 0.123 | 0.067 | 13.590 | 1/1 | 0/4 | 5.591 | — |

## sqlite: 1 registered peers, 1 active / burst_64

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 252.357/480.602/503.369 | 224.195 | 257.653 | 10.663 | 1/1 | 0/4 | 503.369 | 65.097 |
| 1 | row | 64/64 | 64/64 | 225.814/416.750/436.387 | 196.366 | 223.996 | 9.810 | 1/1 | 0/5 | 436.387 | 75.089 |
| 1 | cached_row | 64/64 | 64/64 | 219.969/412.917/435.038 | 190.532 | 216.161 | 8.084 | 1/1 | 0/4 | 435.038 | 75.322 |
| 2 | snapshot | 64/64 | 64/64 | 237.851/459.487/477.821 | 208.820 | 242.471 | 9.797 | 1/1 | 0/4 | 477.821 | 68.578 |
| 2 | row | 64/64 | 64/64 | 234.816/423.486/442.044 | 207.962 | 229.614 | 8.398 | 1/1 | 0/5 | 442.044 | 74.128 |
| 2 | cached_row | 64/64 | 64/64 | 247.082/467.702/489.412 | 218.043 | 245.090 | 10.457 | 1/1 | 0/4 | 489.412 | 66.954 |
| 3 | snapshot | 64/64 | 64/64 | 224.972/412.901/432.736 | 198.118 | 219.228 | 9.005 | 1/1 | 0/4 | 432.736 | 75.723 |
| 3 | row | 64/64 | 64/64 | 218.294/403.363/422.270 | 191.934 | 211.815 | 7.949 | 1/1 | 0/5 | 422.270 | 77.600 |
| 3 | cached_row | 64/64 | 64/64 | 252.168/453.887/477.733 | 225.309 | 244.896 | 10.819 | 1/1 | 0/4 | 477.733 | 68.591 |

## sqlite: 1 registered peers, 1 active / burst_256

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 256/256 | 151/256 | 849.379/1633.629/1697.626 | 1397.152 | 229.265 | 8.042 | 1/1 | 0/4 | 1710.184 | 76.642 |
| 1 | row | 256/256 | 153/256 | 837.220/1577.046/1661.870 | 1359.466 | 212.280 | 7.897 | 1/1 | 0/5 | 1675.924 | 78.209 |
| 1 | cached_row | 256/256 | 152/256 | 840.909/1644.858/1722.884 | 1409.397 | 236.699 | 8.551 | 1/1 | 0/4 | 1735.955 | 75.504 |
| 2 | snapshot | 256/256 | 156/256 | 818.010/1584.113/1647.625 | 1362.130 | 221.891 | 7.836 | 1/1 | 0/4 | 1660.698 | 78.926 |
| 2 | row | 256/256 | 150/256 | 850.368/1642.331/1704.682 | 1414.081 | 222.460 | 8.605 | 1/1 | 0/5 | 1717.245 | 76.327 |
| 2 | cached_row | 256/256 | 144/256 | 870.927/1720.833/1785.607 | 1496.594 | 262.332 | 9.054 | 1/1 | 0/4 | 1798.233 | 72.889 |
| 3 | snapshot | 256/256 | 147/256 | 876.861/1649.043/1717.037 | 1427.369 | 236.246 | 8.471 | 1/1 | 0/4 | 1731.480 | 75.699 |
| 3 | row | 256/256 | 141/256 | 897.507/1751.537/1825.601 | 1505.593 | 240.502 | 8.994 | 1/1 | 0/5 | 1839.877 | 71.240 |
| 3 | cached_row | 256/256 | 137/256 | 940.286/1684.552/1749.186 | 1478.608 | 269.925 | 9.266 | 1/1 | 0/4 | 1761.900 | 74.392 |

## sqlite: 1 registered peers, 1 active / burst_512

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 512/512 | 143/512 | 1752.419/3236.087/3362.089 | 3022.515 | 226.587 | 7.901 | 1/1 | 0/4 | 3394.656 | 77.223 |
| 1 | row | 512/512 | 156/512 | 1637.174/3231.123/3363.449 | 2994.238 | 242.033 | 8.517 | 1/1 | 0/5 | 3407.179 | 76.939 |
| 1 | cached_row | 512/512 | 152/512 | 1650.402/3216.715/3362.203 | 2987.939 | 234.180 | 8.445 | 1/1 | 0/4 | 3392.770 | 77.265 |
| 2 | snapshot | 512/512 | 146/512 | 1731.480/3268.948/3392.871 | 3047.964 | 224.773 | 8.326 | 1/1 | 0/4 | 3424.311 | 76.554 |
| 2 | row | 512/512 | 155/512 | 1668.260/3256.924/3404.513 | 2981.502 | 257.063 | 8.557 | 1/1 | 0/5 | 3440.542 | 76.193 |
| 2 | cached_row | 512/512 | 138/512 | 1798.056/3427.168/3566.012 | 3212.096 | 247.961 | 9.105 | 1/1 | 0/4 | 3608.442 | 72.647 |
| 3 | snapshot | 512/512 | 129/512 | 1913.011/3459.119/3594.295 | 3231.316 | 255.703 | 9.192 | 1/1 | 0/4 | 3627.407 | 72.268 |
| 3 | row | 512/512 | 143/512 | 1698.974/3210.083/3340.018 | 2996.377 | 233.626 | 8.588 | 1/1 | 0/5 | 3371.797 | 77.746 |
| 3 | cached_row | 512/512 | 143/512 | 1741.049/3418.698/3562.343 | 3177.542 | 245.348 | 9.374 | 1/1 | 0/4 | 3603.487 | 72.747 |

## sqlite: 100 registered peers, 32 active / small_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 6.662/9.454/12.735 | 0.115 | 0.060 | 9.332 | 1/1 | 0/4 | 6.795 | — |
| 1 | row | 64/64 | 64/64 | 6.360/8.406/14.516 | 0.112 | 0.062 | 8.291 | 1/1 | 0/5 | 7.943 | — |
| 1 | cached_row | 64/64 | 64/64 | 6.569/8.639/11.357 | 0.115 | 0.076 | 8.461 | 1/1 | 0/4 | 7.407 | — |
| 2 | snapshot | 64/64 | 64/64 | 8.300/10.813/22.271 | 0.143 | 0.072 | 10.671 | 1/1 | 0/4 | 8.698 | — |
| 2 | row | 64/64 | 64/64 | 7.862/9.724/16.585 | 0.125 | 0.077 | 9.559 | 1/1 | 0/5 | 5.779 | — |
| 2 | cached_row | 64/64 | 64/64 | 8.266/12.042/18.379 | 0.120 | 0.064 | 11.906 | 1/1 | 0/4 | 9.024 | — |
| 3 | snapshot | 64/64 | 64/64 | 6.758/12.040/13.641 | 0.107 | 0.058 | 11.929 | 1/1 | 0/4 | 5.966 | — |
| 3 | row | 64/64 | 64/64 | 6.514/8.895/12.765 | 0.111 | 0.070 | 8.788 | 1/1 | 0/5 | 5.574 | — |
| 3 | cached_row | 64/64 | 64/64 | 6.514/8.843/12.566 | 0.115 | 0.067 | 8.688 | 1/1 | 0/4 | 6.355 | — |

## sqlite: 100 registered peers, 32 active / mixed_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 6.817/10.017/23.757 | 0.116 | 0.059 | 9.886 | 1/1 | 0/4 | 5.760 | — |
| 1 | row | 64/64 | 64/64 | 7.566/13.065/14.870 | 0.111 | 0.072 | 12.916 | 1/1 | 0/5 | 8.715 | — |
| 1 | cached_row | 64/64 | 64/64 | 6.542/8.495/11.484 | 0.112 | 0.089 | 8.324 | 1/1 | 0/4 | 5.654 | — |
| 2 | snapshot | 64/64 | 64/64 | 6.870/10.623/13.653 | 0.110 | 0.065 | 10.471 | 1/1 | 0/4 | 5.763 | — |
| 2 | row | 64/64 | 64/64 | 6.337/7.381/11.834 | 0.126 | 0.069 | 7.201 | 1/1 | 0/5 | 5.723 | — |
| 2 | cached_row | 64/64 | 64/64 | 7.584/10.393/12.934 | 0.111 | 0.089 | 10.240 | 1/1 | 0/4 | 6.527 | — |
| 3 | snapshot | 64/64 | 64/64 | 6.977/9.399/14.511 | 0.119 | 0.058 | 9.275 | 1/1 | 0/4 | 5.852 | — |
| 3 | row | 64/64 | 64/64 | 6.352/7.349/11.970 | 0.118 | 0.074 | 7.189 | 1/1 | 0/5 | 7.358 | — |
| 3 | cached_row | 64/64 | 64/64 | 6.365/7.590/13.689 | 0.109 | 0.062 | 7.470 | 1/1 | 0/4 | 7.574 | — |

## sqlite: 100 registered peers, 32 active / small_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 640/640 | 262/640 | 1216.974/2311.370/2412.290 | 625.602 | 1721.250 | 11.761 | 1/1 | 0/4 | 2351.874 | — |
| 1 | row | 640/640 | 335/640 | 900.622/2757.219/3128.760 | 1874.864 | 2732.150 | 23.726 | 8/8 | 0/5 | 2351.392 | — |
| 1 | cached_row | 640/640 | 274/640 | 1239.271/2826.504/3130.936 | 1715.897 | 2720.032 | 14.115 | 8/8 | 0/4 | 2603.375 | — |
| 2 | snapshot | 640/640 | 258/640 | 1196.056/2241.860/2340.243 | 564.643 | 1675.201 | 11.298 | 1/1 | 0/4 | 2286.791 | — |
| 2 | row | 640/640 | 358/640 | 745.239/2548.741/3021.863 | 1494.217 | 2523.665 | 39.506 | 8/8 | 0/5 | 2201.769 | — |
| 2 | cached_row | 640/640 | 367/640 | 756.081/2509.979/2821.999 | 1598.166 | 2484.873 | 14.554 | 8/8 | 0/4 | 2053.053 | — |
| 3 | snapshot | 640/640 | 270/640 | 1162.531/2144.850/2399.115 | 495.888 | 1652.490 | 10.074 | 1/1 | 0/4 | 2230.241 | — |
| 3 | row | 640/640 | 243/640 | 1574.417/4327.804/4734.232 | 3502.840 | 4152.348 | 15.571 | 8/8 | 0/5 | 3682.264 | — |
| 3 | cached_row | 640/640 | 240/640 | 1616.542/3893.150/4339.777 | 2829.014 | 3717.828 | 15.439 | 8/8 | 0/4 | 3536.667 | — |

## sqlite: 100 registered peers, 32 active / mixed_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 640/640 | 269/640 | 1159.755/2193.352/2331.143 | 521.921 | 1671.607 | 11.185 | 1/1 | 0/4 | 2254.779 | — |
| 1 | row | 640/640 | 351/640 | 894.371/2431.615/2918.841 | 1100.706 | 2073.196 | 24.337 | 8/8 | 0/5 | 2031.101 | — |
| 1 | cached_row | 640/640 | 348/640 | 835.977/2682.964/3024.382 | 1857.995 | 2657.856 | 25.913 | 8/8 | 0/4 | 2124.690 | — |
| 2 | snapshot | 640/640 | 306/640 | 1048.358/2036.195/2215.565 | 374.140 | 1656.488 | 9.313 | 1/1 | 0/4 | 2125.492 | — |
| 2 | row | 640/640 | 353/640 | 797.543/3279.443/3749.188 | 2454.475 | 2314.341 | 24.368 | 8/8 | 0/5 | 2433.237 | — |
| 2 | cached_row | 640/640 | 373/640 | 720.312/2690.513/2922.551 | 1807.757 | 2607.665 | 15.376 | 8/8 | 0/4 | 2317.962 | — |
| 3 | snapshot | 640/640 | 300/640 | 1066.478/2026.087/2197.312 | 375.512 | 1643.416 | 11.200 | 1/1 | 0/4 | 2110.902 | — |
| 3 | row | 640/640 | 329/640 | 940.823/3478.200/3841.301 | 2647.475 | 3453.179 | 20.268 | 8/8 | 0/5 | 2921.959 | — |
| 3 | cached_row | 640/640 | 345/640 | 902.049/2783.063/3126.882 | 1919.255 | 2757.989 | 24.520 | 8/8 | 0/4 | 2201.227 | — |

## sqlite: 100 registered peers, 32 active / small_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 6400/6400 | 142/6400 | 21670.829/41302.623/43050.870 | 39431.602 | 2047.704 | 11.704 | 1/1 | 0/4 | 43419.896 | — |
| 1 | row | 6400/6400 | 232/6400 | 19116.868/37209.862/38092.703 | 35975.129 | 7805.740 | 10.103 | 8/8 | 0/5 | 38421.852 | — |
| 1 | cached_row | 6400/6400 | 293/6400 | 19577.856/37196.258/38041.453 | 37000.752 | 7460.087 | 8.617 | 8/8 | 0/4 | 38266.771 | — |
| 2 | snapshot | 6400/6400 | 160/6400 | 20093.036/38597.905/40127.445 | 36743.842 | 1849.556 | 11.208 | 1/1 | 0/4 | 40503.029 | — |
| 2 | row | 6400/6400 | 181/6400 | 19898.438/37549.883/38594.665 | 37335.648 | 8052.460 | 9.049 | 8/8 | 0/5 | 38795.929 | — |
| 2 | cached_row | 6400/6400 | 230/6400 | 19077.846/37887.215/39012.446 | 37680.965 | 8347.557 | 13.188 | 8/8 | 0/4 | 39248.549 | — |
| 3 | snapshot | 6400/6400 | 124/6400 | 23083.428/41644.913/43312.902 | 39972.280 | 2218.641 | 11.558 | 1/1 | 0/4 | 43577.205 | — |
| 3 | row | 6400/6400 | 205/6400 | 20124.358/39476.136/41030.767 | 38653.681 | 7447.598 | 10.084 | 8/8 | 0/5 | 41290.334 | — |
| 3 | cached_row | 6400/6400 | 307/6400 | 19479.794/37251.511/38704.579 | 36964.737 | 8136.253 | 9.126 | 8/8 | 0/4 | 38908.027 | — |

## sqlite: 100 registered peers, 32 active / mixed_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 6400/6400 | 164/6400 | 20502.732/39142.034/41231.231 | 37300.472 | 1857.666 | 11.397 | 1/1 | 0/4 | 41670.199 | — |
| 1 | row | 6400/6400 | 143/6400 | 21561.623/38483.667/39638.795 | 38182.244 | 10423.649 | 11.028 | 8/8 | 0/5 | 39850.838 | — |
| 1 | cached_row | 6400/6400 | 194/6400 | 18894.563/36358.339/37204.066 | 36168.709 | 4875.314 | 8.528 | 8/8 | 0/4 | 37410.003 | — |
| 2 | snapshot | 6400/6400 | 160/6400 | 21819.383/41000.038/42735.085 | 39077.278 | 2166.287 | 11.537 | 1/1 | 0/4 | 43062.069 | — |
| 2 | row | 6400/6400 | 170/6400 | 21583.083/37327.872/38660.371 | 37020.693 | 7822.679 | 10.137 | 8/8 | 0/5 | 38858.350 | — |
| 2 | cached_row | 6400/6400 | 239/6400 | 18890.594/40375.284/42078.830 | 39951.464 | 10966.880 | 13.030 | 8/8 | 0/4 | 42279.847 | — |
| 3 | snapshot | 6400/6400 | 159/6400 | 20936.146/40671.012/42169.061 | 39028.319 | 2222.550 | 11.667 | 1/1 | 0/4 | 42560.534 | — |
| 3 | row | 6400/6400 | 246/6400 | 19197.700/37323.744/38304.610 | 37107.515 | 8822.563 | 9.433 | 8/8 | 0/5 | 38500.902 | — |
| 3 | cached_row | 6400/6400 | 297/6400 | 18313.881/34995.909/36510.876 | 34703.761 | 9632.746 | 8.130 | 8/8 | 0/4 | 36705.576 | — |

## sqlite: 100 registered peers, 32 active / small_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 12800/12800 | 156/12800 | 42888.883/80970.185/84290.251 | 79252.633 | 1912.422 | 11.397 | 1/1 | 0/4 | 85197.990 | — |
| 1 | row | 12800/12800 | 210/12800 | 39609.189/76694.978/80358.337 | 76340.653 | 8870.777 | 11.333 | 8/8 | 0/5 | 81099.537 | — |
| 1 | cached_row | 12800/12800 | 213/12800 | 39796.208/78635.196/81888.973 | 78263.009 | 8625.851 | 12.015 | 8/8 | 0/4 | 82560.572 | — |
| 2 | snapshot | 12800/12800 | 145/12800 | 42770.595/80901.585/85291.835 | 79037.224 | 2072.637 | 11.519 | 1/1 | 0/4 | 86258.503 | — |
| 2 | row | 12800/12800 | 187/12800 | 43634.439/79659.786/83614.103 | 79437.580 | 8785.545 | 12.117 | 8/8 | 0/5 | 84538.680 | — |
| 2 | cached_row | 12800/12800 | 140/12800 | 41599.079/76601.743/79138.799 | 76397.651 | 913.668 | 8.956 | 8/8 | 0/4 | 79801.038 | — |
| 3 | snapshot | 12800/12800 | 151/12800 | 42076.822/82833.791/86136.374 | 81135.226 | 2185.734 | 11.516 | 1/1 | 0/4 | 86900.575 | — |
| 3 | row | 12800/12800 | 211/12800 | 42779.597/77649.527/80240.047 | 77261.631 | 7796.077 | 24.923 | 8/8 | 0/5 | 80876.424 | — |
| 3 | cached_row | 12800/12800 | 186/12800 | 39103.598/75885.929/78800.296 | 75339.472 | 8552.923 | 9.073 | 8/8 | 0/4 | 79565.260 | — |

## sqlite: 100 registered peers, 32 active / mixed_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 12800/12800 | 146/12800 | 42292.445/80525.243/84416.939 | 78848.813 | 2002.965 | 11.412 | 1/1 | 0/4 | 85474.354 | — |
| 1 | row | 12800/12800 | 205/12800 | 42848.525/78707.731/81281.157 | 78372.970 | 7949.151 | 10.947 | 8/8 | 0/5 | 82000.971 | — |
| 1 | cached_row | 12800/12800 | 136/12800 | 44623.625/78271.061/81542.110 | 77772.784 | 10006.642 | 10.149 | 8/8 | 0/4 | 82104.380 | — |
| 2 | snapshot | 12800/12800 | 143/12800 | 42095.417/82721.714/86148.242 | 81006.820 | 2223.163 | 11.552 | 1/1 | 0/4 | 86904.744 | — |
| 2 | row | 12800/12800 | 199/12800 | 37725.719/73899.535/76252.662 | 73708.131 | 9523.805 | 9.329 | 8/8 | 0/5 | 76842.616 | — |
| 2 | cached_row | 12800/12800 | 213/12800 | 39603.578/77143.254/80416.627 | 76321.926 | 9645.871 | 9.565 | 8/8 | 0/4 | 81089.814 | — |
| 3 | snapshot | 12800/12800 | 147/12800 | 43742.319/83272.410/86660.143 | 81536.733 | 2051.897 | 11.522 | 1/1 | 0/4 | 87431.238 | — |
| 3 | row | 12800/12800 | 154/12800 | 40944.034/78517.162/82711.869 | 77982.271 | 8519.032 | 12.441 | 8/8 | 0/5 | 83549.216 | — |
| 3 | cached_row | 12800/12800 | 164/12800 | 43492.751/78215.096/82142.930 | 77869.848 | 9092.523 | 11.592 | 8/8 | 0/4 | 83003.735 | — |

## sqlite: 100 registered peers, 32 active / heterogeneous_mixed

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 4976/4976 | 169/4976 | 16074.579/31111.464/32441.392 | 29418.885 | 2044.251 | 11.575 | 1/1 | 0/4 | 32668.381 | — |
| 1 | row | 4976/4976 | 289/4976 | 15481.820/29990.857/30502.712 | 28737.509 | 8876.943 | 10.439 | 8/8 | 0/5 | 30679.006 | — |
| 1 | cached_row | 4976/4976 | 154/4976 | 14265.223/27628.626/28156.309 | 27445.275 | 5364.563 | 8.350 | 8/8 | 0/4 | 28267.260 | — |
| 2 | snapshot | 4976/4976 | 149/4976 | 17345.188/32117.806/33431.576 | 30187.846 | 2166.521 | 11.751 | 1/1 | 0/4 | 33592.741 | — |
| 2 | row | 4976/4976 | 241/4976 | 13786.753/28152.639/28732.134 | 26929.703 | 6157.572 | 8.960 | 8/8 | 0/5 | 28910.357 | — |
| 2 | cached_row | 4976/4976 | 211/4976 | 14791.326/29215.643/29845.816 | 29027.242 | 7613.135 | 9.195 | 8/8 | 0/4 | 29991.552 | — |
| 3 | snapshot | 4976/4976 | 126/4976 | 17463.220/31403.147/32646.407 | 29679.240 | 2355.754 | 11.672 | 1/1 | 0/4 | 32925.402 | — |
| 3 | row | 4976/4976 | 180/4976 | 15341.141/28865.099/29426.590 | 27703.832 | 6533.897 | 8.559 | 8/8 | 0/5 | 29543.979 | — |
| 3 | cached_row | 4976/4976 | 150/4976 | 17097.152/31905.774/32620.574 | 30860.938 | 10122.119 | 13.238 | 8/8 | 0/4 | 32744.174 | — |

## sqlite: 100 registered peers, 32 active / regular_large

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 6.573/10.911/12.473 | 0.111 | 0.066 | 10.764 | 1/1 | 0/4 | 5.851 | — |
| 1 | row | 64/64 | 64/64 | 6.560/9.151/16.553 | 0.125 | 0.067 | 8.999 | 1/1 | 0/5 | 5.582 | — |
| 1 | cached_row | 64/64 | 64/64 | 7.781/11.035/15.433 | 0.120 | 0.070 | 10.899 | 1/1 | 0/4 | 5.357 | — |
| 2 | snapshot | 64/64 | 64/64 | 6.812/11.661/12.735 | 0.109 | 0.052 | 11.545 | 1/1 | 0/4 | 6.945 | — |
| 2 | row | 64/64 | 64/64 | 6.434/8.044/12.483 | 0.110 | 0.062 | 7.881 | 1/1 | 0/5 | 6.523 | — |
| 2 | cached_row | 64/64 | 64/64 | 6.500/8.170/12.809 | 0.113 | 0.065 | 8.024 | 1/1 | 0/4 | 6.085 | — |
| 3 | snapshot | 64/64 | 64/64 | 6.964/12.291/15.406 | 0.112 | 0.067 | 12.142 | 1/1 | 0/4 | 8.564 | — |
| 3 | row | 64/64 | 64/64 | 6.737/9.497/17.973 | 0.138 | 0.068 | 9.347 | 1/1 | 0/5 | 6.937 | — |
| 3 | cached_row | 64/64 | 64/64 | 6.586/8.298/12.962 | 0.113 | 0.067 | 8.117 | 1/1 | 0/4 | 6.705 | — |

## sqlite: 100 registered peers, 32 active / burst_64

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 234.838/437.250/456.640 | 200.988 | 235.870 | 11.976 | 1/1 | 0/4 | 456.640 | 71.759 |
| 1 | row | 64/64 | 64/64 | 239.255/669.415/692.993 | 550.950 | 637.413 | 337.120 | 8/8 | 0/5 | 692.993 | 47.285 |
| 1 | cached_row | 64/64 | 64/64 | 386.784/761.780/779.642 | 649.508 | 737.098 | 435.607 | 8/8 | 0/4 | 779.642 | 42.030 |
| 2 | snapshot | 64/64 | 64/64 | 240.916/459.927/479.102 | 213.964 | 246.105 | 10.274 | 1/1 | 0/4 | 479.102 | 68.395 |
| 2 | row | 64/64 | 64/64 | 279.422/663.115/681.204 | 549.863 | 636.325 | 337.914 | 8/8 | 0/5 | 681.204 | 48.103 |
| 2 | cached_row | 64/64 | 64/64 | 229.752/565.949/591.776 | 456.772 | 535.776 | 235.662 | 8/8 | 0/4 | 591.776 | 55.372 |
| 3 | snapshot | 64/64 | 64/64 | 226.192/432.492/453.767 | 196.827 | 231.305 | 9.233 | 1/1 | 0/4 | 453.767 | 72.213 |
| 3 | row | 64/64 | 64/64 | 438.008/863.722/881.557 | 751.835 | 837.189 | 537.003 | 8/8 | 0/5 | 881.557 | 37.171 |
| 3 | cached_row | 64/64 | 64/64 | 287.111/664.410/681.996 | 550.337 | 637.376 | 335.718 | 8/8 | 0/4 | 681.996 | 48.047 |

## sqlite: 100 registered peers, 32 active / burst_256

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 256/256 | 124/256 | 1037.841/1877.572/1960.949 | 1660.255 | 267.734 | 12.425 | 1/1 | 0/4 | 1973.743 | 66.408 |
| 1 | row | 256/256 | 147/256 | 866.686/1758.467/1825.570 | 1724.909 | 856.473 | 136.031 | 8/8 | 0/5 | 1837.889 | 71.317 |
| 1 | cached_row | 256/256 | 116/256 | 1087.639/2107.153/2174.762 | 2074.669 | 1159.291 | 84.389 | 8/8 | 0/4 | 2187.826 | 59.910 |
| 2 | snapshot | 256/256 | 122/256 | 1044.157/2054.563/2138.239 | 1768.273 | 290.437 | 13.879 | 1/1 | 0/4 | 2153.778 | 60.857 |
| 2 | row | 256/256 | 136/256 | 948.800/1966.548/2034.977 | 1929.736 | 663.600 | 111.319 | 8/8 | 0/5 | 2047.339 | 64.021 |
| 2 | cached_row | 256/256 | 128/256 | 939.143/2061.447/2122.689 | 2029.555 | 1055.803 | 10.223 | 8/8 | 0/4 | 2134.705 | 61.401 |
| 3 | snapshot | 256/256 | 133/256 | 965.027/1872.173/1940.427 | 1621.843 | 265.291 | 12.105 | 1/1 | 0/4 | 1952.852 | 67.118 |
| 3 | row | 256/256 | 147/256 | 872.600/1655.461/1720.808 | 1624.699 | 989.080 | 40.968 | 8/8 | 0/5 | 1732.990 | 75.633 |
| 3 | cached_row | 256/256 | 139/256 | 865.706/1759.727/1821.841 | 1726.612 | 955.559 | 10.461 | 8/8 | 0/4 | 1834.481 | 71.449 |

## sqlite: 100 registered peers, 32 active / burst_512

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 512/512 | 139/512 | 1838.476/3587.498/3728.708 | 3340.297 | 253.066 | 11.998 | 1/1 | 0/4 | 3764.446 | 69.637 |
| 1 | row | 512/512 | 139/512 | 1764.106/3396.965/3525.965 | 3347.645 | 457.139 | 9.124 | 8/8 | 0/5 | 3581.076 | 73.203 |
| 1 | cached_row | 512/512 | 138/512 | 1791.138/3493.899/3627.601 | 3462.013 | 1284.906 | 25.656 | 8/8 | 0/4 | 3658.067 | 71.662 |
| 2 | snapshot | 512/512 | 119/512 | 2380.807/4495.525/4674.581 | 4185.144 | 358.574 | 14.972 | 1/1 | 0/4 | 4724.738 | 55.483 |
| 2 | row | 512/512 | 134/512 | 1880.146/3600.111/3748.722 | 3565.010 | 648.576 | 10.342 | 8/8 | 0/5 | 3782.981 | 69.296 |
| 2 | cached_row | 512/512 | 144/512 | 1721.787/3279.788/3461.145 | 3118.078 | 1255.273 | 39.139 | 8/8 | 0/4 | 3496.494 | 74.973 |
| 3 | snapshot | 512/512 | 140/512 | 1875.273/3821.016/3987.589 | 3552.758 | 294.175 | 12.038 | 1/1 | 0/4 | 4028.208 | 65.077 |
| 3 | row | 512/512 | 138/512 | 1846.173/3754.462/3930.167 | 3678.102 | 950.877 | 11.018 | 8/8 | 0/5 | 3973.686 | 65.970 |
| 3 | cached_row | 512/512 | 143/512 | 1745.031/3325.686/3458.194 | 3290.459 | 754.145 | 40.365 | 8/8 | 0/4 | 3488.796 | 75.139 |

## postgres: 1000 registered peers, 32 active / small_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 21.996/24.121/24.596 | 0.134 | 0.055 | 24.010 | 1/1 | 1/1 | 21.651 | — |
| 1 | row | 64/64 | 64/64 | 2.354/3.617/4.046 | 0.114 | 0.084 | 3.460 | 1/1 | 2/2 | 2.206 | — |
| 1 | cached_row | 64/64 | 64/64 | 2.341/4.170/6.834 | 0.108 | 0.064 | 4.039 | 1/1 | 1/1 | 3.423 | — |
| 2 | snapshot | 64/64 | 64/64 | 25.396/30.492/48.161 | 0.109 | 0.057 | 30.369 | 1/1 | 1/1 | 48.161 | — |
| 2 | row | 64/64 | 64/64 | 5.482/10.604/16.611 | 0.109 | 0.074 | 10.474 | 1/1 | 2/2 | 3.547 | — |
| 2 | cached_row | 64/64 | 64/64 | 4.767/8.281/10.987 | 0.124 | 0.062 | 8.139 | 1/1 | 1/1 | 4.446 | — |
| 3 | snapshot | 64/64 | 64/64 | 24.623/28.806/31.899 | 0.114 | 0.059 | 28.657 | 1/1 | 1/1 | 25.566 | — |
| 3 | row | 64/64 | 64/64 | 5.576/10.322/22.871 | 0.125 | 0.087 | 10.195 | 1/1 | 2/2 | 7.240 | — |
| 3 | cached_row | 64/64 | 64/64 | 4.790/9.088/13.555 | 0.125 | 0.064 | 8.931 | 1/1 | 1/1 | 3.939 | — |

## postgres: 1000 registered peers, 32 active / mixed_period_1000ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 23.111/26.008/28.440 | 0.110 | 0.061 | 25.843 | 1/1 | 1/1 | 22.620 | — |
| 1 | row | 64/64 | 64/64 | 3.597/6.783/12.633 | 0.108 | 0.068 | 6.653 | 1/1 | 2/2 | 3.367 | — |
| 1 | cached_row | 64/64 | 64/64 | 3.498/5.432/8.188 | 0.120 | 0.070 | 5.295 | 1/1 | 1/1 | 3.631 | — |
| 2 | snapshot | 64/64 | 64/64 | 28.531/36.984/44.639 | 0.108 | 5.643 | 32.644 | 1/1 | 1/1 | 29.798 | — |
| 2 | row | 64/64 | 64/64 | 6.296/16.138/24.158 | 0.109 | 0.062 | 16.015 | 1/1 | 2/2 | 9.330 | — |
| 2 | cached_row | 64/64 | 64/64 | 6.318/13.323/23.335 | 0.107 | 0.078 | 13.184 | 1/1 | 1/1 | 6.434 | — |
| 3 | snapshot | 64/64 | 64/64 | 25.473/31.163/37.724 | 0.111 | 0.079 | 30.851 | 1/1 | 1/1 | 24.383 | — |
| 3 | row | 64/64 | 64/64 | 5.230/9.111/14.792 | 0.108 | 0.065 | 8.986 | 1/1 | 2/2 | 7.860 | — |
| 3 | cached_row | 64/64 | 64/64 | 4.699/7.944/11.402 | 0.118 | 0.070 | 7.819 | 1/1 | 1/1 | 4.549 | — |

## postgres: 1000 registered peers, 32 active / small_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 640/640 | 51/640 | 6202.463/12207.151/12639.701 | 6325.773 | 5952.560 | 25.820 | 1/1 | 1/1 | 12703.107 | — |
| 1 | row | 640/640 | 640/640 | 1.850/3.531/4.621 | 0.105 | 0.052 | 3.404 | 2/2 | 2/2 | 1.763 | — |
| 1 | cached_row | 640/640 | 640/640 | 1.850/4.769/6.761 | 0.100 | 0.049 | 4.655 | 3/3 | 1/1 | 1.659 | — |
| 2 | snapshot | 640/640 | 39/640 | 7519.136/14202.429/14764.870 | 7489.655 | 6801.020 | 30.856 | 1/1 | 1/1 | 14809.801 | — |
| 2 | row | 640/640 | 640/640 | 6.124/11.821/17.542 | 0.107 | 0.055 | 11.713 | 8/8 | 2/2 | 5.535 | — |
| 2 | cached_row | 640/640 | 640/640 | 7.047/14.383/18.026 | 0.105 | 0.050 | 14.271 | 7/7 | 1/1 | 5.279 | — |
| 3 | snapshot | 640/640 | 42/640 | 7416.530/13900.549/14514.283 | 7354.840 | 6802.529 | 32.014 | 1/1 | 1/1 | 14638.370 | — |
| 3 | row | 640/640 | 640/640 | 6.304/10.889/14.205 | 0.102 | 0.050 | 10.784 | 6/6 | 2/2 | 7.773 | — |
| 3 | cached_row | 640/640 | 640/640 | 7.587/13.387/20.109 | 0.103 | 0.052 | 13.276 | 8/8 | 1/1 | 8.756 | — |

## postgres: 1000 registered peers, 32 active / mixed_period_100ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 640/640 | 50/640 | 6325.804/12104.644/12670.685 | 6223.006 | 5888.963 | 25.567 | 1/1 | 1/1 | 12688.434 | — |
| 1 | row | 640/640 | 640/640 | 1.875/3.343/5.371 | 0.104 | 0.053 | 3.224 | 3/3 | 2/2 | 1.630 | — |
| 1 | cached_row | 640/640 | 640/640 | 3.059/7.632/12.466 | 0.107 | 0.056 | 7.503 | 5/5 | 1/1 | 3.095 | — |
| 2 | snapshot | 640/640 | 41/640 | 7252.276/13917.693/14477.102 | 7414.960 | 6620.957 | 31.347 | 1/1 | 1/1 | 14517.079 | — |
| 2 | row | 640/640 | 640/640 | 7.166/12.663/19.848 | 0.106 | 0.053 | 12.536 | 8/8 | 2/2 | 6.593 | — |
| 2 | cached_row | 640/640 | 640/640 | 6.959/12.159/18.228 | 0.105 | 0.053 | 12.061 | 8/8 | 1/1 | 5.990 | — |
| 3 | snapshot | 640/640 | 42/640 | 7318.400/13728.011/14240.069 | 7426.550 | 6657.046 | 30.722 | 1/1 | 1/1 | 14224.924 | — |
| 3 | row | 640/640 | 640/640 | 4.820/9.037/16.349 | 0.107 | 0.053 | 8.777 | 8/8 | 2/2 | 5.644 | — |
| 3 | cached_row | 640/640 | 640/640 | 5.730/11.348/15.232 | 0.107 | 0.054 | 11.252 | 6/6 | 1/1 | 6.059 | — |

## postgres: 1000 registered peers, 32 active / small_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 6400/6400 | 45/6400 | 72368.956/136971.110/142835.271 | 131232.211 | 6226.053 | 25.248 | 1/1 | 1/1 | 144086.280 | — |
| 1 | row | 6400/6400 | 2585/6400 | 1216.625/2359.538/2447.760 | 2160.161 | 213.814 | 8.508 | 8/8 | 2/2 | 2469.699 | — |
| 1 | cached_row | 6400/6400 | 6400/6400 | 457.597/880.903/900.859 | 776.891 | 153.006 | 5.947 | 8/8 | 1/1 | 905.394 | — |
| 2 | snapshot | 6400/6400 | 39/6400 | 83710.168/158080.884/164476.467 | 151398.837 | 7238.728 | 31.976 | 1/1 | 1/1 | 165948.956 | — |
| 2 | row | 6400/6400 | 1337/6400 | 2447.757/4442.207/4571.880 | 4218.455 | 303.809 | 13.252 | 8/8 | 2/2 | 4598.526 | — |
| 2 | cached_row | 6400/6400 | 1169/6400 | 2317.086/4772.400/5001.559 | 4460.919 | 328.335 | 13.392 | 8/8 | 1/1 | 5052.925 | — |
| 3 | snapshot | 6400/6400 | 41/6400 | 82836.798/157257.144/163601.461 | 149997.708 | 7432.230 | 31.733 | 1/1 | 1/1 | 165150.451 | — |
| 3 | row | 6400/6400 | 1943/6400 | 1730.318/3368.701/3505.714 | 3154.027 | 251.679 | 9.191 | 8/8 | 2/2 | 3535.355 | — |
| 3 | cached_row | 6400/6400 | 1608/6400 | 1960.295/3648.990/3789.552 | 3408.271 | 268.030 | 10.133 | 8/8 | 1/1 | 3821.266 | — |

## postgres: 1000 registered peers, 32 active / mixed_period_10ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 6400/6400 | 44/6400 | 71672.584/137156.000/142829.888 | 131175.638 | 6094.823 | 25.580 | 1/1 | 1/1 | 144091.266 | — |
| 1 | row | 6400/6400 | 5838/6400 | 666.643/1019.868/1046.666 | 915.549 | 177.044 | 6.808 | 8/8 | 2/2 | 1055.417 | — |
| 1 | cached_row | 6400/6400 | 6400/6400 | 296.549/682.908/736.975 | 563.632 | 135.436 | 5.533 | 8/8 | 1/1 | 748.713 | — |
| 2 | snapshot | 6400/6400 | 40/6400 | 81579.811/157184.263/163642.345 | 150590.664 | 7274.146 | 31.682 | 1/1 | 1/1 | 165230.478 | — |
| 2 | row | 6400/6400 | 1539/6400 | 2026.395/3727.142/3853.115 | 3516.445 | 267.922 | 10.855 | 8/8 | 2/2 | 3883.308 | — |
| 2 | cached_row | 6400/6400 | 1793/6400 | 1876.034/3530.773/3702.755 | 3284.765 | 254.036 | 10.873 | 8/8 | 1/1 | 3735.066 | — |
| 3 | snapshot | 6400/6400 | 39/6400 | 81996.216/155765.685/162245.637 | 149355.357 | 7219.333 | 31.634 | 1/1 | 1/1 | 163735.342 | — |
| 3 | row | 6400/6400 | 1676/6400 | 1919.214/3782.286/3964.769 | 3513.145 | 283.932 | 10.197 | 8/8 | 2/2 | 4008.047 | — |
| 3 | cached_row | 6400/6400 | 1458/6400 | 2162.701/4393.388/4571.041 | 4103.843 | 334.893 | 14.468 | 8/8 | 1/1 | 4606.523 | — |

## postgres: 1000 registered peers, 32 active / small_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 12800/12800 | 43/12800 | 150333.606/302858.271/315787.113 | 296041.978 | 7403.786 | 30.813 | 1/1 | 1/1 | 319083.057 | — |
| 1 | row | 12800/12800 | 1248/12800 | 5829.590/9810.012/10303.406 | 9617.828 | 345.820 | 13.690 | 8/8 | 2/2 | 10569.424 | — |
| 1 | cached_row | 12800/12800 | 969/12800 | 5814.409/10761.016/11132.946 | 10526.038 | 332.938 | 12.469 | 8/8 | 1/1 | 11222.443 | — |
| 2 | snapshot | 12800/12800 | 38/12800 | 163304.385/315011.377/328857.252 | 308416.550 | 7294.794 | 32.094 | 1/1 | 1/1 | 332247.947 | — |
| 2 | row | 12800/12800 | 1408/12800 | 4509.340/8828.893/9273.010 | 8580.984 | 262.542 | 9.996 | 8/8 | 2/2 | 9397.150 | — |
| 2 | cached_row | 12800/12800 | 1189/12800 | 5224.618/9281.871/9528.176 | 9162.544 | 288.761 | 10.804 | 8/8 | 1/1 | 9594.248 | — |
| 3 | snapshot | 12800/12800 | 39/12800 | 165214.944/313940.561/328148.281 | 307295.941 | 7252.204 | 31.844 | 1/1 | 1/1 | 331191.151 | — |
| 3 | row | 12800/12800 | 1265/12800 | 5482.842/10213.980/10679.323 | 9942.899 | 316.667 | 12.784 | 8/8 | 2/2 | 10788.556 | — |
| 3 | cached_row | 12800/12800 | 1229/12800 | 5827.982/10387.632/10773.685 | 10133.681 | 322.455 | 12.011 | 8/8 | 1/1 | 10867.605 | — |

## postgres: 1000 registered peers, 32 active / mixed_period_5ms

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 12800/12800 | 41/12800 | 166056.687/315998.568/328988.707 | 309073.353 | 7174.088 | 32.272 | 1/1 | 1/1 | 332164.893 | — |
| 1 | row | 12800/12800 | 1336/12800 | 6368.418/11510.083/11941.230 | 11255.325 | 351.156 | 13.744 | 8/8 | 2/2 | 12056.871 | — |
| 1 | cached_row | 12800/12800 | 1304/12800 | 6336.610/12396.624/12727.432 | 12193.618 | 378.058 | 14.728 | 8/8 | 1/1 | 12812.175 | — |
| 2 | snapshot | 12800/12800 | 40/12800 | 167938.057/319205.669/332182.097 | 312576.748 | 7368.338 | 32.831 | 1/1 | 1/1 | 335430.554 | — |
| 2 | row | 12800/12800 | 1217/12800 | 5579.154/10446.761/10899.547 | 10194.088 | 319.599 | 12.309 | 8/8 | 2/2 | 11008.627 | — |
| 2 | cached_row | 12800/12800 | 1313/12800 | 4800.992/9767.607/10148.182 | 9539.108 | 299.472 | 11.601 | 8/8 | 1/1 | 10243.071 | — |
| 3 | snapshot | 12800/12800 | 39/12800 | 172385.084/324854.537/338067.096 | 318159.166 | 7464.661 | 33.873 | 1/1 | 1/1 | 341280.954 | — |
| 3 | row | 12800/12800 | 2153/12800 | 4710.079/9732.860/10263.884 | 9475.423 | 331.496 | 13.081 | 8/8 | 2/2 | 10403.884 | — |
| 3 | cached_row | 12800/12800 | 1024/12800 | 5840.701/11085.919/11554.180 | 10790.884 | 310.720 | 13.276 | 8/8 | 1/1 | 11668.057 | — |

## postgres: 1000 registered peers, 32 active / heterogeneous_mixed

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 4976/4976 | 39/4976 | 64330.953/120195.756/125104.640 | 113194.811 | 7088.996 | 31.270 | 1/1 | 1/1 | 126298.114 | — |
| 1 | row | 4976/4976 | 2399/4976 | 1033.997/2238.166/2344.615 | 1980.203 | 305.257 | 9.510 | 8/8 | 2/2 | 2371.302 | — |
| 1 | cached_row | 4976/4976 | 2031/4976 | 1227.605/2238.587/2324.768 | 2015.330 | 256.390 | 9.659 | 8/8 | 1/1 | 2341.374 | — |
| 2 | snapshot | 4976/4976 | 42/4976 | 62465.514/120866.559/125641.078 | 114009.960 | 7317.731 | 32.604 | 1/1 | 1/1 | 126745.999 | — |
| 2 | row | 4976/4976 | 1478/4976 | 1590.776/2967.351/3080.635 | 2724.850 | 301.410 | 13.206 | 8/8 | 2/2 | 3121.083 | — |
| 2 | cached_row | 4976/4976 | 1748/4976 | 1432.327/2643.936/2790.181 | 2411.917 | 278.508 | 11.076 | 8/8 | 1/1 | 2822.341 | — |
| 3 | snapshot | 4976/4976 | 40/4976 | 63519.771/121998.652/126896.865 | 114835.917 | 7218.943 | 32.603 | 1/1 | 1/1 | 128035.498 | — |
| 3 | row | 4976/4976 | 1378/4976 | 1791.891/3340.121/3434.790 | 3076.491 | 313.764 | 12.712 | 8/8 | 2/2 | 3456.886 | — |
| 3 | cached_row | 4976/4976 | 1370/4976 | 1509.012/2452.069/2535.601 | 2222.875 | 312.027 | 11.396 | 8/8 | 1/1 | 2556.033 | — |

## postgres: 1000 registered peers, 32 active / regular_large

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 64/64 | 24.743/28.392/32.236 | 0.105 | 0.045 | 28.250 | 1/1 | 1/1 | 23.858 | — |
| 1 | row | 64/64 | 64/64 | 4.499/8.763/12.645 | 0.118 | 0.068 | 8.652 | 1/1 | 2/2 | 3.735 | — |
| 1 | cached_row | 64/64 | 64/64 | 4.897/7.609/10.705 | 0.111 | 0.067 | 7.477 | 1/1 | 1/1 | 7.639 | — |
| 2 | snapshot | 64/64 | 64/64 | 24.828/28.960/32.105 | 0.098 | 0.052 | 28.836 | 1/1 | 1/1 | 24.371 | — |
| 2 | row | 64/64 | 64/64 | 5.697/8.872/11.844 | 0.111 | 0.066 | 8.741 | 1/1 | 2/2 | 4.990 | — |
| 2 | cached_row | 64/64 | 64/64 | 4.662/10.313/12.349 | 0.114 | 0.071 | 10.205 | 1/1 | 1/1 | 10.554 | — |
| 3 | snapshot | 64/64 | 64/64 | 25.752/32.751/36.038 | 0.107 | 1.413 | 31.631 | 1/1 | 1/1 | 27.742 | — |
| 3 | row | 64/64 | 64/64 | 5.901/10.867/15.473 | 0.110 | 0.068 | 10.750 | 1/1 | 2/2 | 5.561 | — |
| 3 | cached_row | 64/64 | 64/64 | 4.380/10.501/21.451 | 0.112 | 0.069 | 10.345 | 1/1 | 1/1 | 4.519 | — |

## postgres: 1000 registered peers, 32 active / burst_64

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 64/64 | 39/64 | 806.123/1540.917/1620.352 | 704.635 | 817.462 | 28.717 | 1/1 | 1/1 | 1620.352 | 20.223 |
| 1 | row | 64/64 | 64/64 | 42.280/93.431/93.477 | 33.233 | 50.143 | 19.703 | 8/8 | 2/2 | 93.477 | 350.545 |
| 1 | cached_row | 64/64 | 64/64 | 38.256/62.616/65.702 | 27.897 | 36.578 | 13.047 | 8/8 | 1/1 | 65.702 | 498.738 |
| 2 | snapshot | 64/64 | 38/64 | 833.242/1600.666/1673.149 | 735.633 | 844.151 | 31.764 | 1/1 | 1/1 | 1673.149 | 19.585 |
| 2 | row | 64/64 | 64/64 | 32.887/61.730/61.754 | 25.122 | 32.656 | 10.697 | 8/8 | 2/2 | 61.754 | 530.620 |
| 2 | cached_row | 64/64 | 64/64 | 41.373/76.543/76.581 | 23.074 | 47.760 | 18.313 | 8/8 | 1/1 | 76.581 | 427.884 |
| 3 | snapshot | 64/64 | 38/64 | 841.483/1596.037/1674.540 | 735.671 | 846.333 | 29.807 | 1/1 | 1/1 | 1674.540 | 19.568 |
| 3 | row | 64/64 | 64/64 | 38.172/66.300/66.309 | 32.107 | 37.981 | 16.338 | 8/8 | 2/2 | 66.309 | 494.169 |
| 3 | cached_row | 64/64 | 64/64 | 50.154/82.245/82.264 | 42.384 | 49.964 | 21.002 | 8/8 | 1/1 | 82.264 | 398.327 |

## postgres: 1000 registered peers, 32 active / burst_256

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 256/256 | 40/256 | 3259.967/6218.786/6464.416 | 5383.920 | 849.512 | 29.512 | 1/1 | 1/1 | 6514.769 | 20.119 |
| 1 | row | 256/256 | 256/256 | 105.168/208.805/214.837 | 175.916 | 32.007 | 7.736 | 8/8 | 2/2 | 214.871 | 610.003 |
| 1 | cached_row | 256/256 | 256/256 | 110.881/212.813/221.902 | 178.484 | 27.586 | 9.046 | 8/8 | 1/1 | 221.932 | 590.596 |
| 2 | snapshot | 256/256 | 38/256 | 3349.801/6438.898/6702.734 | 5538.303 | 877.695 | 31.529 | 1/1 | 1/1 | 6753.664 | 19.408 |
| 2 | row | 256/256 | 256/256 | 147.209/278.424/285.020 | 242.016 | 49.109 | 19.214 | 8/8 | 2/2 | 285.038 | 459.840 |
| 2 | cached_row | 256/256 | 256/256 | 134.192/240.860/247.562 | 205.054 | 43.915 | 9.568 | 8/8 | 1/1 | 247.581 | 529.410 |
| 3 | snapshot | 256/256 | 38/256 | 3327.219/6379.869/6641.189 | 5538.229 | 882.757 | 30.105 | 1/1 | 1/1 | 6696.646 | 19.573 |
| 3 | row | 256/256 | 256/256 | 117.534/228.369/238.038 | 188.839 | 31.931 | 9.213 | 8/8 | 2/2 | 238.044 | 550.620 |
| 3 | cached_row | 256/256 | 256/256 | 130.278/236.887/244.502 | 201.768 | 39.336 | 10.665 | 8/8 | 1/1 | 244.534 | 536.008 |

## postgres: 1000 registered peers, 32 active / burst_512

| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |
|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | snapshot | 512/512 | 36/512 | 6809.527/12837.020/13337.729 | 11974.932 | 890.350 | 32.047 | 1/1 | 1/1 | 13457.988 | 19.479 |
| 1 | row | 512/512 | 512/512 | 266.731/475.912/499.014 | 441.718 | 46.709 | 10.699 | 8/8 | 2/2 | 499.095 | 525.239 |
| 1 | cached_row | 512/512 | 512/512 | 234.189/427.465/447.396 | 391.964 | 34.773 | 9.879 | 8/8 | 1/1 | 447.459 | 585.850 |
| 2 | snapshot | 512/512 | 38/512 | 6487.440/12601.698/13097.089 | 11746.549 | 975.542 | 29.855 | 1/1 | 1/1 | 13221.855 | 19.827 |
| 2 | row | 512/512 | 512/512 | 261.525/497.979/526.987 | 453.767 | 44.109 | 13.809 | 8/8 | 2/2 | 533.814 | 491.077 |
| 2 | cached_row | 512/512 | 512/512 | 243.382/461.637/483.496 | 426.073 | 35.461 | 9.884 | 8/8 | 1/1 | 483.527 | 542.149 |
| 3 | snapshot | 512/512 | 36/512 | 6602.744/12477.623/13000.759 | 11649.340 | 856.929 | 30.142 | 1/1 | 1/1 | 13150.759 | 19.934 |
| 3 | row | 512/512 | 512/512 | 240.486/439.420/460.340 | 405.450 | 35.171 | 9.696 | 8/8 | 2/2 | 460.362 | 569.430 |
| 3 | cached_row | 512/512 | 512/512 | 203.197/389.027/407.094 | 358.847 | 30.185 | 8.941 | 8/8 | 1/1 | 407.110 | 643.915 |

