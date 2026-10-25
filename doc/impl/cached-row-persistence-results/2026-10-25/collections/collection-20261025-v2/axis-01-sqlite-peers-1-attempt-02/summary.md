# Native persistence benchmark report

Input: `/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/collection-20261025-v2/axis-01-sqlite-peers-1-attempt-02/report.json`

Input SHA-256: `4c27bed30063ab0963a268bf8f09b3f317cc7a24c7175c2a21e1151564e32e2e`

Backend: **sqlite**. Ratios divide paired batch durations; above 1 means the denominator arm finished sooner. Latencies remain per trial, never pooled. Logical bytes and query exchanges are not physical I/O or network packet counts. Application request/result journaling and provider transport are excluded.

## small_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 1048576; wire bytes: 1140494.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 5991.780 | 170.9 | 0.17 | 7905.843 / 9921.774 / 21794.209 |
| 1 | 1 | row | 6364.182 | 160.9 | 0.16 | 8498.186 / 11712.376 / 18891.277 |
| 1 | 2 | cached_row | 5988.866 | 171.0 | 0.17 | 7121.182 / 9880.828 / 15415.849 |
| 2 | 0 | row | 6652.142 | 153.9 | 0.15 | 8714.097 / 12743.265 / 17293.223 |
| 2 | 1 | cached_row | 6144.718 | 166.6 | 0.16 | 8197.926 / 11828.062 / 15996.069 |
| 2 | 2 | snapshot | 5990.286 | 170.9 | 0.17 | 7066.621 / 10926.565 / 14606.443 |
| 3 | 0 | cached_row | 6284.115 | 163.0 | 0.16 | 8083.484 / 13950.031 / 25896.233 |
| 3 | 1 | snapshot | 6131.915 | 167.0 | 0.16 | 7976.795 / 10214.389 / 17849.558 |
| 3 | 2 | row | 6103.358 | 167.8 | 0.16 | 8035.383 / 10546.377 / 15703.724 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.941 | 1.000 | 1.063 |
| 2 | 0.901 | 0.975 | 1.083 |
| 3 | 1.005 | 0.976 | 0.971 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.941 | 0.901 | 1.005 | 3 |
| snapshot_over_cached_row | 0.976 | 0.975 | 1.000 | 3 |
| row_over_cached_row | 1.063 | 0.971 | 1.083 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1388639 / 0 | 0 | 73728 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 846116 / 846117 / 0 | 846116 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 842057 / 842056 | 842056 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1389915 / 0 | 0 | 73728 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 834701 / 834700 / 0 | 834701 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 840000 / 840002 | 840002 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1400976 / 0 | 0 | 73728 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 815333 / 815341 / 0 | 815333 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 843013 / 843011 | 843011 | 0 |

## small_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 1048576; wire bytes: 1140492.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 6368.051 | 160.8 | 0.16 | 8466.957 / 12090.831 / 16105.301 |
| 1 | 1 | cached_row | 6243.404 | 164.0 | 0.16 | 8251.616 / 11492.678 / 16359.465 |
| 1 | 2 | snapshot | 7906.804 | 129.5 | 0.13 | 12099.508 / 14785.216 / 31124.612 |
| 2 | 0 | cached_row | 6138.444 | 166.8 | 0.16 | 7792.733 / 10164.987 / 15595.292 |
| 2 | 1 | snapshot | 6315.580 | 162.1 | 0.16 | 8284.157 / 11179.264 / 16127.233 |
| 2 | 2 | row | 6072.001 | 168.6 | 0.16 | 7390.414 / 10008.796 / 13089.449 |
| 3 | 0 | snapshot | 6230.935 | 164.3 | 0.16 | 8972.988 / 11083.416 / 14706.709 |
| 3 | 1 | row | 6373.209 | 160.7 | 0.16 | 8503.735 / 11519.057 / 15687.915 |
| 3 | 2 | cached_row | 6018.150 | 170.2 | 0.17 | 7276.551 / 10471.017 / 15946.446 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.242 | 1.266 | 1.020 |
| 2 | 1.040 | 1.029 | 0.989 |
| 3 | 0.978 | 1.035 | 1.059 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.040 | 0.978 | 1.242 | 3 |
| snapshot_over_cached_row | 1.035 | 1.029 | 1.266 | 3 |
| row_over_cached_row | 1.020 | 0.989 | 1.059 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1390735 / 0 | 0 | 73728 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 851020 / 851022 / 0 | 851020 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 841909 / 841912 | 841912 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1394814 / 0 | 0 | 73728 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 831740 / 831734 / 0 | 831740 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 839778 / 839780 | 839780 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1398022 / 0 | 0 | 73728 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 824450 / 824467 / 0 | 824450 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 852296 / 852290 | 852290 | 0 |

## large_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 128; plaintext bytes: 8388608; wire bytes: 8400384.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 783.973 | 163.3 | 10.20 | 7427.783 / 11285.673 / 12913.712 |
| 1 | 1 | cached_row | 774.314 | 165.3 | 10.33 | 7805.807 / 11507.666 / 15049.427 |
| 1 | 2 | snapshot | 751.766 | 170.3 | 10.64 | 6504.495 / 9849.680 / 11215.653 |
| 2 | 0 | cached_row | 783.391 | 163.4 | 10.21 | 7260.792 / 13478.553 / 14107.845 |
| 2 | 1 | snapshot | 750.940 | 170.5 | 10.65 | 6545.501 / 7128.155 / 11088.415 |
| 2 | 2 | row | 779.845 | 164.1 | 10.26 | 9472.388 / 10763.240 / 11061.376 |
| 3 | 0 | snapshot | 751.188 | 170.4 | 10.65 | 6867.841 / 8427.694 / 11441.864 |
| 3 | 1 | row | 756.135 | 169.3 | 10.58 | 6603.379 / 11075.561 / 11227.254 |
| 3 | 2 | cached_row | 781.788 | 163.7 | 10.23 | 8459.763 / 10996.644 / 16841.762 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.959 | 0.971 | 1.012 |
| 2 | 0.963 | 0.959 | 0.995 |
| 3 | 0.993 | 0.961 | 0.967 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.963 | 0.959 | 0.993 | 3 |
| snapshot_over_cached_row | 0.961 | 0.959 | 0.971 | 3 |
| row_over_cached_row | 0.995 | 0.967 | 1.012 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 174610 / 0 | 0 | 9216 |
| 1 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 106195 / 106192 / 0 | 106195 | 0 |
| 1 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 104945 / 104945 | 104945 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 174397 / 0 | 0 | 9216 |
| 2 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 103723 / 103726 / 0 | 103723 | 0 |
| 2 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 104839 / 104837 | 104837 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 175547 / 0 | 0 | 9216 |
| 3 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 104225 / 104224 / 0 | 104225 | 0 |
| 3 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 106254 / 106262 | 106262 | 0 |

## large_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 128; plaintext bytes: 8388608; wire bytes: 8400384.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 780.526 | 164.0 | 10.25 | 7573.454 / 15851.660 / 19160.738 |
| 1 | 1 | snapshot | 767.304 | 166.8 | 10.43 | 7857.313 / 10980.024 / 11121.367 |
| 1 | 2 | row | 810.503 | 157.9 | 9.87 | 8329.101 / 8922.755 / 15332.022 |
| 2 | 0 | snapshot | 765.750 | 167.2 | 10.45 | 7874.605 / 11953.936 / 13646.006 |
| 2 | 1 | row | 775.377 | 165.1 | 10.32 | 8020.606 / 14014.391 / 16019.241 |
| 2 | 2 | cached_row | 786.328 | 162.8 | 10.17 | 9529.484 / 11075.973 / 11237.884 |
| 3 | 0 | row | 787.548 | 162.5 | 10.16 | 8702.154 / 11166.120 / 12613.844 |
| 3 | 1 | cached_row | 745.482 | 171.7 | 10.73 | 6423.875 / 10064.630 / 11097.913 |
| 3 | 2 | snapshot | 790.494 | 161.9 | 10.12 | 7886.958 / 12516.353 / 13644.413 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.947 | 0.983 | 1.038 |
| 2 | 0.988 | 0.974 | 0.986 |
| 3 | 1.004 | 1.060 | 1.056 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.988 | 0.947 | 1.004 | 3 |
| snapshot_over_cached_row | 0.983 | 0.974 | 1.060 | 3 |
| row_over_cached_row | 1.038 | 0.986 | 1.056 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 173690 / 0 | 0 | 9216 |
| 1 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 106166 / 106167 / 0 | 106166 | 0 |
| 1 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 105334 / 105337 | 105337 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 174517 / 0 | 0 | 9216 |
| 2 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 104477 / 104488 / 0 | 104477 | 0 |
| 2 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 105355 / 105352 | 105352 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 175648 / 0 | 0 | 9216 |
| 3 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 103058 / 103056 / 0 | 103058 | 0 |
| 3 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 105631 / 105635 | 105635 | 0 |

## mixed_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 5177344; wire bytes: 5269632.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 6186.407 | 165.5 | 0.80 | 8047.076 / 11309.417 / 15417.011 |
| 1 | 1 | snapshot | 6487.983 | 157.8 | 0.76 | 8625.712 / 11905.296 / 18946.931 |
| 1 | 2 | row | 6635.592 | 154.3 | 0.74 | 8787.474 / 12344.854 / 20082.584 |
| 2 | 0 | snapshot | 6313.324 | 162.2 | 0.78 | 8467.739 / 13303.838 / 18028.421 |
| 2 | 1 | row | 6093.883 | 168.0 | 0.81 | 7961.046 / 10673.945 / 16559.277 |
| 2 | 2 | cached_row | 6405.205 | 159.9 | 0.77 | 8496.372 / 12349.141 / 19547.207 |
| 3 | 0 | row | 6229.125 | 164.4 | 0.79 | 8410.421 / 11101.009 / 15762.243 |
| 3 | 1 | cached_row | 6331.654 | 161.7 | 0.78 | 8520.506 / 11642.356 / 15756.894 |
| 3 | 2 | snapshot | 6425.327 | 159.4 | 0.77 | 8770.572 / 11739.788 / 16256.734 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.978 | 1.049 | 1.073 |
| 2 | 1.036 | 0.986 | 0.951 |
| 3 | 1.031 | 1.015 | 0.984 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.031 | 0.978 | 1.036 | 3 |
| snapshot_over_cached_row | 1.015 | 0.986 | 1.049 | 3 |
| row_over_cached_row | 0.984 | 0.951 | 1.073 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1390874 / 0 | 0 | 73728 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 850333 / 850335 / 0 | 850333 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 836852 / 836854 | 836854 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1387769 / 0 | 0 | 73728 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 841014 / 841018 / 0 | 841014 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 841993 / 841995 | 841995 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1397902 / 0 | 0 | 73728 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 831751 / 831757 / 0 | 831751 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 846127 / 846117 | 846117 | 0 |

## mixed_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 5177344; wire bytes: 5269632.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 7034.775 | 145.6 | 0.70 | 11822.622 / 15798.982 / 18230.928 |
| 1 | 1 | row | 6793.783 | 150.7 | 0.73 | 9004.618 / 12883.426 / 19293.736 |
| 1 | 2 | cached_row | 6369.668 | 160.8 | 0.78 | 8724.776 / 12135.645 / 22238.295 |
| 2 | 0 | row | 8543.870 | 119.9 | 0.58 | 12351.276 / 16496.911 / 26441.578 |
| 2 | 1 | cached_row | 7086.501 | 144.5 | 0.70 | 9954.466 / 14683.236 / 20169.436 |
| 2 | 2 | snapshot | 6018.607 | 170.1 | 0.82 | 7476.694 / 10489.751 / 15726.968 |
| 3 | 0 | cached_row | 6062.798 | 168.9 | 0.81 | 7877.290 / 10415.213 / 14948.379 |
| 3 | 1 | snapshot | 6292.682 | 162.7 | 0.78 | 8369.045 / 11521.922 / 14764.848 |
| 3 | 2 | row | 6226.121 | 164.5 | 0.79 | 8430.549 / 10755.736 / 34322.975 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.035 | 1.104 | 1.067 |
| 2 | 0.704 | 0.849 | 1.206 |
| 3 | 1.011 | 1.038 | 1.027 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.011 | 0.704 | 1.035 | 3 |
| snapshot_over_cached_row | 1.038 | 0.849 | 1.104 | 3 |
| row_over_cached_row | 1.067 | 1.027 | 1.206 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1386718 / 0 | 0 | 73728 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 851351 / 851351 / 0 | 851351 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 840899 / 840896 | 840896 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1387732 / 0 | 0 | 73728 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 839958 / 839949 / 0 | 839958 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 840871 / 840872 | 840872 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1400032 / 0 | 0 | 73728 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 830971 / 830971 / 0 | 830971 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 855264 / 855263 | 855263 | 0 |

## burst_64 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 64; plaintext bytes: 32768000; wire bytes: 32773888.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 422.206 | 151.6 | 74.02 | 7493.857 / 11797.024 / 11797.024 |
| 1 | 1 | row | 428.976 | 149.2 | 72.85 | 7708.746 / 13457.384 / 13457.384 |
| 1 | 2 | cached_row | 449.592 | 142.4 | 69.51 | 8963.842 / 17221.890 / 17221.890 |
| 2 | 0 | row | 422.581 | 151.5 | 73.95 | 7686.645 / 11642.227 / 11642.227 |
| 2 | 1 | cached_row | 422.791 | 151.4 | 73.91 | 7813.161 / 12123.823 / 12123.823 |
| 2 | 2 | snapshot | 429.775 | 148.9 | 72.71 | 7911.514 / 12364.220 / 12364.220 |
| 3 | 0 | cached_row | 530.640 | 120.6 | 58.89 | 13032.213 / 19467.649 / 19467.649 |
| 3 | 1 | snapshot | 421.213 | 151.9 | 74.19 | 7370.517 / 12234.398 / 12234.398 |
| 3 | 2 | row | 416.983 | 153.5 | 74.94 | 7055.340 / 12161.643 / 12161.643 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.984 | 0.939 | 0.954 |
| 2 | 1.017 | 1.017 | 1.000 |
| 3 | 1.010 | 0.794 | 0.786 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.010 | 0.984 | 1.017 | 3 |
| snapshot_over_cached_row | 0.939 | 0.794 | 1.017 | 3 |
| row_over_cached_row | 0.954 | 0.786 | 1.000 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 86420 / 0 | 0 | 4608 |
| 1 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 53164 / 53162 / 0 | 53164 | 0 |
| 1 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52490 / 52487 | 52487 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 87117 / 0 | 0 | 4608 |
| 2 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 51947 / 51946 / 0 | 51947 | 0 |
| 2 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52541 / 52538 | 52538 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 87925 / 0 | 0 | 4608 |
| 3 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 51984 / 51973 / 0 | 51984 | 0 |
| 3 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52910 / 52918 | 52918 | 0 |

## burst_64 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 64; plaintext bytes: 32768000; wire bytes: 32773888.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 426.077 | 150.2 | 73.34 | 8524.244 / 11822.221 / 11822.221 |
| 1 | 1 | cached_row | 421.257 | 151.9 | 74.18 | 9831.396 / 11873.917 / 11873.917 |
| 1 | 2 | snapshot | 429.383 | 149.1 | 72.78 | 8256.996 / 11465.387 / 11465.387 |
| 2 | 0 | cached_row | 415.611 | 154.0 | 75.19 | 8115.393 / 12739.368 / 12739.368 |
| 2 | 1 | snapshot | 408.387 | 156.7 | 76.52 | 7520.666 / 11914.082 / 11914.082 |
| 2 | 2 | row | 405.224 | 157.9 | 77.12 | 7022.459 / 11828.413 / 11828.413 |
| 3 | 0 | snapshot | 441.434 | 145.0 | 70.79 | 8829.241 / 12925.124 / 12925.124 |
| 3 | 1 | row | 419.972 | 152.4 | 74.41 | 8617.166 / 11837.309 / 11837.309 |
| 3 | 2 | cached_row | 413.214 | 154.9 | 75.63 | 7591.137 / 11683.603 / 11683.603 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.008 | 1.019 | 1.011 |
| 2 | 1.008 | 0.983 | 0.975 |
| 3 | 1.051 | 1.068 | 1.016 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.008 | 1.008 | 1.051 | 3 |
| snapshot_over_cached_row | 1.019 | 0.983 | 1.068 | 3 |
| row_over_cached_row | 1.011 | 0.975 | 1.016 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 87258 / 0 | 0 | 4608 |
| 1 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 53054 / 53061 / 0 | 53054 | 0 |
| 1 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52737 / 52735 | 52735 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 87320 / 0 | 0 | 4608 |
| 2 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 52450 / 52457 / 0 | 52450 | 0 |
| 2 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52751 / 52752 | 52752 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 87999 / 0 | 0 | 4608 |
| 3 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 51241 / 51240 / 0 | 51241 | 0 |
| 3 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52902 / 52901 | 52901 | 0 |

## burst_256 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 256; plaintext bytes: 131072000; wire bytes: 131095552.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 1718.413 | 149.0 | 72.74 | 8119.460 / 12096.622 / 13607.764 |
| 1 | 1 | cached_row | 2107.214 | 121.5 | 59.32 | 11580.291 / 15151.287 / 16319.160 |
| 1 | 2 | snapshot | 2176.003 | 117.6 | 57.44 | 12188.643 / 16469.249 / 17306.397 |
| 2 | 0 | cached_row | 1927.278 | 132.8 | 64.86 | 11043.652 / 13670.862 / 19367.252 |
| 2 | 1 | snapshot | 1725.673 | 148.3 | 72.44 | 8351.121 / 10915.685 / 12803.838 |
| 2 | 2 | row | 1729.378 | 148.0 | 72.28 | 8956.828 / 12005.131 / 12304.108 |
| 3 | 0 | snapshot | 1829.797 | 139.9 | 68.31 | 9011.301 / 12193.101 / 13018.608 |
| 3 | 1 | row | 1778.494 | 143.9 | 70.28 | 9084.096 / 12133.210 / 12507.367 |
| 3 | 2 | cached_row | 1828.013 | 140.0 | 68.38 | 9851.254 / 12259.275 / 12960.249 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.266 | 1.033 | 0.815 |
| 2 | 0.998 | 0.895 | 0.897 |
| 3 | 1.029 | 1.001 | 0.973 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.029 | 0.998 | 1.266 | 3 |
| snapshot_over_cached_row | 1.001 | 0.895 | 1.033 | 3 |
| row_over_cached_row | 0.897 | 0.815 | 0.973 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 347665 / 0 | 0 | 18432 |
| 1 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 214358 / 214363 / 0 | 214358 | 0 |
| 1 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 210525 / 210527 | 210527 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 348691 / 0 | 0 | 18432 |
| 2 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 209701 / 209705 / 0 | 209701 | 0 |
| 2 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 209896 / 209903 | 209903 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 351018 / 0 | 0 | 18432 |
| 3 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 207638 / 207648 / 0 | 207638 | 0 |
| 3 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 212092 / 212093 | 212093 | 0 |

## burst_256 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 256; plaintext bytes: 131072000; wire bytes: 131095552.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 1825.792 | 140.2 | 68.46 | 9680.445 / 12267.821 / 16785.347 |
| 1 | 1 | snapshot | 1778.285 | 144.0 | 70.29 | 9152.323 / 13916.839 / 16399.089 |
| 1 | 2 | row | 1754.760 | 145.9 | 71.23 | 8682.208 / 11559.302 / 13284.212 |
| 2 | 0 | snapshot | 1664.673 | 153.8 | 75.09 | 8070.849 / 12454.799 / 14236.935 |
| 2 | 1 | row | 1672.879 | 153.0 | 74.72 | 9083.545 / 12118.603 / 17272.234 |
| 2 | 2 | cached_row | 1646.385 | 155.5 | 75.92 | 7992.895 / 11045.035 / 11898.172 |
| 3 | 0 | row | 2037.357 | 125.7 | 61.35 | 10849.111 / 13564.193 / 18511.810 |
| 3 | 1 | cached_row | 1837.362 | 139.3 | 68.03 | 9793.957 / 14458.327 / 18764.321 |
| 3 | 2 | snapshot | 1821.972 | 140.5 | 68.61 | 10207.937 / 14701.970 / 16914.278 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.013 | 0.974 | 0.961 |
| 2 | 0.995 | 1.011 | 1.016 |
| 3 | 0.894 | 0.992 | 1.109 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.995 | 0.894 | 1.013 | 3 |
| snapshot_over_cached_row | 0.992 | 0.974 | 1.011 | 3 |
| row_over_cached_row | 1.016 | 0.961 | 1.109 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 346653 / 0 | 0 | 18432 |
| 1 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 213632 / 213624 / 0 | 213632 | 0 |
| 1 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 210503 / 210505 | 210505 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 347910 / 0 | 0 | 18432 |
| 2 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 210769 / 210765 / 0 | 210769 | 0 |
| 2 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 209246 / 209245 | 209245 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 349772 / 0 | 0 | 18432 |
| 3 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 207427 / 207426 / 0 | 207427 | 0 |
| 3 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 211502 / 211499 | 211499 | 0 |

## burst_512 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 512; plaintext bytes: 262144000; wire bytes: 262191104.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 3616.290 | 141.6 | 69.13 | 9294.498 / 12075.152 / 15780.998 |
| 1 | 1 | snapshot | 3893.924 | 131.5 | 64.20 | 10567.917 / 13812.315 / 19471.226 |
| 1 | 2 | row | 3765.869 | 136.0 | 66.39 | 10409.021 / 16757.856 / 25590.054 |
| 2 | 0 | snapshot | 3663.959 | 139.7 | 68.23 | 9310.497 / 13604.749 / 18248.060 |
| 2 | 1 | row | 3497.258 | 146.4 | 71.48 | 8541.115 / 12421.977 / 14498.171 |
| 2 | 2 | cached_row | 3549.397 | 144.2 | 70.43 | 8798.184 / 10086.381 / 16429.666 |
| 3 | 0 | row | 3501.430 | 146.2 | 71.40 | 8961.807 / 10832.569 / 13865.845 |
| 3 | 1 | cached_row | 3836.150 | 133.5 | 65.17 | 10804.728 / 14582.318 / 16599.682 |
| 3 | 2 | snapshot | 3628.750 | 141.1 | 68.89 | 9836.556 / 13608.064 / 15966.464 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.034 | 1.077 | 1.041 |
| 2 | 1.048 | 1.032 | 0.985 |
| 3 | 1.036 | 0.946 | 0.913 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.036 | 1.034 | 1.048 | 3 |
| snapshot_over_cached_row | 1.032 | 0.946 | 1.077 | 3 |
| row_over_cached_row | 0.985 | 0.913 | 1.041 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 691380 / 0 | 0 | 36864 |
| 1 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 424607 / 424605 / 0 | 424607 | 0 |
| 1 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 419951 / 419949 | 419949 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 693804 / 0 | 0 | 36864 |
| 2 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 417365 / 417361 / 0 | 417365 | 0 |
| 2 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 420389 / 420382 | 420382 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 698430 / 0 | 0 | 36864 |
| 3 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 415051 / 415044 / 0 | 415051 | 0 |
| 3 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 425633 / 425630 | 425630 | 0 |

## burst_512 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 512; plaintext bytes: 262144000; wire bytes: 262191104.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 3750.379 | 136.5 | 66.66 | 9695.534 / 12595.510 / 18854.508 |
| 1 | 1 | row | 3495.220 | 146.5 | 71.53 | 8976.595 / 10424.009 / 15433.321 |
| 1 | 2 | cached_row | 3351.385 | 152.8 | 74.60 | 7959.212 / 11064.691 / 16018.280 |
| 2 | 0 | row | 4076.661 | 125.6 | 61.32 | 11156.011 / 15379.431 / 20151.221 |
| 2 | 1 | cached_row | 3490.259 | 146.7 | 71.63 | 9014.496 / 11701.617 / 16793.242 |
| 2 | 2 | snapshot | 3424.128 | 149.5 | 73.01 | 8672.840 / 11477.489 / 14240.422 |
| 3 | 0 | cached_row | 3458.420 | 148.0 | 72.29 | 8854.969 / 11501.515 / 13952.014 |
| 3 | 1 | snapshot | 3263.267 | 156.9 | 76.61 | 7733.052 / 10700.854 / 18506.480 |
| 3 | 2 | row | 3323.110 | 154.1 | 75.23 | 8245.304 / 10407.117 / 12405.256 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.073 | 1.119 | 1.043 |
| 2 | 0.840 | 0.981 | 1.168 |
| 3 | 0.982 | 0.944 | 0.961 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.982 | 0.840 | 1.073 | 3 |
| snapshot_over_cached_row | 0.981 | 0.944 | 1.119 | 3 |
| row_over_cached_row | 1.043 | 0.961 | 1.168 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 692894 / 0 | 0 | 36864 |
| 1 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 426040 / 426042 / 0 | 426040 | 0 |
| 1 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 422026 / 422026 | 422026 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 695973 / 0 | 0 | 36864 |
| 2 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 419605 / 419607 / 0 | 419605 | 0 |
| 2 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 421980 / 421977 | 421977 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 701091 / 0 | 0 | 36864 |
| 3 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 411166 / 411163 / 0 | 411166 | 0 |
| 3 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 424491 / 424493 | 424493 | 0 |

