# Native persistence benchmark report

Input: `/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/collection-20261025-v2/axis-02-postgres-peers-1-attempt-01/report.json`

Input SHA-256: `760110c89a89a1b5cd2fa9a90ba4c7c300bb3f78d4fd238b0062627daf5cff30`

Backend: **postgres**. Ratios divide paired batch durations; above 1 means the denominator arm finished sooner. Latencies remain per trial, never pooled. Logical bytes and query exchanges are not physical I/O or network packet counts. Application request/result journaling and provider transport are excluded.

## small_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 1048576; wire bytes: 1140494.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 1739.285 | 588.7 | 0.57 | 2480.256 / 4144.132 / 6209.496 |
| 1 | 1 | row | 1833.477 | 558.5 | 0.55 | 2542.652 / 3482.582 / 6151.528 |
| 1 | 2 | cached_row | 2111.698 | 484.9 | 0.47 | 3984.596 / 5404.979 / 9265.453 |
| 2 | 0 | row | 2327.087 | 440.0 | 0.43 | 3897.122 / 5196.681 / 14294.723 |
| 2 | 1 | cached_row | 1804.084 | 567.6 | 0.55 | 2520.150 / 4054.065 / 7301.268 |
| 2 | 2 | snapshot | 2010.305 | 509.4 | 0.50 | 4234.119 / 5263.726 / 7065.499 |
| 3 | 0 | cached_row | 1918.743 | 533.7 | 0.52 | 3302.887 / 4413.814 / 7187.496 |
| 3 | 1 | snapshot | 1848.827 | 553.9 | 0.54 | 3315.991 / 4499.694 / 8042.256 |
| 3 | 2 | row | 1990.952 | 514.3 | 0.50 | 3315.430 / 5119.167 / 12149.761 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.949 | 0.824 | 0.868 |
| 2 | 0.864 | 1.114 | 1.290 |
| 3 | 0.929 | 0.964 | 1.038 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.929 | 0.864 | 0.949 | 3 |
| snapshot_over_cached_row | 0.964 | 0.824 | 1.114 | 3 |
| row_over_cached_row | 1.038 | 0.868 | 1.290 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1390758 / 0 | 73728 | 0 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 834817 / 834817 / 0 | 834817 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 844684 / 844682 | 844682 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1390704 / 0 | 73728 | 0 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 823365 / 823367 / 0 | 823365 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 839952 / 839954 | 839954 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1378478 / 0 | 73728 | 0 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 838949 / 838955 / 0 | 838949 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 843838 / 843833 | 843833 | 0 |

## small_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 1048576; wire bytes: 1140492.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 3221.336 | 317.9 | 0.31 | 4933.511 / 7016.818 / 12156.313 |
| 1 | 1 | cached_row | 3075.374 | 333.0 | 0.33 | 4990.247 / 8407.386 / 17498.625 |
| 1 | 2 | snapshot | 3009.381 | 340.3 | 0.33 | 5073.542 / 7420.770 / 11996.295 |
| 2 | 0 | cached_row | 2451.904 | 417.6 | 0.41 | 5105.561 / 6743.279 / 9285.590 |
| 2 | 1 | snapshot | 1859.945 | 550.6 | 0.54 | 3314.609 / 4649.312 / 8346.103 |
| 2 | 2 | row | 2012.584 | 508.8 | 0.50 | 3125.186 / 6213.192 / 12021.402 |
| 3 | 0 | snapshot | 1854.106 | 552.3 | 0.54 | 3154.761 / 4105.230 / 7192.896 |
| 3 | 1 | row | 2150.893 | 476.1 | 0.46 | 3618.795 / 5226.556 / 8101.647 |
| 3 | 2 | cached_row | 1964.554 | 521.2 | 0.51 | 3561.208 / 4682.514 / 9014.776 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.934 | 0.979 | 1.047 |
| 2 | 0.924 | 0.759 | 0.821 |
| 3 | 0.862 | 0.944 | 1.095 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.924 | 0.862 | 0.934 | 3 |
| snapshot_over_cached_row | 0.944 | 0.759 | 0.979 | 3 |
| row_over_cached_row | 1.047 | 0.821 | 1.095 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1395879 / 0 | 73728 | 0 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 840799 / 840806 / 0 | 840799 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 843968 / 843971 | 843971 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1391835 / 0 | 73728 | 0 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 828582 / 828586 / 0 | 828582 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 839926 / 839922 | 839922 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1391870 / 0 | 73728 | 0 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 837661 / 837661 / 0 | 837661 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 843949 / 843947 | 843947 | 0 |

## large_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 128; plaintext bytes: 8388608; wire bytes: 8400384.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 423.910 | 302.0 | 18.87 | 5967.575 / 6293.502 / 6466.965 |
| 1 | 1 | cached_row | 389.727 | 328.4 | 20.53 | 4030.100 / 5950.764 / 6070.076 |
| 1 | 2 | snapshot | 245.758 | 520.8 | 32.55 | 3282.528 / 3583.640 / 3685.980 |
| 2 | 0 | cached_row | 248.022 | 516.1 | 32.26 | 3161.393 / 3983.924 / 6635.479 |
| 2 | 1 | snapshot | 251.413 | 509.1 | 31.82 | 3355.906 / 5190.189 / 6330.751 |
| 2 | 2 | row | 235.572 | 543.4 | 33.96 | 2693.132 / 2715.354 / 3577.859 |
| 3 | 0 | snapshot | 221.645 | 577.5 | 36.09 | 2546.830 / 2588.848 / 3450.121 |
| 3 | 1 | row | 264.598 | 483.8 | 30.23 | 3395.319 / 5126.120 / 6319.490 |
| 3 | 2 | cached_row | 330.402 | 387.4 | 24.21 | 4119.586 / 4705.968 / 9952.812 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.580 | 0.631 | 1.088 |
| 2 | 1.067 | 1.014 | 0.950 |
| 3 | 0.838 | 0.671 | 0.801 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.838 | 0.580 | 1.067 | 3 |
| snapshot_over_cached_row | 0.671 | 0.631 | 1.014 | 3 |
| row_over_cached_row | 0.950 | 0.801 | 1.088 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 128 | 128 / 128 | 0 / 174762 / 0 | 9216 | 0 |
| 1 | row | 128 / 0 / 128 | 128 / 128 | 256 / 256 | 105397 / 105395 / 0 | 105397 | 0 |
| 1 | cached_row | 0 / 128 / 128 | 0 / 128 | 128 / 128 | 0 / 105379 / 105376 | 105376 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 128 | 128 / 128 | 0 / 173346 / 0 | 9216 | 0 |
| 2 | row | 128 / 0 / 128 | 128 / 128 | 256 / 256 | 103553 / 103557 / 0 | 103553 | 0 |
| 2 | cached_row | 0 / 128 / 128 | 0 / 128 | 128 / 128 | 0 / 105588 / 105580 | 105580 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 128 | 128 / 128 | 0 / 174049 / 0 | 9216 | 0 |
| 3 | row | 128 / 0 / 128 | 128 / 128 | 256 / 256 | 105021 / 105026 / 0 | 105021 | 0 |
| 3 | cached_row | 0 / 128 / 128 | 0 / 128 | 128 / 128 | 0 / 105858 / 105859 | 105859 | 0 |

## large_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 128; plaintext bytes: 8388608; wire bytes: 8400384.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 253.353 | 505.2 | 31.58 | 3205.425 / 3888.616 / 3894.447 |
| 1 | 1 | snapshot | 226.086 | 566.2 | 35.38 | 2541.940 / 2935.363 / 3285.374 |
| 1 | 2 | row | 261.072 | 490.3 | 30.64 | 3321.872 / 5013.581 / 7093.902 |
| 2 | 0 | snapshot | 230.215 | 556.0 | 34.75 | 2628.452 / 4072.369 / 4370.072 |
| 2 | 1 | row | 256.542 | 498.9 | 31.18 | 3384.549 / 5543.486 / 6162.849 |
| 2 | 2 | cached_row | 224.081 | 571.2 | 35.70 | 2538.414 / 2595.981 / 2850.205 |
| 3 | 0 | row | 335.351 | 381.7 | 23.86 | 4063.753 / 4861.217 / 9884.986 |
| 3 | 1 | cached_row | 307.188 | 416.7 | 26.04 | 4008.530 / 4342.011 / 6435.286 |
| 3 | 2 | snapshot | 304.846 | 419.9 | 26.24 | 4287.609 / 6002.821 / 7303.973 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.866 | 0.892 | 1.030 |
| 2 | 0.897 | 1.027 | 1.145 |
| 3 | 0.909 | 0.992 | 1.092 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.897 | 0.866 | 0.909 | 3 |
| snapshot_over_cached_row | 0.992 | 0.892 | 1.027 | 3 |
| row_over_cached_row | 1.092 | 1.030 | 1.145 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 128 | 128 / 128 | 0 / 175360 / 0 | 9216 | 0 |
| 1 | row | 128 / 0 / 128 | 128 / 128 | 256 / 256 | 104960 / 104956 / 0 | 104960 | 0 |
| 1 | cached_row | 0 / 128 / 128 | 0 / 128 | 128 / 128 | 0 / 106097 / 106085 | 106085 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 128 | 128 / 128 | 0 / 174120 / 0 | 9216 | 0 |
| 2 | row | 128 / 0 / 128 | 128 / 128 | 256 / 256 | 104211 / 104218 / 0 | 104211 | 0 |
| 2 | cached_row | 0 / 128 / 128 | 0 / 128 | 128 / 128 | 0 / 106085 / 106091 | 106091 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 128 | 128 / 128 | 0 / 173482 / 0 | 9216 | 0 |
| 3 | row | 128 / 0 / 128 | 128 / 128 | 256 / 256 | 105503 / 105505 / 0 | 105503 | 0 |
| 3 | cached_row | 0 / 128 / 128 | 0 / 128 | 128 / 128 | 0 / 105490 / 105490 | 105490 | 0 |

## mixed_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 5177344; wire bytes: 5269632.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 2021.903 | 506.5 | 2.44 | 3501.907 / 5303.220 / 8328.399 |
| 1 | 1 | snapshot | 1857.053 | 551.4 | 2.66 | 3295.633 / 4548.004 / 12099.377 |
| 1 | 2 | row | 1925.072 | 531.9 | 2.56 | 2867.477 / 4064.884 / 7101.215 |
| 2 | 0 | snapshot | 1755.621 | 583.3 | 2.81 | 2496.906 / 4092.476 / 7242.879 |
| 2 | 1 | row | 1880.377 | 544.6 | 2.63 | 2642.988 / 4012.508 / 7892.628 |
| 2 | 2 | cached_row | 1813.465 | 564.7 | 2.72 | 2626.257 / 4551.991 / 7232.319 |
| 3 | 0 | row | 2196.092 | 466.3 | 2.25 | 3886.823 / 5484.817 / 9393.712 |
| 3 | 1 | cached_row | 1792.951 | 571.1 | 2.75 | 2519.408 / 3494.714 / 12835.947 |
| 3 | 2 | snapshot | 1787.888 | 572.7 | 2.76 | 2714.912 / 4474.878 / 9142.805 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.965 | 0.918 | 0.952 |
| 2 | 0.934 | 0.968 | 1.037 |
| 3 | 0.814 | 0.997 | 1.225 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.934 | 0.814 | 0.965 | 3 |
| snapshot_over_cached_row | 0.968 | 0.918 | 0.997 | 3 |
| row_over_cached_row | 1.037 | 0.952 | 1.225 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1392840 / 0 | 73728 | 0 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 838814 / 838815 / 0 | 838814 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 855372 / 855378 | 855378 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1391902 / 0 | 73728 | 0 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 835842 / 835841 / 0 | 835842 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 838806 / 838812 | 838812 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1389803 / 0 | 73728 | 0 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 842046 / 842041 / 0 | 842046 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 847239 / 847236 | 847236 | 0 |

## mixed_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 5177344; wire bytes: 5269632.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 1936.491 | 528.8 | 2.55 | 3485.477 / 5580.475 / 9602.790 |
| 1 | 1 | row | 2943.434 | 347.9 | 1.68 | 4451.905 / 6589.693 / 10571.123 |
| 1 | 2 | cached_row | 1961.196 | 522.1 | 2.52 | 3512.617 / 5075.806 / 8806.479 |
| 2 | 0 | row | 1978.118 | 517.7 | 2.50 | 2733.156 / 5203.443 / 12122.239 |
| 2 | 1 | cached_row | 1847.000 | 554.4 | 2.67 | 2568.240 / 4448.228 / 7334.069 |
| 2 | 2 | snapshot | 1960.541 | 522.3 | 2.52 | 3511.344 / 5439.613 / 8522.310 |
| 3 | 0 | cached_row | 1911.239 | 535.8 | 2.58 | 3006.956 / 4290.634 / 10441.742 |
| 3 | 1 | snapshot | 1794.299 | 570.7 | 2.75 | 2631.216 / 3927.109 / 8025.405 |
| 3 | 2 | row | 1938.970 | 528.1 | 2.55 | 2851.186 / 4572.208 / 6894.611 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.658 | 0.987 | 1.501 |
| 2 | 0.991 | 1.061 | 1.071 |
| 3 | 0.925 | 0.939 | 1.015 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.925 | 0.658 | 0.991 | 3 |
| snapshot_over_cached_row | 0.987 | 0.939 | 1.061 | 3 |
| row_over_cached_row | 1.071 | 1.015 | 1.501 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1394051 / 0 | 73728 | 0 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 840919 / 840921 / 0 | 840919 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 841925 / 841932 | 841932 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1391850 / 0 | 73728 | 0 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 832722 / 832720 / 0 | 832722 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 843086 / 843076 | 843076 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 1024 | 1024 / 1024 | 0 / 1385749 / 0 | 73728 | 0 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 2048 / 2048 | 838854 / 838847 / 0 | 838854 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 1024 / 1024 | 0 / 847140 / 847137 | 847137 | 0 |

## burst_64 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 64; plaintext bytes: 32768000; wire bytes: 32773888.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 179.582 | 356.4 | 174.02 | 4706.148 / 4982.813 / 4982.813 |
| 1 | 1 | row | 168.935 | 378.8 | 184.98 | 3454.299 / 4020.191 / 4020.191 |
| 1 | 2 | cached_row | 163.944 | 390.4 | 190.61 | 3322.914 / 5142.260 / 5142.260 |
| 2 | 0 | row | 181.084 | 353.4 | 172.57 | 4023.968 / 4715.786 / 4715.786 |
| 2 | 1 | cached_row | 165.723 | 386.2 | 188.57 | 3607.954 / 4346.048 / 4346.048 |
| 2 | 2 | snapshot | 160.637 | 398.4 | 194.54 | 3466.651 / 3604.649 / 3604.649 |
| 3 | 0 | cached_row | 177.318 | 360.9 | 176.24 | 4217.068 / 5034.799 / 5034.799 |
| 3 | 1 | snapshot | 170.778 | 374.8 | 182.99 | 4310.983 / 4871.456 / 4871.456 |
| 3 | 2 | row | 192.489 | 332.5 | 162.35 | 3873.729 / 13221.275 / 13221.275 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.063 | 1.095 | 1.030 |
| 2 | 0.887 | 0.969 | 1.093 |
| 3 | 0.887 | 0.963 | 1.086 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.887 | 0.887 | 1.063 | 3 |
| snapshot_over_cached_row | 0.969 | 0.963 | 1.095 | 3 |
| row_over_cached_row | 1.086 | 1.030 | 1.093 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 64 | 64 / 64 | 0 / 87470 / 0 | 4608 | 0 |
| 1 | row | 64 / 0 / 64 | 64 / 64 | 128 / 128 | 52529 / 52529 / 0 | 52529 | 0 |
| 1 | cached_row | 0 / 64 / 64 | 0 / 64 | 64 / 64 | 0 / 52945 / 52936 | 52936 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 64 | 64 / 64 | 0 / 87440 / 0 | 4608 | 0 |
| 2 | row | 64 / 0 / 64 | 64 / 64 | 128 / 128 | 52157 / 52157 / 0 | 52157 | 0 |
| 2 | cached_row | 0 / 64 / 64 | 0 / 64 | 64 / 64 | 0 / 53078 / 53081 | 53081 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 64 | 64 / 64 | 0 / 87184 / 0 | 4608 | 0 |
| 3 | row | 64 / 0 / 64 | 64 / 64 | 128 / 128 | 52197 / 52197 / 0 | 52197 | 0 |
| 3 | cached_row | 0 / 64 / 64 | 0 / 64 | 64 / 64 | 0 / 53083 / 53083 | 53083 | 0 |

## burst_64 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 64; plaintext bytes: 32768000; wire bytes: 32773888.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 156.960 | 407.7 | 199.10 | 3237.455 / 3362.979 / 3362.979 |
| 1 | 1 | cached_row | 149.185 | 429.0 | 209.47 | 3383.657 / 4615.088 / 4615.088 |
| 1 | 2 | snapshot | 144.446 | 443.1 | 216.34 | 3192.642 / 3484.835 / 3484.835 |
| 2 | 0 | cached_row | 160.146 | 399.6 | 195.13 | 3598.837 / 3965.580 / 3965.580 |
| 2 | 1 | snapshot | 156.357 | 409.3 | 199.86 | 3763.905 / 4455.842 / 4455.842 |
| 2 | 2 | row | 157.423 | 406.5 | 198.51 | 3832.863 / 3957.445 / 3957.445 |
| 3 | 0 | snapshot | 157.125 | 407.3 | 198.89 | 3612.453 / 6285.928 / 6285.928 |
| 3 | 1 | row | 168.564 | 379.7 | 185.39 | 4256.822 / 6312.317 / 6312.317 |
| 3 | 2 | cached_row | 151.324 | 422.9 | 206.51 | 3352.259 / 3716.867 / 3716.867 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.920 | 0.968 | 1.052 |
| 2 | 0.993 | 0.976 | 0.983 |
| 3 | 0.932 | 1.038 | 1.114 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.932 | 0.920 | 0.993 | 3 |
| snapshot_over_cached_row | 0.976 | 0.968 | 1.038 | 3 |
| row_over_cached_row | 1.052 | 0.983 | 1.114 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 64 | 64 / 64 | 0 / 87328 / 0 | 4608 | 0 |
| 1 | row | 64 / 0 / 64 | 64 / 64 | 128 / 128 | 52546 / 52551 / 0 | 52546 | 0 |
| 1 | cached_row | 0 / 64 / 64 | 0 / 64 | 64 / 64 | 0 / 53159 / 53162 | 53162 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 64 | 64 / 64 | 0 / 86774 / 0 | 4608 | 0 |
| 2 | row | 64 / 0 / 64 | 64 / 64 | 128 / 128 | 52036 / 52036 / 0 | 52036 | 0 |
| 2 | cached_row | 0 / 64 / 64 | 0 / 64 | 64 / 64 | 0 / 52495 / 52500 | 52500 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 64 | 64 / 64 | 0 / 86636 / 0 | 4608 | 0 |
| 3 | row | 64 / 0 / 64 | 64 / 64 | 128 / 128 | 52404 / 52409 / 0 | 52404 | 0 |
| 3 | cached_row | 0 / 64 / 64 | 0 / 64 | 64 / 64 | 0 / 52931 / 52941 | 52941 | 0 |

## burst_256 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 256; plaintext bytes: 131072000; wire bytes: 131095552.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 678.919 | 377.1 | 184.12 | 3521.684 / 3986.619 / 4437.979 |
| 1 | 1 | cached_row | 782.986 | 327.0 | 159.65 | 4988.463 / 9788.236 / 11255.537 |
| 1 | 2 | snapshot | 872.358 | 293.5 | 143.29 | 4989.556 / 9286.723 / 13979.065 |
| 2 | 0 | cached_row | 688.137 | 372.0 | 181.65 | 4511.697 / 5465.051 / 5873.681 |
| 2 | 1 | snapshot | 656.480 | 390.0 | 190.41 | 3650.624 / 6003.813 / 8518.573 |
| 2 | 2 | row | 685.340 | 373.5 | 182.39 | 3609.487 / 4456.553 / 5723.481 |
| 3 | 0 | snapshot | 637.400 | 401.6 | 196.11 | 3460.029 / 3763.023 / 3863.139 |
| 3 | 1 | row | 671.424 | 381.3 | 186.17 | 4018.108 / 4920.838 / 5526.986 |
| 3 | 2 | cached_row | 654.079 | 391.4 | 191.11 | 3718.080 / 4906.451 / 6580.526 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.285 | 1.114 | 0.867 |
| 2 | 0.958 | 0.954 | 0.996 |
| 3 | 0.949 | 0.975 | 1.027 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.958 | 0.949 | 1.285 | 3 |
| snapshot_over_cached_row | 0.975 | 0.954 | 1.114 | 3 |
| row_over_cached_row | 0.996 | 0.867 | 1.027 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 256 | 256 / 256 | 0 / 347948 / 0 | 18432 | 0 |
| 1 | row | 256 / 0 / 256 | 256 / 256 | 512 / 512 | 211475 / 211471 / 0 | 211475 | 0 |
| 1 | cached_row | 0 / 256 / 256 | 0 / 256 | 256 / 256 | 0 / 211184 / 211180 | 211180 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 256 | 256 / 256 | 0 / 348726 / 0 | 18432 | 0 |
| 2 | row | 256 / 0 / 256 | 256 / 256 | 512 / 512 | 208476 / 208475 / 0 | 208476 | 0 |
| 2 | cached_row | 0 / 256 / 256 | 0 / 256 | 256 / 256 | 0 / 211139 / 211135 | 211135 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 256 | 256 / 256 | 0 / 346497 / 0 | 18432 | 0 |
| 3 | row | 256 / 0 / 256 | 256 / 256 | 512 / 512 | 209971 / 209968 / 0 | 209971 | 0 |
| 3 | cached_row | 0 / 256 / 256 | 0 / 256 | 256 / 256 | 0 / 210010 / 210012 | 210012 | 0 |

## burst_256 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 256; plaintext bytes: 131072000; wire bytes: 131095552.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 846.636 | 302.4 | 147.64 | 5405.741 / 7474.470 / 8836.495 |
| 1 | 1 | snapshot | 556.573 | 460.0 | 224.59 | 3005.553 / 3111.430 / 3204.053 |
| 1 | 2 | row | 637.281 | 401.7 | 196.15 | 3477.291 / 6531.866 / 9286.733 |
| 2 | 0 | snapshot | 580.967 | 440.6 | 215.16 | 3138.480 / 4840.458 / 6024.692 |
| 2 | 1 | row | 856.233 | 299.0 | 145.99 | 4462.104 / 5512.128 / 5857.110 |
| 2 | 2 | cached_row | 869.275 | 294.5 | 143.80 | 4676.824 / 9407.718 / 13207.369 |
| 3 | 0 | row | 633.710 | 404.0 | 197.25 | 3656.615 / 4559.506 / 7102.769 |
| 3 | 1 | cached_row | 645.621 | 396.5 | 193.61 | 4098.788 / 5758.727 / 6189.850 |
| 3 | 2 | snapshot | 568.048 | 450.7 | 220.05 | 3222.728 / 3700.126 / 6649.515 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.873 | 0.657 | 0.753 |
| 2 | 0.679 | 0.668 | 0.985 |
| 3 | 0.896 | 0.880 | 0.982 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.873 | 0.679 | 0.896 | 3 |
| snapshot_over_cached_row | 0.668 | 0.657 | 0.880 | 3 |
| row_over_cached_row | 0.982 | 0.753 | 0.985 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 256 | 256 / 256 | 0 / 347417 / 0 | 18432 | 0 |
| 1 | row | 256 / 0 / 256 | 256 / 256 | 512 / 512 | 209313 / 209311 / 0 | 209313 | 0 |
| 1 | cached_row | 0 / 256 / 256 | 0 / 256 | 256 / 256 | 0 / 213805 / 213797 | 213797 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 256 | 256 / 256 | 0 / 346847 / 0 | 18432 | 0 |
| 2 | row | 256 / 0 / 256 | 256 / 256 | 512 / 512 | 207887 / 207883 / 0 | 207887 | 0 |
| 2 | cached_row | 0 / 256 / 256 | 0 / 256 | 256 / 256 | 0 / 210921 / 210919 | 210919 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 256 | 256 / 256 | 0 / 345665 / 0 | 18432 | 0 |
| 3 | row | 256 / 0 / 256 | 256 / 256 | 512 / 512 | 209091 / 209091 / 0 | 209091 | 0 |
| 3 | cached_row | 0 / 256 / 256 | 0 / 256 | 256 / 256 | 0 / 211209 / 211206 | 211206 | 0 |

## burst_512 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 512; plaintext bytes: 262144000; wire bytes: 262191104.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 1515.848 | 337.8 | 164.92 | 4465.750 / 5220.776 / 9323.592 |
| 1 | 1 | snapshot | 1611.091 | 317.8 | 155.17 | 4528.197 / 6818.049 / 9914.541 |
| 1 | 2 | row | 1348.428 | 379.7 | 185.40 | 3416.518 / 4662.126 / 7446.257 |
| 2 | 0 | snapshot | 1593.827 | 321.2 | 156.86 | 4886.644 / 6050.280 / 12446.072 |
| 2 | 1 | row | 1533.175 | 333.9 | 163.06 | 4528.848 / 5837.954 / 14358.592 |
| 2 | 2 | cached_row | 1302.176 | 393.2 | 191.99 | 3636.838 / 5540.801 / 6603.439 |
| 3 | 0 | row | 1362.703 | 375.7 | 183.46 | 3861.767 / 5039.909 / 6156.197 |
| 3 | 1 | cached_row | 1433.200 | 357.2 | 174.43 | 4405.709 / 6330.071 / 7412.565 |
| 3 | 2 | snapshot | 1264.683 | 404.8 | 197.68 | 3418.993 / 4267.882 / 7105.403 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.195 | 1.063 | 0.890 |
| 2 | 1.040 | 1.224 | 1.177 |
| 3 | 0.928 | 0.882 | 0.951 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.040 | 0.928 | 1.195 | 3 |
| snapshot_over_cached_row | 1.063 | 0.882 | 1.224 | 3 |
| row_over_cached_row | 0.951 | 0.890 | 1.177 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 512 | 512 / 512 | 0 / 695913 / 0 | 36864 | 0 |
| 1 | row | 512 / 0 / 512 | 512 / 512 | 1024 / 1024 | 422087 / 422093 / 0 | 422087 | 0 |
| 1 | cached_row | 0 / 512 / 512 | 0 / 512 | 512 / 512 | 0 / 426683 / 426693 | 426693 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 512 | 512 / 512 | 0 / 696565 / 0 | 36864 | 0 |
| 2 | row | 512 / 0 / 512 | 512 / 512 | 1024 / 1024 | 414891 / 414896 / 0 | 414891 | 0 |
| 2 | cached_row | 0 / 512 / 512 | 0 / 512 | 512 / 512 | 0 / 423043 / 423044 | 423044 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 512 | 512 / 512 | 0 / 695392 / 0 | 36864 | 0 |
| 3 | row | 512 / 0 / 512 | 512 / 512 | 1024 / 1024 | 419872 / 419878 / 0 | 419872 | 0 |
| 3 | cached_row | 0 / 512 / 512 | 0 / 512 | 512 / 512 | 0 / 421618 / 421616 | 421616 | 0 |

## burst_512 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 512; plaintext bytes: 262144000; wire bytes: 262191104.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 1614.726 | 317.1 | 154.83 | 4459.589 / 6559.848 / 9274.731 |
| 1 | 1 | row | 1927.679 | 265.6 | 129.69 | 4944.773 / 6940.636 / 11848.861 |
| 1 | 2 | cached_row | 1857.562 | 275.6 | 134.59 | 5811.715 / 6989.458 / 10709.039 |
| 2 | 0 | row | 1362.473 | 375.8 | 183.49 | 4265.157 / 5738.850 / 7130.219 |
| 2 | 1 | cached_row | 1169.459 | 437.8 | 213.77 | 3209.292 / 4244.839 / 7075.297 |
| 2 | 2 | snapshot | 1226.597 | 417.4 | 203.82 | 3972.833 / 5944.142 / 6998.173 |
| 3 | 0 | cached_row | 1160.032 | 441.4 | 215.51 | 3263.754 / 4366.697 / 6383.340 |
| 3 | 1 | snapshot | 1235.273 | 414.5 | 202.38 | 3943.579 / 4814.790 / 5950.905 |
| 3 | 2 | row | 1632.565 | 313.6 | 153.13 | 4477.533 / 6482.294 / 11800.871 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.838 | 0.869 | 1.038 |
| 2 | 0.900 | 1.049 | 1.165 |
| 3 | 0.757 | 1.065 | 1.407 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.838 | 0.757 | 0.900 | 3 |
| snapshot_over_cached_row | 1.049 | 0.869 | 1.065 | 3 |
| row_over_cached_row | 1.165 | 1.038 | 1.407 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 0 / 512 | 512 / 512 | 0 / 698955 / 0 | 36864 | 0 |
| 1 | row | 512 / 0 / 512 | 512 / 512 | 1024 / 1024 | 421495 / 421485 / 0 | 421495 | 0 |
| 1 | cached_row | 0 / 512 / 512 | 0 / 512 | 512 / 512 | 0 / 422487 / 422492 | 422492 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 0 / 512 | 512 / 512 | 0 / 696522 / 0 | 36864 | 0 |
| 2 | row | 512 / 0 / 512 | 512 / 512 | 1024 / 1024 | 418255 / 418265 / 0 | 418255 | 0 |
| 2 | cached_row | 0 / 512 / 512 | 0 / 512 | 512 / 512 | 0 / 421395 / 421398 | 421398 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 0 / 512 | 512 / 512 | 0 / 694950 / 0 | 36864 | 0 |
| 3 | row | 512 / 0 / 512 | 512 / 512 | 1024 / 1024 | 421011 / 421008 / 0 | 421011 | 0 |
| 3 | cached_row | 0 / 512 / 512 | 0 / 512 | 512 / 512 | 0 / 423421 / 423417 | 423417 | 0 |

