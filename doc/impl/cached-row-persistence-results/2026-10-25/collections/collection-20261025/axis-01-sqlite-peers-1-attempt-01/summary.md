# Native persistence benchmark report

Input: `/tmp/bc-arc-scratch/row-persistence-20261025/hybrid/collection-20261025/axis-01-sqlite-peers-1-attempt-01/report.json`

Input SHA-256: `6ae114205a22becdfda3a29ba46caeb93e82f78eaa5d8f960409fa860fbba9be`

Backend: **sqlite**. Ratios divide paired batch durations; above 1 means the denominator arm finished sooner. Latencies remain per trial, never pooled. Logical bytes and query exchanges are not physical I/O or network packet counts. Application request/result journaling and provider transport are excluded.

## small_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 1048576; wire bytes: 1140494.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 6789.652 | 150.8 | 0.15 | 9343.949 / 13704.744 / 18555.792 |
| 1 | 1 | row | 6255.848 | 163.7 | 0.16 | 8347.274 / 10851.365 / 13805.913 |
| 1 | 2 | cached_row | 6158.338 | 166.3 | 0.16 | 7930.689 / 10199.371 / 12634.283 |
| 2 | 0 | row | 6402.469 | 159.9 | 0.16 | 8653.253 / 11430.252 / 16668.109 |
| 2 | 1 | cached_row | 6203.296 | 165.1 | 0.16 | 7920.611 / 10901.367 / 19514.286 |
| 2 | 2 | snapshot | 6434.317 | 159.1 | 0.16 | 9022.942 / 12050.145 / 16003.763 |
| 3 | 0 | cached_row | 6844.364 | 149.6 | 0.15 | 9301.400 / 13023.998 / 20425.482 |
| 3 | 1 | snapshot | 6752.235 | 151.7 | 0.15 | 9494.088 / 13435.564 / 18244.613 |
| 3 | 2 | row | 6426.313 | 159.3 | 0.16 | 8583.934 / 11525.719 / 15798.351 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.085 | 1.103 | 1.016 |
| 2 | 1.005 | 1.037 | 1.032 |
| 3 | 1.051 | 0.987 | 0.939 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.051 | 1.005 | 1.085 | 3 |
| snapshot_over_cached_row | 1.037 | 0.987 | 1.103 | 3 |
| row_over_cached_row | 1.016 | 0.939 | 1.032 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1386748 / 0 | 0 | 73728 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 841977 / 841981 / 0 | 841977 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 836718 / 836720 | 836720 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1386910 / 0 | 0 | 73728 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 838653 / 838654 / 0 | 838653 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 846043 / 846045 | 846045 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1384657 / 0 | 0 | 73728 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 843908 / 843916 / 0 | 843908 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 840961 / 840966 | 840966 | 0 |

## small_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 1048576; wire bytes: 1140492.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 6139.378 | 166.8 | 0.16 | 7846.222 / 10082.994 / 21496.315 |
| 1 | 1 | cached_row | 6694.566 | 153.0 | 0.15 | 8871.119 / 11816.811 / 20245.126 |
| 1 | 2 | snapshot | 6004.330 | 170.5 | 0.17 | 7303.312 / 10588.314 / 15719.193 |
| 2 | 0 | cached_row | 7233.370 | 141.6 | 0.14 | 11885.198 / 16034.911 / 19047.267 |
| 2 | 1 | snapshot | 6843.117 | 149.6 | 0.15 | 10873.014 / 13632.550 / 16483.566 |
| 2 | 2 | row | 6557.705 | 156.2 | 0.15 | 10015.149 / 13402.753 / 17086.187 |
| 3 | 0 | snapshot | 6291.718 | 162.8 | 0.16 | 8521.278 / 11895.407 / 18950.317 |
| 3 | 1 | row | 7234.348 | 141.5 | 0.14 | 10089.116 / 13492.800 / 17637.393 |
| 3 | 2 | cached_row | 6815.511 | 150.2 | 0.15 | 9636.473 / 14445.243 / 26404.258 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.978 | 0.897 | 0.917 |
| 2 | 1.044 | 0.946 | 0.907 |
| 3 | 0.870 | 0.923 | 1.061 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.978 | 0.870 | 1.044 | 3 |
| snapshot_over_cached_row | 0.923 | 0.897 | 0.946 | 3 |
| row_over_cached_row | 0.917 | 0.907 | 1.061 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1385672 / 0 | 0 | 73728 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 850170 / 850171 / 0 | 850170 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 833675 / 833674 | 833674 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1396964 / 0 | 0 | 73728 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 843121 / 843129 / 0 | 843121 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 847109 / 847106 | 847106 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1386734 / 0 | 0 | 73728 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 845056 / 845053 / 0 | 845056 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 836791 / 836786 | 836786 | 0 |

## large_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 128; plaintext bytes: 8388608; wire bytes: 8400384.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 933.596 | 137.1 | 8.57 | 9291.111 / 16512.550 / 16516.768 |
| 1 | 1 | cached_row | 1023.830 | 125.0 | 7.81 | 11093.855 / 15646.268 / 17448.061 |
| 1 | 2 | snapshot | 1036.560 | 123.5 | 7.72 | 12486.707 / 14820.441 / 16578.603 |
| 2 | 0 | cached_row | 765.077 | 167.3 | 10.46 | 7202.453 / 11194.663 / 12013.166 |
| 2 | 1 | snapshot | 748.429 | 171.0 | 10.69 | 7017.500 / 10016.781 / 11355.713 |
| 2 | 2 | row | 745.508 | 171.7 | 10.73 | 6416.942 / 11037.691 / 11098.685 |
| 3 | 0 | snapshot | 1001.158 | 127.9 | 7.99 | 11600.398 / 14615.970 / 15347.862 |
| 3 | 1 | row | 893.063 | 143.3 | 8.96 | 10495.351 / 11924.231 / 14738.688 |
| 3 | 2 | cached_row | 738.968 | 173.2 | 10.83 | 6931.119 / 8301.779 / 11014.839 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.110 | 1.012 | 0.912 |
| 2 | 1.004 | 0.978 | 0.974 |
| 3 | 1.121 | 1.355 | 1.209 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.110 | 1.004 | 1.121 | 3 |
| snapshot_over_cached_row | 1.012 | 0.978 | 1.355 | 3 |
| row_over_cached_row | 0.974 | 0.912 | 1.209 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 172619 / 0 | 0 | 9216 |
| 1 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 105533 / 105533 / 0 | 105533 | 0 |
| 1 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 104825 / 104823 | 104823 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 175168 / 0 | 0 | 9216 |
| 2 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 106000 / 106005 / 0 | 106000 | 0 |
| 2 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 106268 / 106269 | 106269 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 173264 / 0 | 0 | 9216 |
| 3 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 105231 / 105223 / 0 | 105231 | 0 |
| 3 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 105829 / 105818 | 105818 | 0 |

## large_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 128; plaintext bytes: 8388608; wire bytes: 8400384.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 1070.617 | 119.6 | 7.47 | 13128.882 / 16721.970 / 19305.688 |
| 1 | 1 | snapshot | 1020.093 | 125.5 | 7.84 | 10575.611 / 15215.806 / 16908.987 |
| 1 | 2 | row | 1124.209 | 113.9 | 7.12 | 15481.160 / 18999.308 / 20449.096 |
| 2 | 0 | snapshot | 784.390 | 163.2 | 10.20 | 9079.466 / 12260.798 / 12821.020 |
| 2 | 1 | row | 843.658 | 151.7 | 9.48 | 10154.186 / 11679.826 / 13318.185 |
| 2 | 2 | cached_row | 795.332 | 160.9 | 10.06 | 7736.137 / 12168.546 / 13689.807 |
| 3 | 0 | row | 749.748 | 170.7 | 10.67 | 6941.427 / 9392.129 / 11222.375 |
| 3 | 1 | cached_row | 868.489 | 147.4 | 9.21 | 10942.123 / 13652.678 / 14297.027 |
| 3 | 2 | snapshot | 948.740 | 134.9 | 8.43 | 11454.336 / 13934.512 / 19118.991 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.907 | 0.953 | 1.050 |
| 2 | 0.930 | 0.986 | 1.061 |
| 3 | 1.265 | 1.092 | 0.863 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.930 | 0.907 | 1.265 | 3 |
| snapshot_over_cached_row | 0.986 | 0.953 | 1.092 | 3 |
| row_over_cached_row | 1.050 | 0.863 | 1.061 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 173611 / 0 | 0 | 9216 |
| 1 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 106502 / 106508 / 0 | 106502 | 0 |
| 1 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 104634 / 104628 | 104628 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 174918 / 0 | 0 | 9216 |
| 2 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 106130 / 106131 / 0 | 106130 | 0 |
| 2 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 105900 / 105901 | 105901 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 128 / 0 | 512 / 0 | 0 / 172719 / 0 | 0 | 9216 |
| 3 | row | 128 / 0 / 128 | 128 / 128 | 640 / 0 | 104765 / 104766 / 0 | 104765 | 0 |
| 3 | cached_row | 0 / 128 / 128 | 0 / 128 | 512 / 0 | 0 / 106130 / 106130 | 106130 | 0 |

## mixed_stream / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 5177344; wire bytes: 5269632.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 6111.147 | 167.6 | 0.81 | 8002.613 / 10901.367 / 15408.315 |
| 1 | 1 | snapshot | 8058.437 | 127.1 | 0.61 | 11328.292 / 16370.595 / 23278.381 |
| 1 | 2 | row | 7266.229 | 140.9 | 0.68 | 10469.023 / 14974.728 / 22729.740 |
| 2 | 0 | snapshot | 6490.834 | 157.8 | 0.76 | 8852.174 / 13521.824 / 18714.498 |
| 2 | 1 | row | 6293.379 | 162.7 | 0.78 | 8493.706 / 11392.672 / 15960.042 |
| 2 | 2 | cached_row | 6212.737 | 164.8 | 0.79 | 8231.669 / 12036.510 / 19287.454 |
| 3 | 0 | row | 6645.493 | 154.1 | 0.74 | 9250.535 / 13120.187 / 18484.409 |
| 3 | 1 | cached_row | 6566.854 | 155.9 | 0.75 | 9432.604 / 11949.538 / 17643.394 |
| 3 | 2 | snapshot | 6593.333 | 155.3 | 0.75 | 9498.306 / 12982.440 / 19867.744 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.109 | 1.319 | 1.189 |
| 2 | 1.031 | 1.045 | 1.013 |
| 3 | 0.992 | 1.004 | 1.012 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.031 | 0.992 | 1.109 | 3 |
| snapshot_over_cached_row | 1.045 | 1.004 | 1.319 | 3 |
| row_over_cached_row | 1.013 | 1.012 | 1.189 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1386850 / 0 | 0 | 73728 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 850357 / 850347 / 0 | 850357 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 845061 / 845060 | 845060 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1395847 / 0 | 0 | 73728 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 849023 / 849022 / 0 | 849023 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 849289 / 849292 | 849292 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1386832 / 0 | 0 | 73728 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 843111 / 843117 / 0 | 843111 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 847203 / 847207 | 847207 | 0 |

## mixed_stream / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 1024; plaintext bytes: 5177344; wire bytes: 5269632.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 7070.790 | 144.8 | 0.70 | 10896.960 / 14098.918 / 19761.837 |
| 1 | 1 | row | 6691.082 | 153.0 | 0.74 | 10324.093 / 15291.076 / 24404.427 |
| 1 | 2 | cached_row | 6651.459 | 154.0 | 0.74 | 9614.653 / 14101.152 / 22728.317 |
| 2 | 0 | row | 6562.821 | 156.0 | 0.75 | 9179.002 / 11972.541 / 18108.150 |
| 2 | 1 | cached_row | 6042.000 | 169.5 | 0.82 | 7353.264 / 10357.696 / 17700.741 |
| 2 | 2 | snapshot | 6460.129 | 158.5 | 0.76 | 8597.299 / 12917.019 / 17916.022 |
| 3 | 0 | cached_row | 6160.150 | 166.2 | 0.80 | 7993.316 / 11446.181 / 16225.726 |
| 3 | 1 | snapshot | 6224.069 | 164.5 | 0.79 | 8128.256 / 11305.048 / 13898.766 |
| 3 | 2 | row | 6353.796 | 161.2 | 0.78 | 8902.568 / 13576.866 / 22133.530 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.057 | 1.063 | 1.006 |
| 2 | 0.984 | 1.069 | 1.086 |
| 3 | 0.980 | 1.010 | 1.031 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.984 | 0.980 | 1.057 | 3 |
| snapshot_over_cached_row | 1.063 | 1.010 | 1.069 | 3 |
| row_over_cached_row | 1.031 | 1.006 | 1.086 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1386795 / 0 | 0 | 73728 |
| 1 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 841073 / 841071 / 0 | 841073 | 0 |
| 1 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 838069 / 838075 | 838075 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1391937 / 0 | 0 | 73728 |
| 2 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 848122 / 848119 / 0 | 848122 | 0 |
| 2 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 844112 / 844111 | 844111 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 1024 / 0 | 4096 / 0 | 0 / 1381544 / 0 | 0 | 73728 |
| 3 | row | 1024 / 0 / 1024 | 1024 / 1024 | 5120 / 0 | 844072 / 844078 / 0 | 844072 | 0 |
| 3 | cached_row | 0 / 1024 / 1024 | 0 / 1024 | 4096 / 0 | 0 / 844905 / 844905 | 844905 | 0 |

## burst_64 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 64; plaintext bytes: 32768000; wire bytes: 32773888.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 429.026 | 149.2 | 72.84 | 9026.638 / 11712.397 / 11712.397 |
| 1 | 1 | row | 426.913 | 149.9 | 73.20 | 8727.893 / 11836.077 / 11836.077 |
| 1 | 2 | cached_row | 567.655 | 112.7 | 55.05 | 11472.340 / 15642.691 / 15642.691 |
| 2 | 0 | row | 443.055 | 144.5 | 70.53 | 8053.337 / 14889.118 / 14889.118 |
| 2 | 1 | cached_row | 444.215 | 144.1 | 70.35 | 9347.696 / 13706.468 / 13706.468 |
| 2 | 2 | snapshot | 440.502 | 145.3 | 70.94 | 9178.732 / 12086.523 / 12086.523 |
| 3 | 0 | cached_row | 481.415 | 132.9 | 64.91 | 9356.202 / 13436.506 / 13436.506 |
| 3 | 1 | snapshot | 500.413 | 127.9 | 62.45 | 11158.676 / 14018.418 / 14018.418 |
| 3 | 2 | row | 463.839 | 138.0 | 67.37 | 9168.933 / 13882.265 / 13882.265 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.005 | 0.756 | 0.752 |
| 2 | 0.994 | 0.992 | 0.997 |
| 3 | 1.079 | 1.039 | 0.963 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.005 | 0.994 | 1.079 | 3 |
| snapshot_over_cached_row | 0.992 | 0.756 | 1.039 | 3 |
| row_over_cached_row | 0.963 | 0.752 | 0.997 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 86521 / 0 | 0 | 4608 |
| 1 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 52940 / 52942 / 0 | 52940 | 0 |
| 1 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52413 / 52406 | 52406 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 87512 / 0 | 0 | 4608 |
| 2 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 52803 / 52808 / 0 | 52803 | 0 |
| 2 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 53143 / 53138 | 53138 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 86551 / 0 | 0 | 4608 |
| 3 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 53084 / 53081 / 0 | 53084 | 0 |
| 3 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52959 / 52959 | 52959 | 0 |

## burst_64 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 64; plaintext bytes: 32768000; wire bytes: 32773888.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 565.666 | 113.1 | 55.24 | 11542.991 / 16630.228 / 16630.228 |
| 1 | 1 | cached_row | 567.603 | 112.8 | 55.06 | 13408.133 / 20188.441 / 20188.441 |
| 1 | 2 | snapshot | 576.108 | 111.1 | 54.24 | 13442.847 / 16186.713 / 16186.713 |
| 2 | 0 | cached_row | 437.035 | 146.4 | 71.50 | 10797.003 / 12561.737 / 12561.737 |
| 2 | 1 | snapshot | 469.589 | 136.3 | 66.55 | 10613.431 / 13571.948 / 13571.948 |
| 2 | 2 | row | 475.040 | 134.7 | 65.78 | 9235.507 / 15410.459 / 15410.459 |
| 3 | 0 | snapshot | 429.172 | 149.1 | 72.81 | 8992.435 / 12843.713 / 12843.713 |
| 3 | 1 | row | 425.548 | 150.4 | 73.43 | 7619.209 / 11951.481 / 11951.481 |
| 3 | 2 | cached_row | 437.805 | 146.2 | 71.38 | 8209.437 / 12964.126 / 12964.126 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.018 | 1.015 | 0.997 |
| 2 | 0.989 | 1.074 | 1.087 |
| 3 | 1.009 | 0.980 | 0.972 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.009 | 0.989 | 1.018 | 3 |
| snapshot_over_cached_row | 1.015 | 0.980 | 1.074 | 3 |
| row_over_cached_row | 0.997 | 0.972 | 1.087 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 86843 / 0 | 0 | 4608 |
| 1 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 52677 / 52674 / 0 | 52677 | 0 |
| 1 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52868 / 52865 | 52865 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 87857 / 0 | 0 | 4608 |
| 2 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 53330 / 53329 / 0 | 53330 | 0 |
| 2 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 53094 / 53096 | 53096 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 64 / 0 | 256 / 0 | 0 / 86472 / 0 | 0 | 4608 |
| 3 | row | 64 / 0 / 64 | 64 / 64 | 320 / 0 | 52566 / 52558 / 0 | 52566 | 0 |
| 3 | cached_row | 0 / 64 / 64 | 0 / 64 | 256 / 0 | 0 / 52853 / 52854 | 52854 | 0 |

## burst_256 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 256; plaintext bytes: 131072000; wire bytes: 131095552.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | row | 2763.865 | 92.6 | 45.23 | 19920.062 / 23328.074 / 28682.768 |
| 1 | 1 | cached_row | 1928.632 | 132.7 | 64.81 | 9627.667 / 13460.330 / 16782.081 |
| 1 | 2 | snapshot | 1781.511 | 143.7 | 70.17 | 8939.146 / 11951.341 / 13457.424 |
| 2 | 0 | cached_row | 1805.534 | 141.8 | 69.23 | 9182.739 / 14725.965 / 15856.850 |
| 2 | 1 | snapshot | 1746.612 | 146.6 | 71.57 | 8955.967 / 12333.172 / 13893.505 |
| 2 | 2 | row | 1903.950 | 134.5 | 65.65 | 10434.779 / 13450.171 / 18880.616 |
| 3 | 0 | snapshot | 1849.016 | 138.5 | 67.60 | 8697.807 / 10542.459 / 23302.005 |
| 3 | 1 | row | 1843.914 | 138.8 | 67.79 | 10335.274 / 13426.697 / 15527.988 |
| 3 | 2 | cached_row | 1725.454 | 148.4 | 72.44 | 8066.142 / 10920.332 / 13414.194 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.645 | 0.924 | 1.433 |
| 2 | 0.917 | 0.967 | 1.055 |
| 3 | 1.003 | 1.072 | 1.069 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.917 | 0.645 | 1.003 | 3 |
| snapshot_over_cached_row | 0.967 | 0.924 | 1.072 | 3 |
| row_over_cached_row | 1.069 | 1.055 | 1.433 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 347674 / 0 | 0 | 18432 |
| 1 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 211236 / 211241 / 0 | 211236 | 0 |
| 1 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 210496 / 210499 | 210499 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 350008 / 0 | 0 | 18432 |
| 2 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 211153 / 211142 / 0 | 211153 | 0 |
| 2 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 212041 / 212044 | 212044 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 344330 / 0 | 0 | 18432 |
| 3 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 210144 / 210145 / 0 | 210144 | 0 |
| 3 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 211538 / 211542 | 211542 | 0 |

## burst_256 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 256; plaintext bytes: 131072000; wire bytes: 131095552.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 1863.876 | 137.3 | 67.06 | 11962.031 / 15154.362 / 15920.749 |
| 1 | 1 | snapshot | 1781.378 | 143.7 | 70.17 | 8634.188 / 12882.224 / 15722.540 |
| 1 | 2 | row | 1654.237 | 154.8 | 75.56 | 8018.362 / 11691.258 / 13557.601 |
| 2 | 0 | snapshot | 2220.340 | 115.3 | 56.30 | 12724.260 / 15603.007 / 23765.137 |
| 2 | 1 | row | 2321.923 | 110.3 | 53.83 | 13299.651 / 17719.466 / 22839.053 |
| 2 | 2 | cached_row | 1659.191 | 154.3 | 75.34 | 8781.111 / 11104.395 / 16187.625 |
| 3 | 0 | row | 1737.963 | 147.3 | 71.92 | 9854.559 / 12765.697 / 17819.061 |
| 3 | 1 | cached_row | 1741.218 | 147.0 | 71.79 | 9067.885 / 11956.992 / 21494.962 |
| 3 | 2 | snapshot | 1592.784 | 160.7 | 78.48 | 7350.689 / 8359.818 / 12714.882 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.077 | 0.956 | 0.888 |
| 2 | 0.956 | 1.338 | 1.399 |
| 3 | 0.916 | 0.915 | 0.998 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.956 | 0.916 | 1.077 | 3 |
| snapshot_over_cached_row | 0.956 | 0.915 | 1.338 | 3 |
| row_over_cached_row | 0.998 | 0.888 | 1.399 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 345682 / 0 | 0 | 18432 |
| 1 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 211991 / 211994 / 0 | 211991 | 0 |
| 1 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 210626 / 210624 | 210624 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 350506 / 0 | 0 | 18432 |
| 2 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 210525 / 210526 / 0 | 210525 | 0 |
| 2 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 211516 / 211515 | 211515 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 256 / 0 | 1024 / 0 | 0 / 347255 / 0 | 0 | 18432 |
| 3 | row | 256 / 0 / 256 | 256 / 256 | 1280 / 0 | 210453 / 210454 / 0 | 210453 | 0 |
| 3 | cached_row | 0 / 256 / 256 | 0 / 256 | 1024 / 0 | 0 / 210262 / 210265 | 210265 | 0 |

## burst_512 / send / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 512; plaintext bytes: 262144000; wire bytes: 262191104.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | cached_row | 3653.394 | 140.1 | 68.43 | 9998.117 / 13611.631 / 15069.855 |
| 1 | 1 | snapshot | 3852.325 | 132.9 | 64.90 | 12701.307 / 14585.894 / 17248.229 |
| 1 | 2 | row | 3737.219 | 137.0 | 66.89 | 11332.329 / 13077.327 / 16600.093 |
| 2 | 0 | snapshot | 3436.677 | 149.0 | 72.74 | 8316.076 / 10922.567 / 16371.828 |
| 2 | 1 | row | 3416.936 | 149.8 | 73.16 | 8248.500 / 10574.239 / 13695.998 |
| 2 | 2 | cached_row | 3708.320 | 138.1 | 67.42 | 9563.758 / 12226.042 / 15098.489 |
| 3 | 0 | row | 3685.393 | 138.9 | 67.84 | 10662.843 / 17109.330 / 18887.430 |
| 3 | 1 | cached_row | 3458.566 | 148.0 | 72.28 | 8829.441 / 11065.714 / 15680.611 |
| 3 | 2 | snapshot | 3725.268 | 137.4 | 67.11 | 9716.713 / 12490.615 / 16833.467 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 1.031 | 1.054 | 1.023 |
| 2 | 1.006 | 0.927 | 0.921 |
| 3 | 1.011 | 1.077 | 1.066 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 1.011 | 1.006 | 1.031 | 3 |
| snapshot_over_cached_row | 1.054 | 0.927 | 1.077 | 3 |
| row_over_cached_row | 1.023 | 0.921 | 1.066 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 694382 / 0 | 0 | 36864 |
| 1 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 424060 / 424062 / 0 | 424060 | 0 |
| 1 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 421971 / 421969 | 421969 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 699552 / 0 | 0 | 36864 |
| 2 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 422927 / 422930 / 0 | 422927 | 0 |
| 2 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 424512 / 424515 | 424515 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 693305 / 0 | 0 | 36864 |
| 3 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 420988 / 420984 / 0 | 420988 | 0 |
| 3 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 421585 / 421579 | 421579 | 0 |

## burst_512 / receive / 1 peers

Eligible/touched peers: 1/1; consumed registrations: 1; messages: 512; plaintext bytes: 262144000; wire bytes: 262191104.

| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | snapshot | 3454.086 | 148.2 | 72.38 | 8977.568 / 11380.570 / 14041.691 |
| 1 | 1 | row | 4221.669 | 121.3 | 59.22 | 12956.742 / 15747.035 / 21079.078 |
| 1 | 2 | cached_row | 3871.588 | 132.2 | 64.57 | 10245.537 / 13720.664 / 18608.831 |
| 2 | 0 | row | 3532.682 | 144.9 | 70.77 | 9252.599 / 13997.288 / 15532.857 |
| 2 | 1 | cached_row | 3858.238 | 132.7 | 64.80 | 10416.455 / 13767.892 / 18817.099 |
| 2 | 2 | snapshot | 3609.024 | 141.9 | 69.27 | 9214.889 / 14542.032 / 16512.951 |
| 3 | 0 | cached_row | 3297.960 | 155.2 | 75.80 | 7993.135 / 10439.879 / 11991.075 |
| 3 | 1 | snapshot | 3365.832 | 152.1 | 74.28 | 8523.592 / 10648.748 / 14304.881 |
| 3 | 2 | row | 4303.092 | 119.0 | 58.10 | 12826.861 / 17675.274 / 23679.117 |

| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |
| ---: | ---: | ---: | ---: |
| 1 | 0.818 | 0.892 | 1.090 |
| 2 | 1.022 | 0.935 | 0.916 |
| 3 | 0.782 | 1.021 | 1.305 |

| Paired comparison | Median | Min | Max | Trials |
| --- | ---: | ---: | ---: | ---: |
| snapshot_over_row | 0.818 | 0.782 | 1.022 | 3 |
| snapshot_over_cached_row | 0.935 | 0.892 | 1.021 | 3 |
| row_over_cached_row | 1.090 | 0.916 | 1.305 | 3 |

| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 693337 / 0 | 0 | 36864 |
| 1 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 425243 / 425243 / 0 | 425243 | 0 |
| 1 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 422049 / 422056 | 422056 | 0 |
| 2 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 698564 / 0 | 0 | 36864 |
| 2 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 422555 / 422559 / 0 | 422555 | 0 |
| 2 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 421416 / 421415 | 421415 | 0 |
| 3 | snapshot | 0 / 0 / 0 | 512 / 0 | 2048 / 0 | 0 / 690307 / 0 | 0 | 36864 |
| 3 | row | 512 / 0 / 512 | 512 / 512 | 2560 / 0 | 418848 / 418849 / 0 | 418848 | 0 |
| 3 | cached_row | 0 / 512 / 512 | 0 / 512 | 2048 / 0 | 0 / 423512 / 423512 | 423512 | 0 |

