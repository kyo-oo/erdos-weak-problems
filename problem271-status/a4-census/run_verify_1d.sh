#!/bin/bash
# task 1-d: fresh independent verification of k=18,19,20 A4 member dumps
cd /home/z/erdos-weak-problems/problem271-status/a4-census || exit 1
rm -f run_1d_status.txt
for k in 18 19 20; do
  case $k in
    18) N=387420489;;    # 3^18
    19) N=1162261467;;   # 3^19
    20) N=3486784401;;   # 3^20
  esac
  start=$(date +%s)
  nice -n 10 timeout 900 ./bin_1d/verify_dump data/a4_members_3k${k}.txt 4 $N > verify_log_k${k}.txt 2>&1
  rc=$?
  end=$(date +%s)
  echo "k=$k rc=$rc wall=$((end-start))s N=$N" >> run_1d_status.txt
done
echo "ALLDONE $(date -u +%FT%TZ)" >> run_1d_status.txt
