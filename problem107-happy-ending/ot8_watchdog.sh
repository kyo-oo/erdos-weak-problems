#!/bin/bash
# W76-107K ot8 watchdog: relaunch the wall-crossing enumeration if it dies.
cd "$(dirname "$0")"
for i in $(seq 1 40); do
  if ! pgrep -f "engine107f5v2.py --stage ot8" > /dev/null; then
    if [ -f engine107f5_cache/ot8.pkl ]; then
      echo "[watchdog] ot8.pkl exists — COMPLETE, exiting." >> ot8_watchdog.log
      exit 0
    fi
    echo "[watchdog] relaunch #$i at $(date)" >> ot8_watchdog.log
    nohup /home/z/.venv/bin/python3 engine107f5v2.py --stage ot8 >> ot8_v2_run.log 2>&1 &
  fi
  sleep 120
done
