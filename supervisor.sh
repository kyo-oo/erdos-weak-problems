#!/bin/bash
# SUPERVISOR: run engines in supervised foreground chunks (sandbox kills background procs)
cd /home/z/erdos-weak-problems/problem142-ap-free/experiments
for i in $(seq 1 40); do
  timeout 480 /home/z/.venv/bin/python3 extend_rk.py >> extend_rk2.log 2>&1
  RC=$?
  if grep -q "EXTENSION COMPLETE" extend_rk2.log; then echo "142-DONE"; break; fi
  if [ $RC -eq 0 ]; then echo "142-DONE (rc=0)"; break; fi
  echo "chunk $i done (rc=$RC), resuming..."
  sleep 1
done
cd /home/z/erdos-weak-problems/problem107-happy-ending/experiments
for i in $(seq 1 12); do
  timeout 480 /home/z/.venv/bin/python3 witness_engine.py >> witness_engine.log 2>&1
  RC=$?
  if grep -q "WROTE witnesses.json" witness_engine.log && grep -c "certified" witness_engine.log > /dev/null; then
    if python3 -c "
import json,sys
d=json.load(open('witnesses.json'))
sys.exit(0 if d.get('E6') or 'E6' in d else 1)" 2>/dev/null; then echo "107-DONE"; break; fi
  fi
  if [ $RC -eq 0 ]; then
    if python3 -c "
import json,sys
d=json.load(open('witnesses.json'))
sys.exit(0 if d.get('E6') else 1)" 2>/dev/null; then echo "107-DONE (rc=0)"; break; fi
  fi
  echo "107 chunk $i done (rc=$RC), resuming..."
  sleep 1
done
echo "SUPERVISOR COMPLETE"
