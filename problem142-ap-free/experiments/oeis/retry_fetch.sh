#!/bin/bash
# Background OEIS b-file re-fetch: spaced polite retries, stops when a file is clean.
UA="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
for a in A003002 A003003 A003004 A003005; do
  if head -c 20 "b$a.txt" 2>/dev/null | grep -q "<" || [ ! -s "b$a.txt" ]; then
    for attempt in $(seq 1 12); do
      for u in "https://oeis.org/$a/b$a.txt" "https://oeis.org/$a/b$a.txt?fmt=text"; do
        curl -s -L --http1.1 -m 30 -A "$UA" -H "Accept: text/plain" "$u" -o "b$a.txt" 2>/dev/null
        if [ -s "b$a.txt" ] && ! head -c 20 "b$a.txt" | grep -q "<"; then echo "$(date +%T) $a OK attempt $attempt"; break 2; fi
      done
      sleep 45
    done
  fi
done
echo "$(date +%T) retry_fetch done"
