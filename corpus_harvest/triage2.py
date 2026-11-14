import re, json, os

def clean(s):
    s = re.sub(r'<script.*?</script>', ' ', s, flags=re.S)
    s = re.sub(r'<[^>]+>', ' ', s)          # strip tags FIRST
    s = html_unescape(s)
    s = re.sub(r'\s+', ' ', s)
    return s.strip()

def html_unescape(s):
    import html as H
    return H.unescape(s)

ATTACKED = set()
for d in os.listdir('/home/z/erdos-weak-problems'):
    m = re.match(r'problem(\d+)', d)
    if m: ATTACKED.add(int(m.group(1)))

OUT = set()
def add(*xs): OUT.update(xs)
def addrange(a,b): OUT.update(range(a,b+1))
add(508,188,212,1135,918,919,376,377,386,936,137,373,930,931,291,264,1049,1160,1159,849,1003,985)
addrange(1167,1221)
add(3,5,233,455,68,249,251,252,257,260,263,267,269,385,413,572,573,634,684,685,1095,805,942,952,1199,1206,495,276)
add(1113,940,1093,675,177,1188,1189,912,393,400,478,1094,278,293,295,301,302,304,311,313,319,327,450,693,886,887,893,945,975,1054,1100,470,9,11,28,33,40,66,870,881,1145,1192,1194,338,683,731,156,472,695,701,970,978,983,996,1151,256,1035,595,602,61,75,159,174,500,563,564,712,827,837,838)
add(422,456,913,1065,1059,1142,324,826,1055,1110,689,312,326,431,892,1101)

NEG = re.compile(r'infinitely many|infinitude|asymptotic|almost all|density|estimate|order of growth|\bo\(|\bO\(|\blim\b|limsup|liminf|converge|sufficiently large|for all large|for large|distribution|normal order|average order|Goldbach|twin prime|Riemann|Ramsey|hypergraph|chromatic|graph|measurable|entire function|polynomial|uniformly|arbitrarily (long|large)|unbounded|grows|to infinity|\\to|\\infty|\\\\to|sunflower|colouring|coloring|triangle-free|monochromatic|girth', re.I)
POS = re.compile(r'does there exist|is there|can one find|find the smallest|what is the smallest|the smallest|the least|find all|determine (all|the)|are there|how many|is it true that.{0,80}unique|is the sequence|does the sequence|is every|are all|must every', re.I)
NT = re.compile(r'prime|factorial|binomial|digit|divisor|gcd|lcm|power|square|cube|base \d|modulo|congruen|sum of|product|composite|coprime|divides|remainder|perfect|pell|smooth', re.I)

corpus = json.load(open('corpus_statements.json'))

fresh = []
for n, v in sorted(corpus.items(), key=lambda kv: int(kv[0])):
    n = int(n)
    if n in ATTACKED or n in OUT: continue
    s = v['stmt']
    if len(s) < 30: continue
    fresh.append((n, s))

print('FRESH pool:', len(fresh))
# gold: number-theory + existence/exact, no negatives
gold, silver = [], []
for n, s in fresh:
    neg = len(NEG.findall(s)); pos = len(POS.findall(s)); nt = len(NT.findall(s))
    if neg == 0 and pos >= 1 and nt >= 1: gold.append((n, s))
    elif neg == 0 and pos >= 1: silver.append((n, s))

print('\n=== GOLD (NT + existence/exact, zero-neg):', len(gold))
for n, s in gold:
    print(f'\n#{n}: {s[:500]}')

print('\n=== SILVER (existence, no-neg, non-NT):', len(silver))
for n, s in silver[:20]:
    print(f'#{n}: {s[:200]}')

# sharp short statements (any type) for manual review
print('\n=== SHORT-ASKS (<330 chars, fresh):')
shorts = [(n,s) for n,s in fresh if len(s) < 330]
print(len(shorts))
for n, s in shorts:
    print(f'#{n}: {s[:300]}')
