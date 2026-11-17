// Exact GST Problem 406 research: zero-residue exclusion in BAD words.
// This is a FINITE MITM audit, not a universal proof.
//
// For an integer R with 0<R<3^L, R mod 3 =1, write ternary digits
// d_0=1,d_1,...,d_(L-1), padding with high zeros.
// The original x4 carry states are c_1=1 and transitions:
// c=0: (d,c')=(0,0),(1,1)
// c=1: (0,0),(1,1),(2,3)
// c=2: (0,0),(1,2),(2,3)
// c=3: (0,1),(1,2)
// This is exactly the no-common-2 language (p>=1).
//
// Given e=floor(4L/3)+1, enumerate all valid prefixes and suffixes.
// The suffix value S is in BASE 3 but starts at trit 0. A completed
// word is R=P+3^m S. Since 3^m is invertible modulo 2^e,
// R == 0 mod 2^e iff S == -P*(3^m)^(-1) mod 2^e.
// We enumerate EVERY admissible prefix and suffix; no random sampling.
// C++ unsigned arithmetic is exact: L<=36, e<=49, R<3^36<2^58.
//
// Length 9/10 has the known exceptional R=4^7; the scope here is
// L=11..36. Failure of a candidate zero-residue proof does not
// refute the original exact-power conjecture, but would refute the
// broader 4L/3 BAD-valuation barrier.
//
// Usage: c++ -O3 -std=c++17 scripts/gst_406_bad_zero_mitm.cpp -o audit
//        ./audit 36
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using U = std::uint64_t;

struct Move { unsigned digit, carry; };
static const std::vector<Move> moves[4] = {
  {{0,0},{1,1}},
  {{0,0},{1,1},{2,3}},
  {{0,0},{1,2},{2,3}},
  {{0,1},{1,2}}
};
struct Item {
  U residue, suffixValue;
  bool operator<(const Item& rhs) const { return residue < rhs.residue; }
};
static U powers3[37], bitMask;
static unsigned L, middle, exponent;
static std::vector<Item> suffixes[4];
static U prefixCount[4]={}, examined=0, witness=0;
static bool hasWitness=false;

static U inverseOddModPow2(U a) {
  // Newton/Hensel: a*x -> 1 modulo twice as many binary digits.
  U x=1;
  for(unsigned i=0;i<7;++i) x*=2-a*x; // 1,2,4,8,...,128 bits
  return x&bitMask;
}

static void enumerateSuffix(unsigned startCarry, unsigned pos,
                            unsigned carry, U value) {
  if(pos==L-middle) {
    suffixes[startCarry].push_back({value&bitMask,value});
    return;
  }
  for(const Move& m : moves[carry])
    enumerateSuffix(startCarry,pos+1,m.carry,value+m.digit*powers3[pos]);
}

static bool originalBad(U R) {
  U S=4*R;
  unsigned p=0;
  while(R>0) {
    if(p>=1 && R%3==2 && S%3==2) return false;
    R/=3;S/=3;++p;
  }
  return true;
}

static void enumeratePrefix(unsigned pos, unsigned carry,
                            U value, U inversePow3Middle) {
  if(hasWitness) return;
  if(pos==middle) {
    ++prefixCount[carry];
    U wanted = (U(0)-value)*inversePow3Middle & bitMask;
    auto& vec=suffixes[carry];
    auto it=std::lower_bound(vec.begin(),vec.end(),Item{wanted,0});
    if(it!=vec.end() && it->residue==wanted) {
      U R=value+powers3[middle]*it->suffixValue;
      if(!(R>0 && R<powers3[L] && R%3==1 &&
           (R&bitMask)==0 && originalBad(R))) {
        std::cerr<<"INTERNAL ERROR: matched residue violates direct BAD check\n";
        std::exit(3);
      }
      witness=R;
      hasWitness=true;
    }
    return;
  }
  for(const Move& m : moves[carry])
    enumeratePrefix(pos+1,m.carry,value+m.digit*powers3[pos],inversePow3Middle);
}

int main(int argc,char**argv) {
  if(argc!=2) { std::cerr<<"usage: audit L, where 11<=L<=36\n"; return 2; }
  L=unsigned(std::atoi(argv[1]));
  if(L<11||L>36) { std::cerr<<"L outside audited domain 11..36\n"; return 2; }
  exponent=(4*L)/3+1; middle=L/2;
  bitMask=(U(1)<<exponent)-1;
  powers3[0]=1;
  for(unsigned i=1;i<=L;++i) powers3[i]=3*powers3[i-1];

  for(unsigned c=0;c<4;++c) {
    enumerateSuffix(c,0,c,0);
    std::sort(suffixes[c].begin(),suffixes[c].end());
  }
  U inv=inverseOddModPow2(powers3[middle]);
  enumeratePrefix(1,1,1,inv);
  for(unsigned c=0;c<4;++c)
    examined+=prefixCount[c]*U(suffixes[c].size());

  std::cout<<"L="<<L<<" e="<<exponent
           <<" exact_BAD_words="<<examined
           <<" source_residue_zero="<<(hasWitness?1:0)
           <<" candidate="<<witness<<"\n";
  if(L==22 && examined!=226449920) {
    std::cerr<<"INTERNAL ERROR: BAD count differs from inherited exhaustive audit\n";
    return 4;
  }
  // A found source would require a mathematical interpretation and could
  // disprove this more general proposed barrier; never suppress it.
  return hasWitness ? 1:0;
}
