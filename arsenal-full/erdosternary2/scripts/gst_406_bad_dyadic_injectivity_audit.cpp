// GST Problem 406: complete finite BAD-word / dyadic-residue injection audit.
// USAGE: c++ -std=c++17 -O3 ... -o audit && ./audit L
// Tested 9<=L<=22. Finite evidence only: it does NOT prove the
// all-L binary-origin exclusion or universal CommonTwo.
// Source R has d_0=1, c_1=1. For j>=1, each BAD transition
// chooses trit d in {0,1,2} and carries the x4 state c.
// Forbid (d,c)=(2,0),(2,3). Every distinct (R,c) word is counted.
// The end-of-word state is irrelevant: d_j=0 thereafter, and
// no shared 2 can ever occur at a higher position.
//
// Exact calculations are unsigned 64-bit; 3^L fits for L<=22.
// Exhaustive one-bit residue bitmap: any repeated residue is an
// exact collision; zero counts exact potential high-v2 BAD words.
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
#include <utility>

struct Move { int trit; int carry; };
static const std::vector<Move> transitions[4] = {
    {{0,0},{1,1}}, {{0,0},{1,1},{2,3}},
    {{0,0},{1,2},{2,3}}, {{0,1},{1,2}}
};
static uint64_t powers3[24];
static std::vector<uint8_t> seen;
static int length=0, exponent=0;
static uint64_t mask=0, count=0, collisions=0, multiples=0, first_collision=0;

static void inspect(int p, int carry, uint64_t value) {
    if (p==length) {
        ++count;
        uint64_t residue = value & mask;
        uint64_t pos=residue >> 3;
        unsigned bit=static_cast<unsigned>(residue & 7u);
        if (seen[pos] & (1u<<bit)) {
            ++collisions;
            if (first_collision==0) first_collision=value;
        } else {
            seen[pos] |= static_cast<uint8_t>(1u<<bit);
        }
        if (residue==0) ++multiples;
        return;
    }
    for (const auto &m:transitions[carry]) {
        inspect(p+1,m.carry,value+static_cast<uint64_t>(m.trit)*powers3[p]);
    }
}

int main(int argc,char**argv) {
    if(argc!=2) {
        std::cerr << "Usage: bad_dyadic_injectivity_audit L (9<=L<=22)\n";
        return 2;
    }
    length=std::atoi(argv[1]);
    if(length<9 || length>22) {
        std::cerr<<"L must be 9..22 (exact bitmap resource contract)\n";
        return 2;
    }
    exponent=(3*length)/2+1;
    mask=(uint64_t(1)<<exponent)-1;
    powers3[0]=1;
    for(int j=1;j<=length;++j) powers3[j]=3*powers3[j-1];
    seen.resize((uint64_t(1)<<exponent)/8);
    inspect(1,1,1);
    std::cout<<"L="<<length<<" t="<<exponent
        <<" unit_BAD_words="<<count<<" collisions="<<collisions
        <<" residue_zero="<<multiples
        <<" first_collision="<<first_collision<<"\n";
    // Exact targeted source-specific crosschecks.
    if (length==9) return (count==1676 && collisions==0 && multiples==1)?0:1;
    if (length==18) return (count==5974880 && collisions==0 && multiples==0)?0:1;
    if (length==22) return (count==226449920 && collisions==0 && multiples==0)?0:1;
    // For other listed depths, assert modular injection and no zero:
    return (collisions==0 && multiples==0)?0:1;
}
