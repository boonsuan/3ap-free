// compile with g++ -O3 -std=c++17 3ap-free.cpp -o 3ap-free
#include <bits/stdc++.h>
using namespace std;

using u128 = __uint128_t;

// Reverse all 64 bits in x.
static inline uint64_t reverse64(uint64_t x) {
    x = ((x & 0x5555555555555555ULL) << 1)  | ((x >> 1)  & 0x5555555555555555ULL);
    x = ((x & 0x3333333333333333ULL) << 2)  | ((x >> 2)  & 0x3333333333333333ULL);
    x = ((x & 0x0F0F0F0F0F0F0F0FULL) << 4)  | ((x >> 4)  & 0x0F0F0F0F0F0F0F0FULL);
    x = ((x & 0x00FF00FF00FF00FFULL) << 8)  | ((x >> 8)  & 0x00FF00FF00FF00FFULL);
    x = ((x & 0x0000FFFF0000FFFFULL) << 16) | ((x >> 16) & 0x0000FFFF0000FFFFULL);
    x = (x << 32) | (x >> 32);
    return x;
}

static inline string to_string_u128(u128 x) {
    if (x == 0) return "0";
    string s;
    while (x > 0) {
        int digit = (int)(x % 10);
        s.push_back(char('0' + digit));
        x /= 10;
    }
    reverse(s.begin(), s.end());
    return s;
}

// A compact open-addressing hash map u128 -> u128.
// Much lower overhead than std::unordered_map for tens of millions of states.
struct FlatHashMap {
    static constexpr u128 EMPTY = (u128)(~(u128)0);

    vector<u128> keys;
    vector<u128> vals;
    size_t filled = 0;
    size_t capMask = 0;

    static inline uint64_t splitmix64(uint64_t x) {
        x += 0x9e3779b97f4a7c15ULL;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
        x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
        return x ^ (x >> 31);
    }

    static inline uint64_t hash_u128(u128 k) {
        uint64_t lo = (uint64_t)k;
        uint64_t hi = (uint64_t)(k >> 64);
        uint64_t h = lo ^ splitmix64(hi + 0x9e3779b97f4a7c15ULL);
        return splitmix64(h);
    }

    static size_t next_pow2(size_t x) {
        size_t p = 1;
        while (p < x) p <<= 1;
        return p;
    }

    explicit FlatHashMap(size_t initial_capacity = 1 << 20) {
        reinit(next_pow2(initial_capacity));
    }

    void reinit(size_t capacity) {
        keys.assign(capacity, EMPTY);
        vals.assign(capacity, 0);
        filled = 0;
        capMask = capacity - 1;
    }

    void rehash(size_t newCapacity) {
        vector<u128> oldK = move(keys);
        vector<u128> oldV = move(vals);
        reinit(next_pow2(newCapacity));
        for (size_t i = 0; i < oldK.size(); i++) {
            if (oldK[i] != EMPTY) set(oldK[i], oldV[i]);
        }
    }

    bool get(u128 key, u128 &out) const {
        size_t idx = (size_t)hash_u128(key) & capMask;
        while (true) {
            u128 k = keys[idx];
            if (k == EMPTY) return false;
            if (k == key) { out = vals[idx]; return true; }
            idx = (idx + 1) & capMask;
        }
    }

    void set(u128 key, u128 val) {
        // Rehash at ~70% load factor.
        if ((filled + 1) * 10 >= keys.size() * 7) {
            rehash(keys.size() * 2);
        }
        size_t idx = (size_t)hash_u128(key) & capMask;
        while (true) {
            if (keys[idx] == EMPTY) {
                keys[idx] = key;
                vals[idx] = val;
                filled++;
                return;
            }
            if (keys[idx] == key) {
                vals[idx] = val;
                return;
            }
            idx = (idx + 1) & capMask;
        }
    }
};

struct Solver {
    int N = 0;

    struct CenterInfo {
        int m;         // m = min(c, N-1-c)
        int leftShift; // shift to extract left segment
        int rightShift;// shift to extract right segment
        uint64_t segMask;
    };
    vector<CenterInfo> center;

    FlatHashMap memo;

    explicit Solver(int n) : N(n), center(n), memo(1 << 20) {
        for (int c = 0; c < N; c++) {
            int m = min(c, N - 1 - c);
            center[c].m = m;
            center[c].leftShift  = c - m;
            center[c].rightShift = c + 1;
            center[c].segMask = (m == 0) ? 0ULL : ((1ULL << m) - 1ULL); // m<=39 for N<=80
        }
    }

    // Reverse the lowest N bits of mask.
    inline u128 reverse_n_bits(u128 mask) const {
        uint64_t lo = (uint64_t)mask;
        uint64_t hi = (uint64_t)(mask >> 64);
        u128 rev128 = ((u128)reverse64(lo) << 64) | (u128)reverse64(hi);
        return rev128 >> (128 - N);
    }

    inline u128 canonical(u128 mask) const {
        u128 r = reverse_n_bits(mask);
        return (r < mask) ? r : mask;
    }

    // Check if c (0-based value index) is a valid next choice for the remaining-set mask.
    // Condition: the remaining-set bitstring is symmetric around c.
    inline bool is_center(u128 mask, int c) const {
        // bit c must be present in mask
        if (((mask >> c) & 1) == 0) return false;

        const auto &ci = center[c];
        int m = ci.m;
        if (m == 0) return true;

        // Extract left segment: bits [c-m .. c-1] (m bits), LSB is c-m.
        uint64_t left = (uint64_t)((mask >> ci.leftShift) & ci.segMask);
        // Extract right segment: bits [c+1 .. c+m] (m bits), LSB is c+1.
        uint64_t right = (uint64_t)((mask >> ci.rightShift) & ci.segMask);

        // Need reverse(left,m) == right. reverse64(left) puts reversed bits in top; shift down.
        uint64_t revLeft = reverse64(left) >> (64 - m);
        return revLeft == right;
    }

    u128 dfs(u128 mask) {
        mask = canonical(mask);

        if (mask == 0) return 1;

        u128 cached;
        if (memo.get(mask, cached)) return cached;

        u128 ans = 0;

        uint64_t lo = (uint64_t)mask;
        uint64_t hi = (uint64_t)(mask >> 64);

        // Iterate set bits in low 64 bits
        while (lo) {
            int b = __builtin_ctzll(lo);
            int c = b;
            if (is_center(mask, c)) {
                ans += dfs(mask & ~((u128)1 << c));
            }
            lo &= (lo - 1);
        }

        // Iterate set bits in high part (bits 64..127)
        while (hi) {
            int b = __builtin_ctzll(hi);
            int c = 64 + b;
            if (c >= N) break; // safety, though bits >=N should never be set
            if (is_center(mask, c)) {
                ans += dfs(mask & ~((u128)1 << c));
            }
            hi &= (hi - 1);
        }

        memo.set(mask, ans);
        return ans;
    }

    // Count 3-term-AP-free permutations of {1..N}.
    u128 solve() {
        u128 full = (((u128)1 << N) - 1);
        return dfs(full);
    }
};

u128 count_ap_free_permutations(int n) {
    if (n <= 0) return 0;
    Solver s(n);
    return s.solve();
}

int main(int argc, char** argv) {
    if (argc != 2) {
        cerr << "Usage: " << argv[0] << " n\n";
        return 1;
    }
    int n = stoi(argv[1]);
    if (n < 1) {
        cerr << "Please use n >= 1.\n";
        return 1;
    }
    u128 ans = count_ap_free_permutations(n);
    cout << to_string_u128(ans) << "\n";
    return 0;
}
