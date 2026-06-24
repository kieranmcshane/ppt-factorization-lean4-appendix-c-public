#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

namespace {

using i64 = long long;
using u64 = unsigned long long;
using u128 = __uint128_t;

struct Key {
  int j;
  int h;
  bool operator<(const Key &other) const {
    return std::tie(j, h) < std::tie(other.j, other.h);
  }
};

struct DefectKey {
  int j;
  int h;
  int plus_defect;
  int minus_defect;
  int pi_cycles;
  int gamma_pi_cycles;
  int pi_gamma_inv_cycles;
  bool operator<(const DefectKey &other) const {
    return std::tie(j, h, plus_defect, minus_defect, pi_cycles,
                    gamma_pi_cycles, pi_gamma_inv_cycles) <
           std::tie(other.j, other.h, other.plus_defect, other.minus_defect,
                    other.pi_cycles, other.gamma_pi_cycles,
                    other.pi_gamma_inv_cycles);
  }
};

std::string u128_to_string(u128 x) {
  if (x == 0) return "0";
  std::string s;
  while (x > 0) {
    int digit = static_cast<int>(x % 10);
    s.push_back(static_cast<char>('0' + digit));
    x /= 10;
  }
  std::reverse(s.begin(), s.end());
  return s;
}

std::vector<int> gamma_perm(int k, int r) {
  std::vector<int> g(k * r);
  for (int b = 0; b < r; ++b) {
    for (int j = 0; j < k; ++j) {
      g[b * k + j] = b * k + ((j + 1) % k);
    }
  }
  return g;
}

std::vector<int> inverse_perm(const std::vector<int> &p) {
  std::vector<int> inv(p.size());
  for (int i = 0; i < static_cast<int>(p.size()); ++i) inv[p[i]] = i;
  return inv;
}

std::vector<int> compose(const std::vector<int> &a, const std::vector<int> &b) {
  std::vector<int> out(a.size());
  for (int i = 0; i < static_cast<int>(a.size()); ++i) out[i] = a[b[i]];
  return out;
}

int cycle_count(const std::vector<int> &p) {
  const int n = static_cast<int>(p.size());
  std::vector<char> seen(n, 0);
  int cycles = 0;
  for (int i = 0; i < n; ++i) {
    if (seen[i]) continue;
    ++cycles;
    int j = i;
    while (!seen[j]) {
      seen[j] = 1;
      j = p[j];
    }
  }
  return cycles;
}

int cycle_count_compose_left(const std::vector<int> &a,
                             const std::vector<int> &b) {
  const int n = static_cast<int>(a.size());
  std::vector<char> seen(n, 0);
  int cycles = 0;
  for (int i = 0; i < n; ++i) {
    if (seen[i]) continue;
    ++cycles;
    int j = i;
    while (!seen[j]) {
      seen[j] = 1;
      j = a[b[j]];
    }
  }
  return cycles;
}

struct DSU {
  std::vector<int> parent;
  explicit DSU(int n) : parent(n) {
    std::iota(parent.begin(), parent.end(), 0);
  }
  int find(int x) {
    while (parent[x] != x) {
      parent[x] = parent[parent[x]];
      x = parent[x];
    }
    return x;
  }
  void unite(int a, int b) {
    a = find(a);
    b = find(b);
    if (a != b) parent[a] = b;
  }
};

std::set<std::vector<int>> genus_zero_block_perms(int k) {
  std::vector<int> g = gamma_perm(k, 1);
  std::vector<int> gi = inverse_perm(g);
  std::vector<int> p(k);
  std::iota(p.begin(), p.end(), 0);
  std::set<std::vector<int>> out;
  do {
    int E = 2 * k + 2 - cycle_count_compose_left(g, p) -
            cycle_count_compose_left(p, gi) - 2 * cycle_count(p);
    if (E == 0) out.insert(p);
  } while (std::next_permutation(p.begin(), p.end()));
  return out;
}

bool has_trivial_block_component(const std::vector<int> &p,
                                 const std::vector<int> &g, int k,
                                 const std::set<std::vector<int>> &Gk) {
  const int n = static_cast<int>(p.size());
  DSU dsu(n);
  for (int i = 0; i < n; ++i) {
    dsu.unite(i, p[i]);
    dsu.unite(i, g[i]);
  }
  std::map<int, std::vector<int>> comps;
  for (int i = 0; i < n; ++i) comps[dsu.find(i)].push_back(i);
  for (const auto &[_, elems] : comps) {
    if (static_cast<int>(elems.size()) != k) continue;
    int base = *std::min_element(elems.begin(), elems.end());
    if (base % k != 0) continue;
    bool block = true;
    for (int j = 0; j < k; ++j) {
      if (!std::binary_search(elems.begin(), elems.end(), base + j)) {
        block = false;
        break;
      }
    }
    if (!block) continue;
    std::vector<int> restricted(k);
    for (int j = 0; j < k; ++j) {
      int image = p[base + j];
      if (image < base || image >= base + k) {
        block = false;
        break;
      }
      restricted[j] = image - base;
    }
    if (block && Gk.count(restricted)) return true;
  }
  return false;
}

int orbit_count(const std::vector<int> &p, const std::vector<int> &g) {
  const int n = static_cast<int>(p.size());
  DSU dsu(n);
  for (int i = 0; i < n; ++i) {
    dsu.unite(i, p[i]);
    dsu.unite(i, g[i]);
  }
  std::set<int> roots;
  for (int i = 0; i < n; ++i) roots.insert(dsu.find(i));
  return static_cast<int>(roots.size());
}

struct SpectrumResult {
  u128 total_perms = 0;
  u128 active_total = 0;
  std::map<Key, u128> table;
  std::map<DefectKey, u128> defect_table;
  double elapsed_seconds = 0.0;
};

SpectrumResult grade_exact(int k, int r, double max_seconds,
                           bool collect_defects) {
  const int n = k * r;
  const std::vector<int> g = gamma_perm(k, r);
  const std::vector<int> gi = inverse_perm(g);
  const auto Gk = genus_zero_block_perms(k);
  std::vector<int> p(n);
  std::iota(p.begin(), p.end(), 0);

  SpectrumResult res;
  auto start = std::chrono::steady_clock::now();
  bool timed_out = false;
  do {
    ++res.total_perms;
    if (max_seconds > 0.0 &&
        (static_cast<u64>(res.total_perms) & 0x3ffffULL) == 0) {
      auto now = std::chrono::steady_clock::now();
      double elapsed =
          std::chrono::duration<double>(now - start).count();
      if (elapsed > max_seconds) {
        timed_out = true;
        break;
      }
    }
    if (has_trivial_block_component(p, g, k, Gk)) continue;
    int comps = orbit_count(p, g);
    int pi_cycles = cycle_count(p);
    int gamma_pi_cycles = cycle_count_compose_left(g, p);
    int pi_gamma_inv_cycles = cycle_count_compose_left(p, gi);
    int plus_defect = n + r - pi_cycles - gamma_pi_cycles;
    int minus_defect = n + r - pi_cycles - pi_gamma_inv_cycles;
    int E = plus_defect + minus_defect;
    int j = r - comps;
    int h = (E - 4 * j) / 2;
    ++res.active_total;
    res.table[{j, h}] += 1;
    if (collect_defects) {
      res.defect_table[{j, h, plus_defect, minus_defect, pi_cycles,
                        gamma_pi_cycles, pi_gamma_inv_cycles}] += 1;
    }
  } while (std::next_permutation(p.begin(), p.end()));
  auto end = std::chrono::steady_clock::now();
  res.elapsed_seconds = std::chrono::duration<double>(end - start).count();
  if (timed_out) {
    std::cerr << "warning: timed out before exact enumeration finished for k="
              << k << " r=" << r << "\n";
  }
  return res;
}

int parse_int_arg(char **argv, int argc, const std::string &name,
                  int default_value) {
  for (int i = 1; i + 1 < argc; ++i) {
    if (argv[i] == name) return std::atoi(argv[i + 1]);
  }
  return default_value;
}

double parse_double_arg(char **argv, int argc, const std::string &name,
                        double default_value) {
  for (int i = 1; i + 1 < argc; ++i) {
    if (argv[i] == name) return std::atof(argv[i + 1]);
  }
  return default_value;
}

bool has_flag(char **argv, int argc, const std::string &flag) {
  for (int i = 1; i < argc; ++i) {
    if (argv[i] == flag) return true;
  }
  return false;
}

}  // namespace

int main(int argc, char **argv) {
  int k = parse_int_arg(argv, argc, "--k", 2);
  int r_min = parse_int_arg(argv, argc, "--r-min", 1);
  int r_max = parse_int_arg(argv, argc, "--r-max", r_min);
  double max_seconds = parse_double_arg(argv, argc, "--max-seconds", 0.0);
  bool csv = has_flag(argv, argc, "--csv");
  bool defect_csv = has_flag(argv, argc, "--defect-csv");

  if (k <= 0 || r_min <= 0 || r_max < r_min) {
    std::cerr << "usage: cl_spectrum --k K --r-min A --r-max B "
                 "[--max-seconds SEC] [--csv] [--defect-csv]\n";
    return 2;
  }
  if (defect_csv) {
    std::cout << "k,r,j,h,E,plus_defect,minus_defect,pi_cycles,"
                 "gamma_pi_cycles,pi_gamma_inv_cycles,count\n";
  } else if (csv) {
    std::cout << "k,r,j,h,E,count\n";
  }
  for (int r = r_min; r <= r_max; ++r) {
    SpectrumResult res = grade_exact(k, r, max_seconds, defect_csv);
    if (!csv && !defect_csv) {
      std::cout << "k=" << k << " r=" << r
                << " total_perms=" << u128_to_string(res.total_perms)
                << " active_total=" << u128_to_string(res.active_total)
                << " elapsed_seconds=" << std::fixed << std::setprecision(3)
                << res.elapsed_seconds << "\n";
    }
    if (defect_csv) {
      for (const auto &[key, count] : res.defect_table) {
        int E = 4 * key.j + 2 * key.h;
        std::cout << k << "," << r << "," << key.j << "," << key.h << ","
                  << E << "," << key.plus_defect << ","
                  << key.minus_defect << "," << key.pi_cycles << ","
                  << key.gamma_pi_cycles << ","
                  << key.pi_gamma_inv_cycles << ","
                  << u128_to_string(count) << "\n";
      }
      continue;
    }
    for (const auto &[key, count] : res.table) {
      int E = 4 * key.j + 2 * key.h;
      if (csv) {
        std::cout << k << "," << r << "," << key.j << "," << key.h << ","
                  << E << "," << u128_to_string(count) << "\n";
      } else {
        std::cout << "  j=" << key.j << " h=" << key.h << " E=" << E
                  << " N=" << u128_to_string(count) << "\n";
      }
    }
  }
  return 0;
}
