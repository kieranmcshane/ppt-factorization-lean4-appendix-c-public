#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <string>
#include <tuple>
#include <vector>

namespace {

using u128 = __uint128_t;

struct Key {
  int plus_defect;
  int g_plus;
  std::string status;

  bool operator<(const Key &other) const {
    return std::tie(plus_defect, g_plus, status) <
           std::tie(other.plus_defect, other.g_plus, other.status);
  }
};

struct BidefectKey {
  int plus_defect;
  int minus_defect;
  int g_plus;
  int g_minus;

  bool operator<(const BidefectKey &other) const {
    return std::tie(plus_defect, minus_defect, g_plus, g_minus) <
           std::tie(other.plus_defect, other.minus_defect, other.g_plus,
                    other.g_minus);
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

std::vector<int> gamma_perm(int k) {
  std::vector<int> g(2 * k);
  for (int block = 0; block < 2; ++block) {
    for (int j = 0; j < k; ++j) {
      g[block * k + j] = block * k + ((j + 1) % k);
    }
  }
  return g;
}

std::vector<int> inverse_perm(const std::vector<int> &p) {
  std::vector<int> inv(p.size());
  for (int i = 0; i < static_cast<int>(p.size()); ++i) inv[p[i]] = i;
  return inv;
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

int cycle_count_gamma_pi(const std::vector<int> &gamma,
                         const std::vector<int> &pi) {
  const int n = static_cast<int>(pi.size());
  std::vector<char> seen(n, 0);
  int cycles = 0;
  for (int i = 0; i < n; ++i) {
    if (seen[i]) continue;
    ++cycles;
    int j = i;
    while (!seen[j]) {
      seen[j] = 1;
      j = gamma[pi[j]];
    }
  }
  return cycles;
}

int cycle_count_pi_gamma_inv(const std::vector<int> &pi,
                             const std::vector<int> &gamma_inv) {
  const int n = static_cast<int>(pi.size());
  std::vector<char> seen(n, 0);
  int cycles = 0;
  for (int i = 0; i < n; ++i) {
    if (seen[i]) continue;
    ++cycles;
    int j = i;
    while (!seen[j]) {
      seen[j] = 1;
      j = pi[gamma_inv[j]];
    }
  }
  return cycles;
}

bool connected_two_blocks(const std::vector<int> &pi, int k) {
  for (int i = 0; i < k; ++i) {
    if (pi[i] >= k) return true;
  }
  return false;
}

std::string classify(int k, int g_plus) {
  constexpr int r = 2;
  constexpr int merger = r - 1;
  const double half_density = static_cast<double>(merger + g_plus) / r;
  if (g_plus <= merger) return "map_set_closes";
  if (half_density >= static_cast<double>(k - 1) / 2.0) return "cycle_closes";
  return "open_benchmark";
}

int parse_int_arg(char **argv, int argc, const std::string &name, int def) {
  for (int i = 1; i + 1 < argc; ++i) {
    if (argv[i] == name) return std::atoi(argv[i + 1]);
  }
  return def;
}

bool has_flag(char **argv, int argc, const std::string &flag) {
  for (int i = 1; i < argc; ++i) {
    if (argv[i] == flag) return true;
  }
  return false;
}

}  // namespace

int main(int argc, char **argv) {
  const int k = parse_int_arg(argv, argc, "--k", 6);
  const bool bidefect = has_flag(argv, argc, "--bidefect");
  if (k < 2) {
    std::cerr << "usage: two_block_open_exact --k K [--bidefect]\n";
    return 2;
  }

  const int r = 2;
  const int n = 2 * k;
  const auto gamma = gamma_perm(k);
  const auto gamma_inv = inverse_perm(gamma);
  std::vector<int> pi(n);
  std::iota(pi.begin(), pi.end(), 0);

  u128 total = 0;
  u128 connected = 0;
  std::map<Key, u128> distribution;
  std::map<BidefectKey, u128> bidefect_distribution;
  auto start = std::chrono::steady_clock::now();

  do {
    ++total;
    if (!connected_two_blocks(pi, k)) continue;
    ++connected;
    const int pi_cycles = cycle_count(pi);
    const int gamma_pi_cycles = cycle_count_gamma_pi(gamma, pi);
    const int pi_gamma_inv_cycles = cycle_count_pi_gamma_inv(pi, gamma_inv);
    const int plus_defect = n + r - pi_cycles - gamma_pi_cycles;
    const int minus_defect = n + r - pi_cycles - pi_gamma_inv_cycles;
    if (plus_defect < 2 * (r - 1) || plus_defect % 2 != 0) {
      std::cerr << "bad connected plus defect: " << plus_defect << "\n";
      return 1;
    }
    if (minus_defect < 2 * (r - 1) || minus_defect % 2 != 0) {
      std::cerr << "bad connected minus defect: " << minus_defect << "\n";
      return 1;
    }
    const int g_plus = (plus_defect - 2 * (r - 1)) / 2;
    const int g_minus = (minus_defect - 2 * (r - 1)) / 2;
    distribution[{plus_defect, g_plus, classify(k, g_plus)}] += 1;
    bidefect_distribution[{plus_defect, minus_defect, g_plus, g_minus}] += 1;
  } while (std::next_permutation(pi.begin(), pi.end()));

  auto end = std::chrono::steady_clock::now();
  double elapsed = std::chrono::duration<double>(end - start).count();

  std::cout << "# Two-block connected one-sided exact profile\n";
  std::cout << "# k=" << k << "\n";
  std::cout << "# r=2\n";
  std::cout << "# total_permutations=" << u128_to_string(total) << "\n";
  std::cout << "# connected_permutations=" << u128_to_string(connected) << "\n";
  std::cout << "# elapsed_seconds=" << std::fixed << std::setprecision(3)
            << elapsed << "\n";
  if (bidefect) {
    std::cout << "plus_defect,minus_defect,g_plus,g_minus,count,"
                 "frequency_among_connected\n";
    for (const auto &[key, count] : bidefect_distribution) {
      long double freq = 0.0L;
      if (connected != 0) {
        freq = static_cast<long double>(count) /
               static_cast<long double>(connected);
      }
      std::cout << key.plus_defect << "," << key.minus_defect << ","
                << key.g_plus << "," << key.g_minus << ","
                << u128_to_string(count) << "," << std::setprecision(12)
                << static_cast<double>(freq) << "\n";
    }
    return 0;
  }

  std::cout << "plus_defect,g_plus,status,count,frequency_among_connected\n";
  for (const auto &[key, count] : distribution) {
    long double freq = 0.0L;
    if (connected != 0) {
      freq = static_cast<long double>(count) / static_cast<long double>(connected);
    }
    std::cout << key.plus_defect << "," << key.g_plus << "," << key.status
              << "," << u128_to_string(count) << "," << std::setprecision(12)
              << static_cast<double>(freq) << "\n";
  }
  return 0;
}
