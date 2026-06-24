#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <gmpxx.h>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace {

using Partition = std::vector<int>;
using Poly = std::map<std::pair<int, int>, mpq_class>;
using PolyC = std::map<std::tuple<int, int, int>, mpq_class>;

int part_size(const Partition &p) {
  return std::accumulate(p.begin(), p.end(), 0);
}

std::vector<Partition> partitions_rec(int n, int max_part) {
  if (n == 0) return {Partition{}};
  max_part = std::min(max_part, n);
  std::vector<Partition> out;
  for (int first = max_part; first >= 1; --first) {
    int rest_max = (n - first > 0) ? std::min(first, n - first) : 0;
    for (auto rest : partitions_rec(n - first, rest_max)) {
      rest.insert(rest.begin(), first);
      out.push_back(std::move(rest));
    }
  }
  return out;
}

std::vector<Partition> partitions(int n) {
  return partitions_rec(n, n);
}

mpz_class factorial(int n) {
  mpz_class out = 1;
  for (int i = 2; i <= n; ++i) out *= i;
  return out;
}

mpz_class dim_specht(const Partition &lam) {
  int n = part_size(lam);
  mpz_class hooks = 1;
  int max_col = lam.empty() ? 0 : lam.front();
  std::vector<int> col_heights(max_col, 0);
  for (int c = 0; c < max_col; ++c) {
    for (int row_len : lam) {
      if (row_len > c) ++col_heights[c];
    }
  }
  for (int r = 0; r < static_cast<int>(lam.size()); ++r) {
    for (int c = 0; c < lam[r]; ++c) {
      hooks *= (lam[r] - c) + (col_heights[c] - r - 1);
    }
  }
  return factorial(n) / hooks;
}

Partition trim_partition(Partition p) {
  while (!p.empty() && p.back() == 0) p.pop_back();
  return p;
}

void subpartitions_rec(const Partition &lam, int target, int i, int prev,
                       int remaining, Partition &acc,
                       std::vector<Partition> &out) {
  if (i == static_cast<int>(lam.size())) {
    if (remaining == 0) out.push_back(trim_partition(acc));
    return;
  }
  int upper = std::min({prev, lam[i], remaining});
  for (int value = upper; value >= 0; --value) {
    acc.push_back(value);
    subpartitions_rec(lam, target, i + 1, value, remaining - value, acc, out);
    acc.pop_back();
  }
}

std::vector<Partition> subpartitions_bounded(const Partition &lam, int target) {
  std::vector<Partition> out;
  Partition acc;
  subpartitions_rec(lam, target, 0, 1000000000, target, acc, out);
  return out;
}

std::set<std::pair<int, int>> skew_cells(const Partition &lam,
                                         const Partition &nu) {
  std::set<std::pair<int, int>> cells;
  for (int r = 0; r < static_cast<int>(lam.size()); ++r) {
    int nu_len = (r < static_cast<int>(nu.size())) ? nu[r] : 0;
    for (int c = nu_len; c < lam[r]; ++c) cells.insert({r, c});
  }
  return cells;
}

bool connected(const std::set<std::pair<int, int>> &cells) {
  if (cells.empty()) return false;
  std::vector<std::pair<int, int>> stack{*cells.begin()};
  std::set<std::pair<int, int>> seen{*cells.begin()};
  while (!stack.empty()) {
    auto [r, c] = stack.back();
    stack.pop_back();
    for (auto nb : {std::pair<int, int>{r - 1, c}, {r + 1, c}, {r, c - 1},
                    {r, c + 1}}) {
      if (cells.count(nb) && !seen.count(nb)) {
        seen.insert(nb);
        stack.push_back(nb);
      }
    }
  }
  return seen.size() == cells.size();
}

bool no_two_by_two(const std::set<std::pair<int, int>> &cells) {
  for (auto [r, c] : cells) {
    if (cells.count({r + 1, c}) && cells.count({r, c + 1}) &&
        cells.count({r + 1, c + 1})) {
      return false;
    }
  }
  return true;
}

std::vector<std::pair<Partition, int>> rim_hooks(const Partition &lam, int m) {
  int n = part_size(lam);
  if (m > n) return {};
  std::vector<std::pair<Partition, int>> hooks;
  for (const auto &nu : subpartitions_bounded(lam, n - m)) {
    auto cells = skew_cells(lam, nu);
    if (static_cast<int>(cells.size()) != m) continue;
    if (!connected(cells) || !no_two_by_two(cells)) continue;
    int min_row = cells.begin()->first;
    int max_row = cells.begin()->first;
    for (auto [r, _] : cells) {
      min_row = std::min(min_row, r);
      max_row = std::max(max_row, r);
    }
    hooks.push_back({nu, 1 + max_row - min_row});
  }
  return hooks;
}

std::map<Partition, mpz_class> domino_char_cache;

mpz_class character_domino(const Partition &lam) {
  auto it = domino_char_cache.find(lam);
  if (it != domino_char_cache.end()) return it->second;
  int n = part_size(lam);
  if (n == 0) return domino_char_cache[lam] = 1;
  if (n % 2 != 0) return domino_char_cache[lam] = 0;
  mpz_class total = 0;
  for (const auto &[nu, height] : rim_hooks(lam, 2)) {
    mpz_class term = character_domino(nu);
    if ((height - 1) % 2) total -= term;
    else total += term;
  }
  domino_char_cache[lam] = total;
  return total;
}

std::map<int, mpz_class> content_cycle_transform(const Partition &lam,
                                                 const mpz_class &dim) {
  std::vector<mpz_class> coeff{1};
  for (int row = 0; row < static_cast<int>(lam.size()); ++row) {
    for (int col = 0; col < lam[row]; ++col) {
      int content = col - row;
      std::vector<mpz_class> next(coeff.size() + 1);
      for (int degree = 0; degree < static_cast<int>(coeff.size()); ++degree) {
        next[degree] += coeff[degree] * content;
        next[degree + 1] += coeff[degree];
      }
      coeff.swap(next);
    }
  }
  std::map<int, mpz_class> out;
  for (int degree = 0; degree < static_cast<int>(coeff.size()); ++degree) {
    mpz_class value = dim * coeff[degree];
    if (value != 0) out[degree] = value;
  }
  return out;
}

std::map<std::pair<int, int>, mpz_class> total_polynomial_for_r(int r) {
  int n = 2 * r;
  auto irreps = partitions(n);
  mpz_class nfac = factorial(n);
  mpz_class common_den = nfac * nfac;
  std::map<std::pair<int, int>, mpz_class> term_buckets;
  for (const auto &lam : irreps) {
    mpz_class match_char = character_domino(lam);
    if (match_char == 0) continue;
    mpz_class dim = dim_specht(lam);
    if (nfac % dim != 0) {
      throw std::runtime_error("Specht dimension did not divide n!");
    }
    mpz_class denom_multiplier = nfac / dim;
    auto by_cycles = content_cycle_transform(lam, dim);
    for (const auto &[p, left] : by_cycles) {
      if (left == 0) continue;
      for (const auto &[q, right] : by_cycles) {
        if (right == 0) continue;
        term_buckets[{p, q}] += match_char * left * right * denom_multiplier;
      }
    }
  }
  std::map<std::pair<int, int>, mpz_class> out;
  for (const auto &[key, numerator] : term_buckets) {
    mpz_class rem = numerator % common_den;
    if (rem != 0) throw std::runtime_error("nonintegral coefficient");
    mpz_class coeff = numerator / common_den;
    if (coeff != 0) out[key] = coeff;
  }
  return out;
}

Poly poly_add(const Poly &a, const Poly &b, const mpq_class &scale = 1) {
  Poly out = a;
  for (const auto &[key, value] : b) {
    out[key] += scale * value;
    if (out[key] == 0) out.erase(key);
  }
  return out;
}

Poly poly_mul(const Poly &a, const Poly &b) {
  Poly out;
  for (const auto &[k1, v1] : a) {
    for (const auto &[k2, v2] : b) {
      out[{k1.first + k2.first, k1.second + k2.second}] += v1 * v2;
    }
  }
  for (auto it = out.begin(); it != out.end();) {
    if (it->second == 0) it = out.erase(it);
    else ++it;
  }
  return out;
}

std::vector<Poly> series_mul(const std::vector<Poly> &a,
                             const std::vector<Poly> &b, int R) {
  std::vector<Poly> out(R + 1);
  for (int i = 0; i <= R; ++i) {
    if (a[i].empty()) continue;
    for (int j = 0; j <= R - i; ++j) {
      if (!b[j].empty()) out[i + j] = poly_add(out[i + j], poly_mul(a[i], b[j]));
    }
  }
  return out;
}

std::vector<Poly> series_log(const std::vector<Poly> &total, int R) {
  std::vector<Poly> u(R + 1), out(R + 1), power(R + 1);
  for (int i = 1; i <= R; ++i) u[i] = total[i];
  power[0][{0, 0}] = 1;
  for (int m = 1; m <= R; ++m) {
    power = series_mul(power, u, R);
    mpq_class scale((m % 2) ? 1 : -1, m);
    for (int i = 0; i <= R; ++i) {
      if (!power[i].empty()) out[i] = poly_add(out[i], power[i], scale);
    }
  }
  return out;
}

PolyC polyc_add(const PolyC &a, const PolyC &b, const mpq_class &scale = 1) {
  PolyC out = a;
  for (const auto &[key, value] : b) {
    out[key] += scale * value;
    if (out[key] == 0) out.erase(key);
  }
  return out;
}

PolyC polyc_mul(const PolyC &a, const PolyC &b) {
  PolyC out;
  for (const auto &[k1, v1] : a) {
    for (const auto &[k2, v2] : b) {
      out[{std::get<0>(k1) + std::get<0>(k2),
           std::get<1>(k1) + std::get<1>(k2),
           std::get<2>(k1) + std::get<2>(k2)}] += v1 * v2;
    }
  }
  for (auto it = out.begin(); it != out.end();) {
    if (it->second == 0) it = out.erase(it);
    else ++it;
  }
  return out;
}

std::vector<PolyC> seriesc_mul(const std::vector<PolyC> &a,
                               const std::vector<PolyC> &b, int R) {
  std::vector<PolyC> out(R + 1);
  for (int i = 0; i <= R; ++i) {
    if (a[i].empty()) continue;
    for (int j = 0; j <= R - i; ++j) {
      if (!b[j].empty()) out[i + j] = polyc_add(out[i + j], polyc_mul(a[i], b[j]));
    }
  }
  return out;
}

std::vector<PolyC> seriesc_exp(const std::vector<PolyC> &a, int R) {
  std::vector<PolyC> out(R + 1);
  out[0][{0, 0, 0}] = 1;
  for (int n = 1; n <= R; ++n) {
    PolyC acc;
    for (int i = 1; i <= n; ++i) {
      if (a[i].empty() || out[n - i].empty()) continue;
      PolyC term = polyc_mul(a[i], out[n - i]);
      acc = polyc_add(acc, term, i);
    }
    out[n] = polyc_add(PolyC{}, acc, mpq_class(1, n));
  }
  return out;
}

std::map<int, std::map<std::pair<int, int>, mpz_class>> active_spectra(int R) {
  std::vector<Poly> total(R + 1);
  total[0][{0, 0}] = 1;
  for (int r = 1; r <= R; ++r) {
    std::cerr << "computing total polynomial r=" << r << "\n";
    auto total_r = total_polynomial_for_r(r);
    mpz_class rfac = factorial(r);
    for (const auto &[key, value] : total_r) total[r][key] = mpq_class(value, rfac);
  }
  auto connected = series_log(total, R);
  std::vector<PolyC> active_conn(R + 1);
  for (int r = 2; r <= R; ++r) {
    for (const auto &[key, value] : connected[r]) {
      active_conn[r][{1, key.first, key.second}] = value;
    }
  }
  auto active = seriesc_exp(active_conn, R);
  std::map<int, std::map<std::pair<int, int>, mpz_class>> spectra;
  for (int r = 1; r <= R; ++r) {
    mpz_class rfac = factorial(r);
    for (const auto &[key, value] : active[r]) {
      mpq_class count = value * rfac;
      if (count.get_den() != 1) throw std::runtime_error("nonintegral active count");
      int components = std::get<0>(key);
      int pcycles = std::get<1>(key);
      int qcycles = std::get<2>(key);
      int j = r - components;
      int h = r - pcycles - qcycles + 2 * components;
      spectra[r][{j, h}] += count.get_num();
    }
  }
  return spectra;
}

int parse_int_arg(char **argv, int argc, const std::string &name, int def) {
  for (int i = 1; i + 1 < argc; ++i) {
    if (argv[i] == name) return std::atoi(argv[i + 1]);
  }
  return def;
}

std::string parse_string_arg(char **argv, int argc, const std::string &name,
                             const std::string &def) {
  for (int i = 1; i + 1 < argc; ++i) {
    if (argv[i] == name) return argv[i + 1];
  }
  return def;
}

}  // namespace

int main(int argc, char **argv) {
  int r_max = parse_int_arg(argv, argc, "--r-max", 20);
  std::string out_path =
      parse_string_arg(argv, argc, "--out", "cl_probe/spectrum_k2_character.csv");
  auto spectra = active_spectra(r_max);
  std::ofstream out(out_path);
  out << "k,r,j,h,E,count\n";
  for (const auto &[r, table] : spectra) {
    std::vector<std::tuple<int, int, int, mpz_class>> rows;
    for (const auto &[key, count] : table) {
      int j = key.first;
      int h = key.second;
      if (count != 0) rows.push_back({4 * j + 2 * h, j, h, count});
    }
    std::sort(rows.begin(), rows.end(),
              [](const auto &a, const auto &b) {
                return std::tie(std::get<0>(a), std::get<1>(a), std::get<2>(a)) <
                       std::tie(std::get<0>(b), std::get<1>(b), std::get<2>(b));
              });
    for (const auto &[E, j, h, count] : rows) {
      out << "2," << r << "," << j << "," << h << "," << E << ","
          << count.get_str() << "\n";
    }
  }
  std::cerr << "wrote " << out_path << "\n";
  return 0;
}
