// Search for low expected meeting times in symmetric blocks of closed walks.
// Build: c++ -O3 -std=c++17 search_rendezvous.cpp -o search_rendezvous
// Run:   ./search_rendezvous NEW_OUTPUT_DIRECTORY [maximum_even_block_length]
// Integer replay of the resulting table is independent of this floating-point
// search.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct Path {
  unsigned word;
  signed char h[32];
};
int block_length;
Path decode_word(unsigned w) {
  Path p;
  p.word = w;
  int a = 0;
  for (int t = 0; t < block_length; t++) {
    a += (w >> t & 1) ? 1 : -1;
    p.h[t] = a;
  }
  return p;
}
struct Pair {
  int duration, hits;
};
// Reflection gives four orientation cases. One hits at t=1, since every
// word starts forward. In the three other cases, the first hit is respectively
// the first time left > right, left < right or left + right < 0 in local
// displacements. Otherwise the closed path pays block_length and the block
// restarts.
Pair pair_statistics(const Path &a, const Path &b) {
  int greater_time = block_length + 1, less_time = block_length + 1,
      negative_sum_time = block_length + 1;
  for (int t = 1; t < block_length - 1; t++) {
    int u = a.h[t], v = b.h[t];
    if (u > v && greater_time > block_length)
      greater_time = t + 1;
    if (u < v && less_time > block_length)
      less_time = t + 1;
    if (u + v < 0 && negative_sum_time > block_length)
      negative_sum_time = t + 1;
    if (greater_time <= block_length && less_time <= block_length &&
        negative_sum_time <= block_length)
      break;
  }
  return {1 + min(block_length, greater_time) + min(block_length, less_time) +
              min(block_length, negative_sum_time),
          1 + (greater_time <= block_length) + (less_time <= block_length) +
              (negative_sum_time <= block_length)};
}
struct Mix {
  vector<unsigned> words;
  vector<double> w;
};
// With fixed ratio ratio, minimize x^T(duration-ratio*hits)x over the current
// support by transferring probability between two words at a time. Solving
// this quadratic along each feasible transfer gives the step size below.
double optimize_weights(Mix &mixture) {
  int k = mixture.words.size();
  vector<Path> p;
  for (auto z : mixture.words)
    p.push_back(decode_word(z));
  vector<vector<Pair>> m(k, vector<Pair>(k));
  for (int i = 0; i < k; i++)
    for (int j = 0; j <= i; j++)
      m[i][j] = m[j][i] = pair_statistics(p[i], p[j]);
  auto &x = mixture.w;
  double previous_ratio = 100;
  for (int pass = 0; pass < 8; pass++) {
    double A = 0, B = 0;
    for (int i = 0; i < k; i++)
      if (x[i] > 0)
        for (int j = 0; j < k; j++)
          if (x[j] > 0) {
            A += x[i] * x[j] * m[i][j].duration;
            B += x[i] * x[j] * m[i][j].hits;
          }
    double ratio = A / B;
    if (abs(previous_ratio - ratio) < 1e-9)
      return ratio;
    previous_ratio = ratio;
    vector<vector<double>> quadratic(k, vector<double>(k));
    vector<double> gradient(k);
    for (int i = 0; i < k; i++)
      for (int j = 0; j < k; j++) {
        quadratic[i][j] = m[i][j].duration - ratio * m[i][j].hits;
        gradient[i] += quadratic[i][j] * x[j];
      }
    for (int it = 0; it < 20000; it++) {
      int a = 0, b = -1;
      for (int i = 0; i < k; i++) {
        if (gradient[i] < gradient[a])
          a = i;
        if (x[i] > 1e-15 && (b < 0 || gradient[b] < gradient[i]))
          b = i;
      }
      if (gradient[b] - gradient[a] < 1e-7)
        break;
      double curvature =
          quadratic[a][a] + quadratic[b][b] - 2 * quadratic[a][b];
      double d = curvature > 0
                     ? min(x[b], (gradient[b] - gradient[a]) / curvature)
                     : x[b];
      x[a] += d;
      x[b] -= d;
      for (int i = 0; i < k; i++)
        gradient[i] += d * (quadratic[a][i] - quadratic[b][i]);
    }
  }
  return previous_ratio;
}
void drop_negligible_weights(Mix &s) {
  Mix z;
  double sum = 0;
  for (int i = 0; i < s.w.size(); i++)
    if (s.w[i] > 1e-10) {
      z.words.push_back(s.words[i]);
      z.w.push_back(s.w[i]);
      sum += s.w[i];
    }
  for (double &v : z.w)
    v /= sum;
  s = z;
}
int main(int argc, char **argv) {
  if (argc < 2 || argc > 3) {
    fprintf(stderr, "Usage: %s NEW_OUTPUT_DIRECTORY [maximum_even_length]\n",
            argv[0]);
    return 2;
  }
  int max_length = argc == 3 ? atoi(argv[2]) : 22;
  if (max_length < 4 || max_length > 30 || max_length % 2) {
    fprintf(stderr, "Use an even length from 4 to 30.\n");
    return 2;
  }
  filesystem::path directory(argv[1]);
  if (!filesystem::create_directory(directory)) {
    fprintf(stderr, "Use a new output directory.\n");
    return 2;
  }
  Mix s;
  block_length = 4;
  for (unsigned k = 1; k < (1u << block_length); k += 2)
    if (__builtin_popcount(k) == block_length / 2) {
      s.words.push_back(k);
      s.w.push_back(1. / 3);
    }
  for (; block_length <= max_length; block_length += 2) {
    // Lengthen each old word by a final FB excursion to initialize the new
    // length.
    if (block_length > 4)
      for (auto &k : s.words)
        k |= 1u << (block_length - 2);
    double ratio = optimize_weights(s);
    drop_negligible_weights(s);
    for (int pass = 0; pass < 130; pass++) {
      set<unsigned> neighbors(s.words.begin(), s.words.end());
      for (unsigned w : s.words) {
        // Relocate any one right step to a left step (without moving the first
        // step).
        for (int i = 1; i < block_length; i++)
          if (w >> i & 1)
            for (int j = 1; j < block_length; j++)
              if (!(w >> j & 1))
                neighbors.insert(w ^ (1u << i) ^ (1u << j));
      }
      for (unsigned w : s.words)
        neighbors.erase(w);
      vector<Path> routes;
      for (auto k : s.words)
        routes.push_back(decode_word(k));
      vector<pair<double, unsigned>> improving_words;
      for (unsigned w : neighbors) {
        auto p = decode_word(w);
        double gradient = 0;
        for (int j = 0; j < s.w.size(); j++) {
          auto v = pair_statistics(p, routes[j]);
          gradient += s.w[j] * (v.duration - ratio * v.hits);
        }
        if (gradient < -1e-6)
          improving_words.emplace_back(gradient, w);
      }
      if (improving_words.empty())
        break;
      sort(improving_words.begin(), improving_words.end());
      int add = min(32, (int)improving_words.size());
      for (int j = 0; j < add; j++) {
        s.words.push_back(improving_words[j].second);
        s.w.push_back(0);
      }
      double old = ratio;
      ratio = optimize_weights(s);
      drop_negligible_weights(s);
      if (pass % 10 == 0)
        fprintf(stderr, "block_length=%d pass=%d support=%zu E=%.10f\n",
                block_length, pass, s.w.size(), ratio);
      if (old - ratio < 1e-10)
        break;
    }
    auto path = directory / ("rendezvous-" + to_string(block_length) + ".tsv");
    FILE *f = fopen(path.string().c_str(), "w");
    if (!f) {
      perror("write weights");
      return 1;
    }
    for (int i = 0; i < s.w.size(); i++) {
      for (int j = 0; j < block_length; j++)
        fputc((s.words[i] >> j & 1) ? 'F' : 'B', f);
      fprintf(f, "\t%lld\n", llround(s.w[i] * 1000000000));
    }
    fclose(f);
    fprintf(stderr, "DONE block_length=%d support=%zu E=%.10f\n", block_length,
            s.w.size(), ratio);
  }
}
