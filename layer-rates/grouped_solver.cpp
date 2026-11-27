// Float64 simultaneous GD and Heun steps for the full finite network.
// Neurons that keep the same gates undergo the same 3-by-3 linear map.
// See README for the per-stage check that validates each grouped block.
#include <algorithm>
#include <array>
#include <cmath>
#include <limits>
#include <vector>

using Vec = std::array<double, 3>; // (readout, wx, wy)
using Mat = std::array<Vec, 3>;
constexpr Mat identity{{{1., 0., 0.}, {0., 1., 0.}, {0., 0., 1.}}};

double dot(const Vec &a, const Vec &b) {
  return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}
Vec apply_map(const Mat &m, const Vec &p) {
  return {dot(m[0], p), dot(m[1], p), dot(m[2], p)};
}

struct Group {
  int mask;
  double min_margin;
  Mat second{};
  std::vector<size_t> members;
};
struct State {
  std::vector<Mat> transforms;
  std::vector<Vec> loose;
};

struct Solver {
  std::vector<Vec> points, grid;
  std::vector<Group> groups;
  std::vector<size_t> loose_ids;
  std::vector<double> residual;
  double tau, step, scale, max_shift = 0.;
  bool heun;

  int gates(const Vec &p, double *margin = nullptr) const {
    int mask = 0;
    double minimum = std::numeric_limits<double>::infinity();
    for (size_t i = 0; i < grid.size(); ++i) {
      double z = p[1] * grid[i][1] + p[2] * grid[i][2];
      mask |= int(z > 0.) << i;
      minimum = std::min(minimum, std::abs(z));
    }
    if (margin)
      *margin = minimum / std::sqrt(dot(p, p));
    return mask;
  }

  State partition(double threshold) {
    std::vector<int> by_mask(1u << grid.size(), -1);
    groups.clear();
    loose_ids.clear();
    State state;
    for (size_t j = 0; j < points.size(); ++j) {
      const Vec &p = points[j];
      double margin;
      int mask = gates(p, &margin);
      if (!(margin > threshold)) {
        loose_ids.push_back(j);
        state.loose.push_back(p);
        continue;
      }
      int &index = by_mask[mask];
      if (index == -1) {
        index = groups.size();
        groups.push_back({mask, margin, {}, {}});
        state.transforms.push_back(identity);
      }
      auto &group = groups[index];
      group.members.push_back(j);
      group.min_margin = std::min(group.min_margin, margin);
      for (int i = 0; i < 3; ++i)
        for (int k = 0; k < 3; ++k)
          group.second[i][k] += p[i] * p[k];
    }
    return state;
  }
  void add_output(int mask, double ax, double ay) {
    for (size_t i = 0; i < grid.size(); ++i)
      if (mask & (1 << i))
        residual[i] += ax * grid[i][1] + ay * grid[i][2];
  }
  Vec force(int mask) const {
    Vec g{};
    for (size_t i = 0; i < grid.size(); ++i)
      if (mask & (1 << i)) {
        g[1] += residual[i] * grid[i][1];
        g[2] += residual[i] * grid[i][2];
      }
    return g;
  }
  static Vec velocity(const Vec &g, const Vec &p, double tau) {
    return {g[1] * p[1] + g[2] * p[2], tau * p[0] * g[1], tau * p[0] * g[2]};
  }
  // Writes U + step*F(V) into W. U and W may coincide.
  bool stage(const State &u, const State &v, State &w,
             std::vector<int> &masks) {
    std::fill(residual.begin(), residual.end(), 0.);
    for (size_t j = 0; j < groups.size(); ++j) {
      const Mat &m = v.transforms[j];
      double sq = 0.;
      for (int i = 1; i < 3; ++i)
        for (int k = 0; k < 3; ++k)
          sq += std::pow(m[i][k] - identity[i][k], 2);
      double shift = std::sqrt(sq);
      max_shift = std::max(max_shift, shift);
      if (!(shift + 1e-14 < groups[j].min_margin))
        return false;
      Vec cov = apply_map(groups[j].second, m[0]);
      add_output(groups[j].mask, dot(m[1], cov), dot(m[2], cov));
    }
    for (size_t j = 0; j < v.loose.size(); ++j) {
      const Vec &p = v.loose[j];
      masks[j] = gates(p);
      add_output(masks[j], p[0] * p[1], p[0] * p[2]);
    }
    for (size_t i = 0; i < grid.size(); ++i)
      residual[i] =
          (1. + grid[i][1] - residual[i] / scale) / (grid.size() * scale);
    for (size_t j = 0; j < groups.size(); ++j) {
      Vec g = force(groups[j].mask);
      const Mat &m = v.transforms[j];
      for (int k = 0; k < 3; ++k) {
        Vec change = velocity(g, {m[0][k], m[1][k], m[2][k]}, tau);
        for (int i = 0; i < 3; ++i)
          w.transforms[j][i][k] = u.transforms[j][i][k] + step * change[i];
      }
    }
    for (size_t j = 0; j < v.loose.size(); ++j) {
      Vec change = velocity(force(masks[j]), v.loose[j], tau);
      for (int i = 0; i < 3; ++i)
        w.loose[j][i] = u.loose[j][i] + step * change[i];
    }
    return true;
  }
  bool block(int steps, double threshold) {
    State current = partition(threshold), trial = current, next = current;
    std::vector<int> masks(current.loose.size());
    max_shift = 0.;
    for (int k = 0; k < steps; ++k) {
      if (!stage(current, current, trial, masks))
        return false;
      if (heun) {
        // .5*current + .5*(trial + step*F(trial))
        if (!stage(trial, trial, next, masks))
          return false;
        for (size_t j = 0; j < groups.size(); ++j)
          for (int i = 0; i < 3; ++i)
            for (int l = 0; l < 3; ++l)
              current.transforms[j][i][l] +=
                  .5 * (next.transforms[j][i][l] - current.transforms[j][i][l]);
        for (size_t j = 0; j < current.loose.size(); ++j)
          for (int i = 0; i < 3; ++i)
            current.loose[j][i] +=
                .5 * (next.loose[j][i] - current.loose[j][i]);
      } else
        std::swap(current, trial);
    }
    for (size_t j = 0; j < groups.size(); ++j)
      for (size_t id : groups[j].members)
        points[id] = apply_map(current.transforms[j], points[id]);
    for (size_t j = 0; j < loose_ids.size(); ++j)
      points[loose_ids[j]] = current.loose[j];
    return true;
  }
  double grid_rms() {
    std::fill(residual.begin(), residual.end(), 0.);
    for (const Vec &p : points)
      add_output(gates(p), p[0] * p[1], p[0] * p[2]);
    double ss = 0.;
    for (size_t i = 0; i < grid.size(); ++i)
      ss += std::pow(residual[i] / scale - 1. - grid[i][1], 2);
    return std::sqrt(ss / grid.size());
  }
};

// 'iters' is the reported step cap. Set tol=0 for exact prescribed step counts.
extern "C" int simulate(int n, int m, double *raw, const double *x, double tau,
                        double step, int iters, int heun, double tol) {
  Solver s;
  s.tau = tau;
  s.step = step;
  s.heun = heun;
  s.scale = std::sqrt(double(m));
  for (int j = 0; j < m; ++j)
    s.points.push_back({raw[3 * j], raw[3 * j + 1], raw[3 * j + 2]});
  for (int i = 0; i < n; ++i)
    s.grid.push_back({0., x[2 * i], x[2 * i + 1]});
  s.residual.resize(n);
  int completed = 0, length = 16;
  double threshold = std::min(1., 5. / s.scale);
  while (completed < iters) {
    int count = std::min(length, iters - completed);
    while (!s.block(count, threshold))
      threshold =
          std::min(2., std::max(2. * threshold, 2. * s.max_shift + 1e-12));
    completed += count;
    if (tol > 0. && s.grid_rms() < tol)
      break;
    threshold = std::min(1., std::max(1e-12, 2. * s.max_shift));
    length = std::min(1024, 2 * length);
  }
  for (int j = 0; j < m; ++j)
    for (int i = 0; i < 3; ++i)
      raw[3 * j + i] = s.points[j][i];
  return completed;
}
