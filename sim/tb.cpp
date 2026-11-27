// Verilator testbench: drives the Solver interface the way design.py does.
//
// Usage: Vsolver FILE.cnf MAX_CYCLES [FILE2.cnf ...]
// For each CNF in turn: abort, load, start, run up to MAX_CYCLES, read the
// model and check it against the clauses. Several files in one process also
// check that ABORT isolates instances. Prints one JSON line per instance:
//   {"file":..., "status":"sat|unsat|unknown|rejected|timeout|skipped",
//    "cycles":N, "model_ok":true|false|null}
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <vector>

#include "Vsolver.h"
#include "caps.h"
#include "verilated.h"

struct Cnf {
  uint64_t nvars = 0, nclauses = 0, nlits = 0;
  std::vector<int32_t> words;  // literals and 0 terminators, file order
  std::vector<std::vector<int32_t>> clauses;
};

static bool read_cnf(const char *path, Cnf &c) {
  FILE *f = fopen(path, "r");
  if (!f) return false;
  char line[1 << 16];
  bool header = false;
  std::vector<int32_t> cur;
  while (true) {
    if (!header) {
      if (!fgets(line, sizeof line, f)) break;
      if (line[0] == 'c' || line[0] == '%') continue;
      if (line[0] == 'p') {
        unsigned long long v, cl;
        sscanf(line, "p cnf %llu %llu", &v, &cl);
        c.nvars = v;
        c.nclauses = cl;
        header = true;
      }
      continue;
    }
    long x;
    int r = fscanf(f, "%ld", &x);
    if (r != 1) {
      // skip a comment or stray token
      int ch = fgetc(f);
      if (ch == EOF) break;
      if (ch == 'c' || ch == '%') {
        if (!fgets(line, sizeof line, f)) break;
      }
      continue;
    }
    c.words.push_back((int32_t)x);
    if (x == 0) {
      c.clauses.push_back(cur);
      cur.clear();
    } else {
      cur.push_back((int32_t)x);
      c.nlits++;
    }
  }
  fclose(f);
  return header;
}

struct Sim {
  std::unique_ptr<VerilatedContext> ctx;
  std::unique_ptr<Vsolver> top;
  uint64_t cycles = 0;
  Sim() : ctx(new VerilatedContext), top(new Vsolver(ctx.get())) {
    top->clk = 0;
    top->rst = 1;
    top->eval();
    tick();
    tick();
    top->rst = 0;
    tick();
  }
  void tick() {
    top->clk = 1;
    top->eval();
    top->clk = 0;
    top->eval();
    cycles++;
  }
};

static void run_one(Sim &s, const char *path, uint64_t max_cycles) {
  Cnf c;
  if (!read_cnf(path, c)) {
    printf("{\"file\":\"%s\",\"status\":\"error\",\"cycles\":0,\"model_ok\":null}\n", path);
    return;
  }
  auto *t = s.top.get();
  if (c.nvars > MAX_VARS || c.nclauses > MAX_CLAUSES || c.nlits > MAX_LITS) {
    printf("{\"file\":\"%s\",\"status\":\"skipped\",\"cycles\":0,\"model_ok\":null}\n", path);
    return;
  }
  // ABORT, held for 2+ cycles, then wait for idle (the shell does this).
  t->__SYM__abort = 1;
  s.tick();
  s.tick();
  int w = 0;
  while (!t->idle && w < 2000000) { s.tick(); w++; }
  t->__SYM__abort = 0;
  s.tick();
  t->nvars = c.nvars;
  t->nclauses = c.nclauses;
  t->nlits = c.nlits;
  s.tick();
  for (int32_t x : c.words) {
    while (!t->load_ready) s.tick();
    t->load_data = (uint32_t)x;
    t->load_valid = 1;
    s.tick();
    t->load_valid = 0;
  }
  s.tick();
  t->start = 1;
  s.tick();
  t->start = 0;
  uint64_t c0 = s.cycles;
  const char *status = "timeout";
  while (s.cycles - c0 < max_cycles) {
    t->eval();
    if (t->rejected) { status = "rejected"; break; }
    if (t->done) {
      status = t->result == 1 ? "sat" : t->result == 2 ? "unsat" : "unknown";
      break;
    }
    s.tick();
  }
  uint64_t cyc = s.cycles - c0;
  const char *mok = "null";
  if (!strcmp(status, "sat")) {
    std::vector<uint8_t> val(c.nvars + 1, 0);
    for (uint64_t v = 0; v < c.nvars; v++) {
      t->model_addr = v;
      s.tick();  // model_val is valid one cycle after model_addr
      t->eval();
      val[v + 1] = t->model_val;
    }
    bool ok = true;
    for (auto &cl : c.clauses) {
      bool sat = false;
      for (int32_t l : cl) {
        if ((l > 0) == (bool)val[l > 0 ? l : -l]) { sat = true; break; }
      }
      if (!sat) { ok = false; break; }
    }
    mok = ok ? "true" : "false";
  }
  printf("{\"file\":\"%s\",\"status\":\"%s\",\"cycles\":%llu,\"model_ok\":%s}\n", path, status,
         (unsigned long long)cyc, mok);
  fflush(stdout);
}

int main(int argc, char **argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: %s FILE.cnf MAX_CYCLES [FILE2.cnf ...]\n", argv[0]);
    return 2;
  }
  uint64_t max_cycles = strtoull(argv[2], nullptr, 10);
  Sim s;
  run_one(s, argv[1], max_cycles);
  for (int i = 3; i < argc; i++) run_one(s, argv[i], max_cycles);
  return 0;
}
