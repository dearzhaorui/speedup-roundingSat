/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2021, Jo Devriendt
Copyright (c) 2020-2021, Stephan Gocht
Copyright (c) 2014-2024, Jakob Nordström
Copyright (c) 2022-2024, Andy Oertel
Copyright (c) 2024, Marc Vinyals

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
***********************************************************************/

#if defined WITHSTACKTRACE
#define BOOST_STACKTRACE_USE_BACKTRACE
#define BOOST_STACKTRACE_USE_ADDR2LINE
#include <boost/stacktrace.hpp>
#endif

#include <csignal>
#include <fstream>
#include <memory>

#include "ConstrExp.hpp"
#include "ConstrExpPool.hpp"
#include "Env.hpp"
#include "Logger.hpp"
#include "auxiliary.hpp"
#include "globals.hpp"
#include "io.hpp"
#include "parsing.hpp"
#include "run.hpp"
#include "version.hpp"

namespace rs {

bool asynch_interrupt;
Options options;
Stats stats;

}  // namespace rs

static void SIGINT_interrupt([[maybe_unused]] int signum) {
  rs::asynch_interrupt = true;
#if HARD_INTERRUPT
  // It is unsafe to do IO on an interrupt, hence disabled by default
  // Should be fine in a competition setting
  rs::quit::exit_INDETERMINATE(rs::run::solver);
  exit(1);
#endif
}

static void SIGINT_exit([[maybe_unused]] int signum) {
  printf("\n*** INTERRUPTED ***\n");
  exit(1);
}

static void SIGABRT_debug([[maybe_unused]] int signum) {
#if defined WITHSTACKTRACE
  std::cerr << boost::stacktrace::stacktrace();
#endif
}

int main(int argc, char** argv) {
  rs::stats.STARTTIME = rs::aux::cpuTime();
  rs::asynch_interrupt = false;

  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
#if defined __unix__
  signal(SIGXCPU, SIGINT_exit);
#endif
  signal(SIGABRT, SIGABRT_debug);

  rs::options.parseCommandLine(argc, argv);

  if (rs::options.verbosity.get() > 0) {
    std::cout << "c RoundingSat 2\n";
    std::cout << "c branch " << GIT_BRANCH << "\n";
    std::cout << "c commit " << GIT_COMMIT_HASH << std::endl;
  }

  rs::Env env;

  const std::string& proof_log_name = rs::options.proofLog.get();
  rs::io::ostream proof_out;

  if (not proof_log_name.empty()) {
    std::ostream& out = proof_out.open(proof_log_name);
    if (not *proof_out.base) {
      rs::quit::exit_ERROR({"Could not open proof log."});
    }
    env.logger = std::make_unique<rs::Logger>(out);
  }

  env.cePools = std::make_unique<rs::ConstrExpPools>(env);
  env.solver = std::make_unique<rs::Solver>(env);

  rs::CeArb objective = env.cePools->takeArb();
  bool infeasible_or_error = false;

  const std::string& input_name = rs::options.formulaName;
  if (not input_name.empty()) {
    rs::io::istream inptr;
    std::istream& in = inptr.open(input_name);
    if (not *inptr.base) {
      rs::quit::exit_ERROR({"Could not open input."});
    }
    infeasible_or_error = rs::parsing::file_read(in, env, objective);
  }
  //  else {
  //    if (rs::options.verbosity.get() > 0) std::cout << "c No filename given, reading from standard input" <<
  //    std::endl; infeasible_or_error = rs::parsing::file_read(std::cin, rs::run::solver, objective);
  //  }

  if (infeasible_or_error) return 0;

  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
#if defined __unix__
  signal(SIGXCPU, SIGINT_interrupt);
#endif

  env.solver->initLP(objective);

  return rs::run::run(env, objective);
}
