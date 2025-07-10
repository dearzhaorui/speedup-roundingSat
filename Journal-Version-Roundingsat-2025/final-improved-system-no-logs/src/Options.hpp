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

#pragma once

#include <sys/ioctl.h>
#include <sstream>

#include "auxiliary.hpp"
#include "quit.hpp"
#include "used_licenses/licenses.hpp"

namespace rs {

class Option {
 public:
  const std::string name = "";
  const std::string description = "";

  Option(const std::string& n, const std::string& d) : name(n), description(d) {}

  virtual void printUsage(const int nameWidth, const int textWidth) const = 0;
  virtual void parse(const std::string& v) = 0;

  void print(
    const int nameWidth,
    const int textWidth,
    const bool hasArgument,
    const std::string& text
  ) const {
    std::cout << "  --" << name;
    std::cout << (hasArgument ? "=? " : "   ");
    for (int i = name.size(); i < nameWidth; ++i) std::cout << " ";
    size_t current = 0;
    size_t length = text.size();
    while (true) {
      // Break line at a space.
      size_t endOfLine = current + textWidth < length ? text.rfind(' ', current + textWidth) : length;
      // If not possible, then break the word.
      if (current == endOfLine || endOfLine == std::string::npos) {
        endOfLine = std::min<size_t>(current + textWidth, length);
      }
      while (current < endOfLine) {
        std::cout << text[current];
        current++;
      }
      std::cout << "\n";
      if (current >= length) {
        break;
      }
      for (int i = 0; i < nameWidth + 6; ++i) std::cout << " ";
    }
    std::cout << "\n";
  }
};

class VoidOption : public Option {
  bool val = false;

 public:
  VoidOption(const std::string& n, const std::string& d) : Option{n, d} {}

  explicit operator bool() const { return val; }

  void printUsage(const int nameWidth, const int textWidth) const override {
    print(nameWidth, textWidth, false, description);
  }

  void parse([[maybe_unused]] const std::string& v) override {
    assert(v == "");
    val = true;
  }
};

class BoolOption : public Option {
  bool val = false;

 public:
  BoolOption(const std::string& n, const std::string& d, bool v) : Option{n, d}, val(v) {}

  explicit operator bool() const { return val; }

  void printUsage(const int nameWidth, const int textWidth) const override {
    std::ostringstream text;
    text << description;
    text << " (0 or 1; default: ";
    text << val;
    text << ")";
    print(nameWidth, textWidth, true, text.str());
  }

  void parse(const std::string& v) override {
    try {
      val = std::stod(v);
    } catch (const std::invalid_argument& ia) {
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    }
    if (val != 0 && val != 1)
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
  }
};

template <typename T>
class ValOption : public Option {
  T val;
  std::string checkDescription;
  std::function<bool(const T&)> check;

 public:
  ValOption(const std::string& n, const std::string& d, const T& v, const std::string& cd,
            const std::function<bool(const T&)>& c)
      : Option{n, d}, val(v), checkDescription(cd), check(c) {}

  T& get() { return val; }

  void printUsage(const int nameWidth, const int textWidth) const override {
    std::ostringstream text;
    text << description;
    text << " (";
    text << checkDescription;
    text << "; default: ";
    text << val;
    text << ")";
    print(nameWidth, textWidth, true, text.str());
  }

  void parse(const std::string& v) override {
    try {
      val = aux::sto<T>(v);
    } catch (const std::invalid_argument& ia) {
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    }
    if (!check(val)) quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
  }
};

class EnumOption : public Option {
  std::string val;
  std::vector<std::string> values;

 public:
  EnumOption(const std::string& n, const std::string& d, const std::string& v, const std::vector<std::string>& vs)
      : Option{n, d}, val(v), values(vs) {}

  void printUsage(const int nameWidth, const int textWidth) const override {
    std::ostringstream text;
    text << description;
    text << " (";
    for (int i = 0; i < (int)values.size(); ++i) {
      if (i > 0) text << ", ";
      text << values[i];
    }
    text << "; default: ";
    text << val;
    text << ")";
    print(nameWidth, textWidth, true, text.str());
  }

  void parse(const std::string& v) override {
    if (std::find(std::begin(values), std::end(values), v) == std::end(values))
      quit::exit_ERROR({"Invalid value for ", name, ": ", v, ".\nCheck usage with --help option."});
    val = v;
  }

  bool is(const std::string& v) const {
    assert(std::find(std::begin(values), std::end(values), v) != std::end(values));
    return val == v;
  }
};


struct Options {
  // Help/debug options.
  VoidOption help{
    "help",
    "Print this help message and exit."
  };
  VoidOption copyright{
    "copyright",
    "Print copyright information and exit."
  };
  ValOption<std::string> license{
    "license",
    "Print the license text of the given license and exit.",
    "",
    "/path/to/file",
    [](const std::string&) -> bool { return true; }
  };
  BoolOption printSol{
    "print-sol",
    "Print the solution if found.",
    0
  };
  ValOption<int> verbosity{
    "verbosity",
    "Verbosity of the output (higher values gives more output).",
    1,
    "0 =< int",
    [](const int& x) -> bool { return x >= 0; }
  };

  // Solver options.
  ValOption<std::string> proofLog{
    "proof-log",
    "Filename for the proof log, leave unspecified to disable proof logging.",
    "",
    "/path/to/file",
    [](const std::string&) -> bool { return true; }};
  EnumOption optMode{
    "opt-mode",
    "Optimization mode to use.",
    "hybrid",
    {"linear", "coreguided", "coreboosted", "hybrid"}
  };
  ValOption<double> lubyBase{
    "luby-base",
    "Base of the Luby restart sequence.",
    2,
    "1 =< float",
    [](double x) -> bool { return 1 <= x; }
  };
  ValOption<int> lubyMult{
    "luby-mult",
    "Multiplier of the Luby restart sequence.",
    100,
    "1 =< int",
    [](const int& x) -> bool { return x >= 1; }
  };
  ValOption<double> varDecay{
    "vsids-var",
    "VSIDS variable decay factor.",
    0.95,
    "0.5 =< float < 1",
    [](const double& x) -> bool { return 0.5 <= x && x < 1; }
  };
  ValOption<double> clauseDecay{
    "vsids-clause",
    "VSIDS clause decay factor.",
    0.999,
    "0.5 =< float < 1",
    [](const double& x) -> bool { return 0.5 <= x && x < 1; }
  };
  ValOption<int> dbCleanInc{
    "db-inc",
    "Database cleanup interval increment.",
    100,
    "1 =< int",
    [](const int& x) -> bool { return 1 <= x; }
  };

  // Propagation options.
  ValOption<double> propCounting{
    "prop-counting",
    "Propagation: Counting propagation instead of watched propagation.",
    0.6,
    "0 (no counting) =< float =< 1 (always counting)",
    [](const double& x) -> bool { return 0 <= x && x <= 1; }
  };
  BoolOption propClause{
    "prop-clause",
    "Propagation: Optimized two-watched propagation for clauses.",
    1
  };
  BoolOption propCard{
    "prop-card",
    "Propagation: Optimized two-watched propagation for cardinality constraints.",
    1
  };
  BoolOption propIdx{
    "prop-idx",
    "Propagation: Optimize index of watches during propagation.",
    1
  };
  BoolOption propSup{
    "prop-sup",
    "Propagation: Avoid superfluous watch checks.",
    1
  };

  // Linear programming (LP) solver options.
  ValOption<double> lpPivotRatio{
    "lp",
    "Linear programming solver: Ratio of #pivots/#conflicts limiting LP calls (negative means infinite, 0 means no LP solving).",
    1,
    "-1 =< float",
    [](const double& x) -> bool { return x >= -1; }
  };
  ValOption<int> lpPivotBudget{
    "lp-budget",
    "Linear programming solver: Base LP call pivot budget.",
    1000,
    "1 =< int",
    [](const int& x) -> bool { return x >= 1; }
  };
  ValOption<double> lpIntolerance{
    "lp-intolerance",
    "Linear programming solver: Intolerance for floating point artifacts.",
    1e-6,
    "0 < float",
    [](const double& x) -> bool { return x > 1; }
  };
  BoolOption addGomoryCuts{
    "lp-cut-gomory",
    "Linear programming solver: Generate Gomory cuts.",
    1
  };
  BoolOption addLearnedCuts{
    "lp-cut-learned",
    "Linear programming solver: Use learned constraints as cuts.",
    1
  };
  ValOption<int> gomoryCutLimit{
    "lp-cut-gomlim",
    "Linear programming solver: Max number of tableau rows considered for Gomory cuts in a single round.",
    100,
    "1 =< int",
    [](const int& x) -> bool { return 1 <= x; }
  };
  ValOption<double> maxCutCos{
    "lp-cut-maxcos",
    "Linear programming solver: Upper bound on cosine of angle between cuts added in one round, higher means cuts can be more parallel.",
    0.1,
    "0 =< float =< 1",
    [](const double& x) -> bool { return 0 <= x && x <= 1; }
  };

  // Conflict analysis and bit-width options.
  BoolOption slackdiv{
    "ca-slackdiv",
    "Conflict analysis: Use slack+1 as divisor for reason constraints (instead of the asserting coefficient).",
    0
  };
  BoolOption weakenFull{
    "ca-weaken-full",
    "Conflict analysis: Weaken non-divisible non-falsified literals in reason constraints completely.",
    0
  };
  BoolOption weakenNonImplying{
    "ca-weaken-nonimplying",
    "Conflict analysis: Weaken non-implying falsified literals from reason constraints.",
    0
  };
  BoolOption bumpOnlyFalse{
    "bump-onlyfalse",
    "Bump activity of literals encountered during conflict analysis only when falsified.",
    0
  };
  BoolOption bumpCanceling{
    "bump-canceling",
    "Bump activity of literals encountered during conflict analysis when canceling.",
    1
  };
  BoolOption bumpLits{
    "bump-lits",
    "Bump activity of literals encountered during conflict analysis, twice when occurring with opposing sign.",
    1
  };
  ValOption<int> bitsOverflow{
    "bits-overflow",
    "Bit-width: Bit width of maximum coefficient during conflict analysis calculations (0 is unlimited, unlimited or greater than 62 may use slower arbitrary precision implementations).",
    62,
    "0 =< int",
    [](const int& x) -> bool { return x >= 0; }
  };
  ValOption<int> bitsReduced{
    "bits-reduced",
    "Bit-width: Bit width of maximum coefficient after reduction when exceeding bits-overflow (0 is unlimited, 1 reduces to cardinalities).",
    29,
    "0 =< int",
    [](const int& x) -> bool { return x >= 0; }
  };
  ValOption<int> bitsLearned{
    "bits-learned",
    "Bit-width: Bit width of maximum coefficient for learned constraints (0 is unlimited, 1 reduces to cardinalities).",
    29,
    "0 =< int",
    [](const int& x) -> bool { return x >= 0; }
  };
  ValOption<int> bitsInput{
    "bits-input",
    "Bit width of maximum coefficient for input constraints (0 is unlimited, 1 allows only cardinalities).",
    0,
    "0 =< int",
    [](const int& x) -> bool { return x >= 0; }
  };

  // Core guided search and core extraction options.
  EnumOption cgEncoding{
    "cg-encoding",
    "Core guided search: Encoding of the extension constraints.",
    "lazysum",
    {"sum", "lazysum", "reified"}
  };
  ValOption<int> cgBoosted{
    "cg-boost",
    "Core guided search: Seconds of core-boosted search before switching to linear search.",
    10,
    "0 =< int",
    [](const int& x) -> bool { return x >= 0; }
  };
  ValOption<float> cgHybrid{
    "cg-hybrid",
    "Core guided search: Ratio of core-guided search to linear search during hybrid optimization.",
    0.5,
    "0 =< float =< 1",
    [](const double& x) -> bool { return x >= 0 && x <= 1; }
  };
  BoolOption cgIndCores{
    "cg-indcores",
    "Core guided search: Use independent cores for core-guided search.",
    0
  };
  BoolOption cgStrat{
    "cg-strat",
    "Core guided search: Use stratification for core-guided search.",
    1
  };
  BoolOption cgSolutionPhase{
    "cg-solutionphase",
    "Core guided search: Fix the phase to the incumbent solution during linear optimization.",
    1
  };
  EnumOption cgReduction{
    "cg-cardreduct",
    "Core guided search: Core-guided reduction to cardinality.",
    "bestbound",
    {"clause", "minslack", "bestbound"}
  };
  BoolOption cgResolveProp{
    "cg-resprop",
    "Core guided search: Resolve propagated assumptions when extracting cores.",
    0
  };
  BoolOption cgDecisionCore{
    "cg-decisioncore",
    "Core guided search: Extract a second decision core, choose the best resulting cardinality core.",
    1
  };
  BoolOption cgCoreUpper{
    "cg-coreupper",
    "Core guided search: Exploit upper bound on cardinality cores.",
    1
  };

  // Misc options.
  BoolOption keepAll{
    "keepall",
    "Keep all learned constraints in the database indefinitely.",
    0
  };
  ValOption<double> time_limit{
    "time-limit",
    "Aborting solving after specified time in seconds.",
    -1,
    "-1 off or 0 <= float",
    [](double x) -> bool { return 0 <= x || x == -1; }
  };
  BoolOption logDebug{
    "log-debug",
    "Output debugging information to proof log.",
#if NDEBUG
    0
#else
    1
#endif
  };

  const std::vector<Option*> options = {
    // Help/debug options.
    &copyright,
    &license,
    &help,
    &printSol,
    &verbosity,

    // Solver options.
    &proofLog,
    &optMode,
    &lubyBase,
    &lubyMult,
    &varDecay,
    &clauseDecay,
    &dbCleanInc,

    // Propagation options.
    &propCounting,
    &propClause,
    &propCard,
    &propIdx,
    &propSup,

    // Linear programming (LP) solver options.
    &lpPivotRatio,
    &lpPivotBudget,
    &lpIntolerance,
    &addGomoryCuts,
    &addLearnedCuts,
    &gomoryCutLimit,
    &maxCutCos,

    // Conflict analysis and bit-width options.
    &slackdiv,
    &weakenFull,
    &weakenNonImplying,
    &bumpOnlyFalse,
    &bumpCanceling,
    &bumpLits,
    &bitsOverflow,
    &bitsReduced,
    &bitsLearned,
    &bitsInput,

    // Core guided search and core extraction options.
    &cgEncoding,
    &cgBoosted,
    &cgHybrid,
    &cgIndCores,
    &cgStrat,
    &cgSolutionPhase,
    &cgReduction,
    &cgResolveProp,
    &cgDecisionCore,
    &cgCoreUpper,

    // Misc options.
    &keepAll,
    &time_limit,
    &logDebug,
  };
  std::unordered_map<std::string, Option*> name2opt;

  Options() {
    for (Option* opt : options) name2opt[opt->name] = opt;
  }

  std::string formulaName;

  void parseCommandLine(int argc, char** argv) {
    std::unordered_map<std::string, std::string> opt_val;
    for (int i = 1; i < argc; i++) {
      std::string arg = argv[i];
      if (arg.substr(0, 2) != "--") {
        formulaName = arg;
      } else {
        size_t eqindex = std::min(arg.size(), arg.find('='));
        std::string inputopt = arg.substr(2, eqindex - 2);
        if (name2opt.count(inputopt) == 0) {
          quit::exit_ERROR({"Unknown option: ", inputopt, ".\nCheck usage with ", argv[0], " --help"});
        } else {
          name2opt[inputopt]->parse(arg.substr(std::min(arg.size(), eqindex + 1)));
        }
      }
    }

    if (help) {
      usage(argv[0]);
      exit(0);
    } else if (copyright) {
      licenses::printUsed();
      exit(0);
    } else if (license.get() != "") {
      licenses::printLicense(license.get());
      exit(0);
    }
  }

  void usage(char* name) {
    printf("Usage: %s [OPTIONS] instance.(opb|cnf|wcnf)\n", name);
    printf("or     cat instance.(opb|cnf|wcnf) | %s [OPTIONS]\n", name);
    printf("\n");
    printf("Options:\n");
    int nameWidth = 0;
    for (Option* opt : options) nameWidth = std::max<int>(nameWidth, opt->name.size());
    struct winsize window;
    ioctl(STDOUT_FILENO, TIOCGWINSZ, &window);
    int textWidth = window.ws_col - nameWidth - 8;
    for (Option* opt : options) opt->printUsage(nameWidth, textWidth);
  }

};

}  // namespace rs
