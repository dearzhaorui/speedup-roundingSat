/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt

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

#include <csignal>
#include <fstream>
#include <memory>
#include "aux.hpp"
#include "globals.hpp"
#include "parsing.hpp"
#include "run.hpp"

bool asynch_interrupt;
Options options;
Stats stats;

// ---------------------------------------------------------------------
// Exit and interrupt

static void SIGINT_interrupt(int signum) {
  _unused(signum);
  asynch_interrupt = true;
}

static void SIGINT_exit(int signum) {
  _unused(signum);
  printf("\n*** INTERRUPTED ***\n");
  exit(1);
}

// ---------------------------------------------------------------------
// Main

int main(int argc, char** argv) {
  stats.STARTTIME = aux::cpuTime();
  asynch_interrupt = false;

  signal(SIGINT, SIGINT_exit);
  signal(SIGTERM, SIGINT_exit);
  signal(SIGXCPU, SIGINT_exit);
  signal(SIGINT, SIGINT_interrupt);
  signal(SIGTERM, SIGINT_interrupt);
  signal(SIGXCPU, SIGINT_interrupt);
  
  options.parseCommandLine(argc, argv);
  run::solver.init();
  std::cout << "tlimit = " << options.tlimit << ", --prop-counting= " << options.countingProp << std::endl;
  std::cout << "benchmark: " << options.formulaName << std::endl;
  std::cout << "exec info file = " << options.exec << std::endl;
  
  if (!options.formulaName.empty()) {
    std::ifstream fin(options.formulaName);
    if (!fin) quit::exit_ERROR({"Could not open ", options.formulaName});
    parsing::file_read(fin, run::solver, run::objective);
  } else {
    if (options.verbosity > 0) std::cout << "c No filename given, reading from standard input." << std::endl;
    parsing::file_read(std::cin, run::solver, run::objective);
  }

  run::run();
}
