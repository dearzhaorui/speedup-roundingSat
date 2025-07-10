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

#include "run.hpp"

#include "ConstrExp.hpp"
#include "ConstrExpPool.hpp"
#include "Solver.hpp"
#include "optimize.hpp"

namespace rs::run {

void decide(Env& env) {
  while (true) {
    SolveState reply = aux::timeCall<SolveState>([&] { return env.solver->solve().state; }, stats.SOLVETIME);
    assert(reply != SolveState::INCONSISTENT);
    if (reply == SolveState::SAT) {
      quit::exit_SAT(env, 0);
      return;
    } else if (reply == SolveState::UNSAT) {
      quit::exit_UNSAT(env);
      return;
    }
    if (options.time_limit.get() != -1.0 && stats.getTime() > options.time_limit.get()) {
      quit::exit_INDETERMINATE(env);
      return;
    }
  }
}

template<typename SMALL, typename LARGE>
void optimize(Env& env, CeArb objective, CePtr<ConstrExp<SMALL,LARGE>> result) {
  objective->copyTo(result);
  env.opt = std::make_unique<Optimization<SMALL,LARGE>>(env, result);
  
  OptState reply = env.opt->optimize();
  switch(reply) {
  case OptState::SAT:
    quit::exit_SAT(env, env.opt->getUpperBound());
    break;
  case OptState::UNSAT:
    quit::exit_UNSAT(env);
    break;
  case OptState::OPT:
    quit::exit_OPT(env, env.opt->getUpperBound());
    break;
  case OptState::UNKNOWN:
    quit::exit_INDETERMINATE(env);
    break;
  default:
    assert(false);
  }
}

int run(Env& env, CeArb objective) {
  stats.RUNSTARTTIME = aux::cpuTime();
  if (options.verbosity.get() > 0)
    std::cout << "c #variables " << env.solver->getNbOrigVars() << " #constraints " << env.solver->getNbConstraints()
              << std::endl;
  try {
    if (objective->vars.size() > 0) {
      BigVal maxVal = objective->getCutoffVal();
      if (maxVal <= limit32) {  // TODO: try to internalize this check in ConstrExp
        ++stats.NCOUNTING32;
        std::cout << "c objective is ce32 " << std::endl;
        optimize(env, objective, env.cePools->take32());
      } else if (maxVal <= limit64) {
        ++stats.NCOUNTING64;
        std::cout << "c objective is ce64 " << std::endl;
        optimize(env, objective, env.cePools->take64());
      } else if (maxVal <= BigVal(limit96)) {
        ++stats.NCOUNTING128;
        std::cout << "c objective is ce96 " << std::endl;
        optimize(env, objective, env.cePools->take96());
      } else if (maxVal <= BigVal(limit128)) {
        ++stats.NCOUNTING128;
        std::cout << "c objective is ce128 " << std::endl;
        optimize(env, objective, env.cePools->take128());
      } else {
        ++stats.NCOUNTINGARB;
        std::cout << "c objective is ceArb " << std::endl;
        optimize(env, objective, env.cePools->takeArb());
      }
    } else {
      decide(env);
    }
  } catch (const AsynchronousInterrupt& ai) {
    if (env.opt) quit::exit_INDETERMINATE(env, env.opt->getLowerBound(), env.opt->getUpperBound());
    else quit::exit_INDETERMINATE(env);
    std::cout << "c " << ai.what() << std::endl;
    return 2;
  } catch (const OutOfMemoryException& e) {
    if (env.opt) quit::exit_INDETERMINATE(env, env.opt->getLowerBound(), env.opt->getUpperBound());
    else quit::exit_INDETERMINATE(env);
    std::cout << "c Out of memory, quitting" << std::endl;
    return 3;
  } catch (const TimeoutInterrupt& ti) {
    if (env.opt) quit::exit_INDETERMINATE(env, env.opt->getLowerBound(), env.opt->getUpperBound());
    else quit::exit_INDETERMINATE(env);
    std::cout << "c " << ti.what() << std::endl;
    return 4;
  }
  return 0;
}

}  // namespace rs::run
