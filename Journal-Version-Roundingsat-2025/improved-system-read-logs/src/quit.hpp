/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2021, Jo Devriendt
Copyright (c) 2020-2021, Stephan Gocht
Copyright (c) 2014-2021, Jakob Nordström

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

#include <memory>
#include <vector>
#include "typedefs.hpp"
#include "ExecInfo.hpp"

namespace rs {

class Env;

namespace quit {
void printSol(const std::vector<Lit>& sol);
void printSolAsOpb(const std::vector<Lit>& sol);
void exit_SAT(const Env& env, const bigint& bestSoFar);
void exit_OPT(const Env& env, const bigint& opt);
void exit_UNSAT(const Env& env);
void exit_INDETERMINATE(const Env& env);
void exit_INDETERMINATE(const Env& env, const bigint& lb, const bigint& ub);
void exit_ERROR(const std::initializer_list<std::string>& messages);

void writeFinalStatus(std::ofstream* out, const bigint& bestObjVal, const std::string status);
void checkResults(const bigint& bestObjVal, const Result& r);
}  // namespace quit

}  // namespace rs
