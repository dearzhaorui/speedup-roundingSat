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

#pragma once

#include "Solver.hpp"
#include <limits>

namespace parsing {
int read_number(const std::string& s) {  // TODO: should also read larger numbers than int (e.g., capture large degree)
  long long answer = 0;
  for (char c : s)
    if ('0' <= c && c <= '9') {
      answer *= 10, answer += c - '0';
      //if (answer >= INF) quit::exit_ERROR({"Input formula contains absolute value larger than 10^9: ", s});
    }
  for (char c : s)
    if (c == '-') answer = -answer;
    
  if (abs(answer) >= INT_MAX) quit::exit_ERROR({"Input formula contains absolute value larger than INT_MAX: ", s}); // RUI
  return answer;
}

void opb_read(std::istream& in, Solver& solver, intConstr& objective) {
  assert(objective.isReset());
  intConstr input;  // TODO: make input use multiple precision to avoid overflow errors
  input.resize(solver.getNbVars() + 1);
  bool first_constraint = true;
  _unused(first_constraint);
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == '*') continue;
    for (char& c : line)
      if (c == ';') c = ' ';
    bool opt_line = line.substr(0, 4) == "min:";
    std::string line0;
    if (opt_line)
      line = line.substr(4), assert(first_constraint);
    else {
      std::string symbol;
      if (line.find(">=") != std::string::npos)
        symbol = ">=";
      else
        symbol = "=";
      assert(line.find(symbol) != std::string::npos);
      line0 = line;
      line = line.substr(0, line.find(symbol));
    }
    first_constraint = false;
    std::istringstream is(line);
    input.reset();
    std::vector<std::string> tokens;
    std::string tmp;
    while (is >> tmp) tokens.push_back(tmp);
    if (tokens.size() % 2 != 0) quit::exit_ERROR({"No support for non-linear constraints."});
    for (int i = 0; i < (long long)tokens.size(); i += 2)
      if (find(tokens[i].begin(), tokens[i].end(), 'x') != tokens[i].end())
        quit::exit_ERROR({"No support for non-linear constraints."});
    for (int i = 0; i < (long long)tokens.size(); i += 2) {
      std::string scoef = tokens[i];
      std::string var = tokens[i + 1];
      Coef coef = read_number(scoef);
      bool negated = false;
      std::string origvar = var;
      if (!var.empty() && var[0] == '~') {
        assert(false);
        negated = true;
        var = var.substr(1);
      }
      if (var.empty() || var[0] != 'x') quit::exit_ERROR({"Invalid literal token: ", origvar});
      var = var.substr(1);
      Lit l = atoi(var.c_str());
      if (!(1 <= l && l <= solver.getNbVars())) quit::exit_ERROR({"Literal token out of variable range: ", origvar});
      if (negated) l = -l;
      input.addLhs(coef, l);
    }
    if (opt_line){
      input.copyTo(objective);
    }
    else {
      input.addRhs(read_number(line0.substr(line0.find("=") + 1)));
      //if (input.getDegree() >= (Val)INF)
        //quit::exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
      if (solver.addConstraint(input, ConstraintType::FORMULA) == ID_Unsat) quit::exit_UNSAT({}, 0, solver.logger, solver.getStoredResult());
      if (line0.find(" = ") != std::string::npos) {  // Handle equality case with second constraint
        input.invert();
        //if (input.getDegree() >= (Val)INF)
          //quit::exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
        if (solver.addConstraint(input, ConstraintType::FORMULA) == ID_Unsat) quit::exit_UNSAT({}, 0, solver.logger, solver.getStoredResult());
      }
    }
  }
  solver.setNbOrigVars(solver.getNbVars());
}

void wcnf_read(std::istream& in, long long top, Solver& solver, intConstr& objective) {
  assert(objective.isReset());
  intConstr input;
  input.resize(solver.getNbVars() + 1);
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == 'c')
      continue;
    else {
      std::istringstream is(line);
      long long weight;
      is >> weight;
      if (weight == 0) continue;
      input.reset();
      input.addRhs(1);
      Lit l;
      while (is >> l, l) input.addLhs(1, l);
      if (weight < top) {  // soft clause
        if (weight >= INF) quit::exit_ERROR({"Clause weight exceeds 10^9: ", std::to_string(weight)});
        if (weight < 0) quit::exit_ERROR({"Negative clause weight: ", std::to_string(weight)});
        solver.setNbVars(solver.getNbVars() + 1);  // increases n to n+1
        input.resize(solver.getNbVars() + 1);
        objective.resize(solver.getNbVars() + 1);
        objective.addLhs(weight, solver.getNbVars());
        input.addLhs(1, solver.getNbVars());
      }  // else hard clause
      if (input.getDegree() >= (Val)INF)
        quit::exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
      if (solver.addConstraint(input, ConstraintType::FORMULA) == ID_Unsat) quit::exit_UNSAT({}, 0, solver.logger, solver.getStoredResult());
    }
  }
  solver.setNbOrigVars(solver.getNbVars() - objective.vars.size());
}

void cnf_read(std::istream& in, Solver& solver) {
  intConstr input;
  input.resize(solver.getNbVars() + 1);
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == 'c')
      continue;
    else {
      std::istringstream is(line);
      input.reset();
      input.addRhs(1);
      Lit l;
      while (is >> l, l) input.addLhs(1, l);
      if (solver.addConstraint(input, ConstraintType::FORMULA) == ID_Unsat) quit::exit_UNSAT({}, 0, solver.logger, solver.getStoredResult());
    }
  }
  solver.setNbOrigVars(solver.getNbVars());
}

void file_read(std::istream& in, Solver& solver, intConstr& objective) {
  for (std::string line; getline(in, line);) {
    if (line.empty() || line[0] == 'c') continue;
    if (line[0] == 'p') {
      std::istringstream is(line);
      is >> line;  // skip 'p'
      std::string type;
      is >> type;
      long long nb;
      is >> nb;
      solver.setNbVars(nb);
      if (type == "cnf") {
        cnf_read(in, solver);
      } else if (type == "wcnf") {
        is >> line;  // skip nbConstraints
        long long top;
        is >> top;
        wcnf_read(in, top, solver, objective);
      }
    } else if (line[0] == '*' && line.substr(0, 13) == "* #variable= ") {
      std::istringstream is(line.substr(13));
      long long nb;
      is >> nb;
      solver.setNbVars(nb);
      opb_read(in, solver, objective);
    } else
      quit::exit_ERROR({"No supported format [opb, cnf, wcnf] detected."});
  }
  if (solver.logger) solver.logger->formula_out << "* INPUT FORMULA ABOVE - AUXILIARY AXIOMS BELOW\n";
}
}  // namespace parsing
