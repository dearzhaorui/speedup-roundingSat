/***********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2020, Jo Devriendt
Copyright (c) 2020, Stephan Gocht

Parts of the code were copied or adapted from MiniSat.

MiniSAT -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
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

#include "licenses.hpp"
#include <iomanip>
#include <iostream>
#include <unordered_map>
#include <vector>
#include "MIT.hpp"
#include "apache_2.hpp"
#include "boost.hpp"
#include "gpl_3_0.hpp"
#include "lgpl_3_0.hpp"
#include "roundingsat.hpp"

namespace licenses {
class LicenseStore {
 private:
  std::unordered_map<std::string, const char*> map;

 public:
  LicenseStore() {
    map.insert({
        {"GPL-3.0", gpl_3_0},
        {"LGPL-3.0", lgpl_3_0},
        {"GMP", lgpl_3_0},
        {"MIT", MIT},
        {"RoundingSAT", roundingsat},
        {"Boost", boost},
        {"Apache-2.0", apache_2},
        {"Soplex", apache_2},
    });
  }

  const char* get(std::string licenseName) {
    auto result = map.find(licenseName);
    if (result != map.end()) {
      return result->second;
    }
    return "License not found, note that license names are case sensitive.";
  }
};

class Tool {
 public:
  std::string shortName;
  std::string info;
  std::string licenseName;
};

std::vector<Tool> usedTools() {
  std::vector<Tool> result = {
      {"RoundingSAT", "The source code of RoundingSAT", "MIT"},
#ifdef WITHGMP
      {"GMP", "GNU Multiple Precision Arithmetic Library", "LGPL-3.0"},
#endif
      {"Boost", "Boost", "Boost"},
#ifdef WITHSOPLEX
      {"Soplex", "Soplex", "Apache 2.0"},
#endif
  };
  return result;
}

void printLicense(std::string licenseName) {
  LicenseStore store;
  std::cout << store.get(licenseName) << std::endl;
}

void printUsed() {
  std::vector<Tool> used = usedTools();
  std::cout << "The following libraries / tools are contained." << std::endl;
  std::cout << "Use --license=[toolName] or --license=[licenseName]  "
            << "to display the license text. " << std::endl;
  std::cout << "Note that the license that applies to the binary depends on "
            << "the tools used. Please refer to the license text to deterimin "
            << "which license applies." << std::endl;

  std::cout << std::setw(20) << "Library / Tool" << std::setw(15) << "License"
            << "   "
            << "Information" << std::endl;

  for (Tool tool : used) {
    std::cout << std::setw(20) << tool.shortName << std::setw(15) << tool.licenseName << "   " << tool.info
              << std::endl;
  }
}
}  // namespace licenses
