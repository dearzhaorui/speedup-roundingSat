# Copyright (c) 2014-2020, Jan Elffers
# Copyright (c) 2019-2021, Jo Devriendt
# Copyright (c) 2020-2021, Stephan Gocht

# Parts of the code were copied or adapted from MiniSat.

# MiniSAT -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
#            Copyright (c) 2007-2010  Niklas Sorensson

# Permission is hereby granted, free of charge, to any person obtaining a
# copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be included
# in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
# OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import argparse
from pathlib import Path

cppTemplate = """
#include "%(headerFile)s"
namespace licenses {
const char* %(license_name)s =
%(license_text)s;
}
"""

hppTemplate = """
#pragma once
namespace licenses {
extern const char* %(license_name)s;
}
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('license_text', type=argparse.FileType('rt', encoding='UTF-8'))
    args = parser.parse_args()

    licenseTextFile = Path(args.license_text.name)
    license_text = ""
    for line in args.license_text:
        line = line.replace("\n", r"\n")
        line = line.replace("\"", r"\"")
        license_text += "    \"%s\"\n"%(line)
    if license_text[-1] == "\n":
        license_text = license_text[:-1]

    licenses_name = licenseTextFile.with_suffix("").name
    licenses_name = licenses_name.replace("-","_")
    licenses_name = licenses_name.replace(".","_")

    headerFile = Path(licenses_name).with_suffix(".hpp")
    sourceFile = Path(licenses_name).with_suffix(".cpp")
    with open(sourceFile, "wt") as file:
        file.write(cppTemplate%{
                "headerFile": headerFile,
                "license_name": licenses_name,
                "license_text": license_text
            })

    with open(headerFile, "wt") as file:
        file.write(hppTemplate%{
                "license_name": licenses_name
            })

if __name__ == '__main__':
    main()