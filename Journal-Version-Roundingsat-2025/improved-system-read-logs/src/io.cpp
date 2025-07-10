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

#include "io.hpp"

#include <fstream>

#include "Config.hpp"

#if defined IOSTREAMS_WITH_BZIP2
#define WITHIOSTREAMS
#include <boost/iostreams/filter/bzip2.hpp>
#endif
#if defined IOSTREAMS_WITH_ZLIB
#define WITHIOSTREAMS
#include <boost/iostreams/filter/gzip.hpp>
#endif
#if defined IOSTREAMS_WITH_LZMA
#define WITHIOSTREAMS
#include <boost/iostreams/filter/lzma.hpp>
#endif
#if defined IOSTREAMS_WITH_ZSTD
#define WITHIOSTREAMS
#include <boost/iostreams/filter/zstd.hpp>
#endif
#if defined WITHIOSTREAMS
#include <boost/iostreams/filtering_stream.hpp>
#endif

namespace rs::io {

std::istream& istream::open(const std::string& fileName) {
  base = std::make_shared<std::ifstream>(fileName, std::ifstream::in);
  in = base;
#if defined WITHIOSTREAMS
  auto filter = std::make_shared<boost::iostreams::filtering_istream>();
  in = filter;
#if defined IOSTREAMS_WITH_ZLIB
  if (fileName.ends_with(".gz")) {
    filter->push(boost::iostreams::gzip_decompressor());
  }
#endif
#if defined IOSTREAMS_WITH_BZIP2
  if (fileName.ends_with(".bz2")) {
    filter->push(boost::iostreams::bzip2_decompressor());
  }
#endif
#if defined IOSTREAMS_WITH_LZMA
  if (fileName.ends_with(".xz")) {
    filter->push(boost::iostreams::lzma_decompressor());
  }
#endif
#if defined IOSTREAMS_WITH_ZSTD
  if (fileName.ends_with(".zst")) {
    filter->push(boost::iostreams::zstd_decompressor());
  }
#endif
  filter->push(*base);
#endif
  return *in;
}

std::ostream& ostream::open(const std::string& fileName) {
  base = std::make_shared<std::ofstream>(fileName, std::ofstream::out);
  out = base;
#if defined WITHIOSTREAMS
  auto filter = std::make_shared<boost::iostreams::filtering_ostream>();
  out = filter;
#if defined IOSTREAMS_WITH_ZLIB
  if (fileName.ends_with(".gz")) {
    filter->push(boost::iostreams::gzip_compressor(boost::iostreams::zlib::best_speed));
  }
#endif
#if defined IOSTREAMS_WITH_BZIP2
  if (fileName.ends_with(".bz2")) {
    filter->push(boost::iostreams::bzip2_compressor());
  }
#endif
#if defined IOSTREAMS_WITH_LZMA
  if (fileName.ends_with(".xz")) {
    filter->push(boost::iostreams::lzma_compressor());
  }
#endif
#if defined IOSTREAMS_WITH_ZSTD
  if (fileName.ends_with(".zst")) {
    filter->push(boost::iostreams::zstd_compressor(boost::iostreams::zstd_params(boost::iostreams::zstd::best_speed)));
  }
#endif
  filter->push(*base);
#endif
  return *out;
}

}  // namespace rs::io
