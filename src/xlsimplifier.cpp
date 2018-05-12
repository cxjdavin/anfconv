/*****************************************************************************
anfconv
Copyright (C) 2016  Security Research Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "xlsimplifier.h"

#include <png.h>
#include "time_mem.h"
#include <stdio.h>
#include <boost/lexical_cast.hpp>
#include <fstream>
#include "configdata.h"
using std::endl;
using std::cout;

//#define DUMP_SIMP_EQ

void XLSimplifier::findTruths(
    vector<BoolePolynomial>& truths
    , const bool onlyPlain
) {
    //matrix is extended with assignement column, so at least 1 col large
    assert(mat->ncols > 0);

    mzd_echelonize(mat, 1);

    vector<int> ones;
    #ifdef DUMP_SIMP_EQ
    std::ofstream simpEQFile("simpEq.txt");
    #endif

    for (int row = mat->nrows-1; row >= 0; row--) {
        ones.clear();
        for (int thisCol = 0; thisCol < mat->ncols-1; thisCol++) {
            if (mzd_read_bit(mat, row, thisCol)) {
                ones.push_back(thisCol);
                if (ones.size() > 2)
                    break;
            }
        }

        //Not trivial truth. Ignore
        if (ones.size() > 2)
            continue;

        //0 = X
        if (ones.size() == 0) {
            //0=0, tautology. Ignore
            if (mzd_read_bit(mat, row, mat->ncols-1) == 0)
                continue;

            //UNSAT -- don't bother to do anything else
            truths.push_back(BoolePolynomial(true, ring));
            return;
        }

        #ifdef DUMP_SIMP_EQ
        {
            BoolePolynomial eq(mzd_read_bit(mat, row, mat->ncols-1), ring);
            for (int thisCol = 0; thisCol < mat->ncols-1; thisCol++) {
                if (mzd_read_bit(mat, row, thisCol)) {
                    eq += revMonomMap.find(thisCol)->second;
                }
            }
            simpEQFile << eq;
        }
        #endif

        BoolePolynomial eq(mzd_read_bit(mat, row, mat->ncols-1), ring);

        uint32_t deg0 = 0;
        uint32_t deg1 = 0;
        if (ones.size() >= 1) {
            map<uint32_t, BooleMonomial>::const_iterator it = revMonomMap.find(ones[0]);
            assert(it != revMonomMap.end());
            deg0 = it->second.deg();
            eq += BoolePolynomial(it->second);
        }

        if (ones.size() >= 2) {
            map<uint32_t, BooleMonomial>::const_iterator it = revMonomMap.find(ones[1]);
            assert(it != revMonomMap.end());
            deg1 = it->second.deg();
            eq += BoolePolynomial(it->second);
        }

        //stuff like "a*b + c = 1" -- not plain, so useless
        if (onlyPlain
            && ones.size() > 1
            && (deg0 > 1 || deg1 > 1)) continue;

        //stuff like "a*b = 0" -- not plain, so useless
        //note that "a*b = 1" is useful, it says that a = 1, b = 1
        if (onlyPlain
            && ones.size() == 1
            && deg0 > 1
            && !eq.hasConstantPart()) continue;

        //cout << "New truth: " << eq << endl;
        truths.push_back(eq);
    }
}

void XLSimplifier::writePNG(const std::string filename) const
{
    FILE *fp = fopen(filename.c_str(), "wb");
    if (!fp) {
        std::cerr << "Cannot open '" << filename << "' for writing" << endl;
        exit(-1);
    }

    png_structp png_ptr = png_create_write_struct(PNG_LIBPNG_VER_STRING, (png_voidp)NULL, NULL, NULL);
    if (!png_ptr) {
        cout << "ERROR: COuld not create write struct" << endl;
        fclose(fp);
        exit(-1);
    }

    png_infop info_ptr = png_create_info_struct(png_ptr);
    if (!info_ptr) {
        png_destroy_write_struct(&png_ptr, (png_infopp)NULL);
        fclose(fp);

        cout << "ERROR: COuld not create info struct" << endl;
        exit(-1);
    }

    if (setjmp(png_jmpbuf(png_ptr))) {
        png_destroy_write_struct(&png_ptr, (png_infopp)NULL);
        fclose(fp);

        cout << "[read_png_file] Error during init_io" << endl;
        exit(-1);
    }

    png_init_io(png_ptr, fp);

    //Set up&write header
    png_uint_32 width = mat->ncols;
    png_uint_32 height = mat->nrows;
    int bit_depth = 1;
    int color_type = PNG_COLOR_TYPE_GRAY;
    int interlace_type = PNG_INTERLACE_NONE;
    png_set_IHDR(png_ptr, info_ptr, width, height,
        bit_depth, color_type, interlace_type,
        PNG_COMPRESSION_TYPE_DEFAULT, PNG_FILTER_TYPE_DEFAULT);
    png_write_info(png_ptr, info_ptr);

    /* write bytes */
    if (setjmp(png_jmpbuf(png_ptr))) {
        cout << "Error during writing picture bytes" << endl;
        exit(-1);
    }

    //Write type: plain
    //png_write_png(png_ptr, info_ptr, PNG_TRANSFORM_IDENTITY, NULL);

    png_byte *row;
    int numBytes = mat->ncols/8 + (mat->ncols%8 > 0);
    row = (png_byte*)malloc(numBytes*sizeof(png_byte));
    for (int i = 0; i < mat->nrows; i++) {
        for(int col = 0; col < numBytes; col++) {
            png_byte thisByte = 0;
            for (int col2 = 7; col2 >= 0; col2--) {
                int position = (7-col2)+col*8;

                if (position < mat->ncols && mzd_read_bit(mat, i, position))
                    thisByte |= 0;
                else
                    thisByte |= 1;

                if (col2 != 0)
                    thisByte <<= 1;
            }
            row[col] = thisByte;
        }
        png_write_row(png_ptr, row);
    }
    free(row);

    // end write
    if (setjmp(png_jmpbuf(png_ptr))) {
        cout << "Error during writing end bytes" << endl;
        exit(-1);
    }

    png_write_end(png_ptr, info_ptr);
    png_destroy_write_struct(&png_ptr, &info_ptr);


    fclose(fp);
}

bool XLSimplifier::simplify(
    ANF& addNewTruthsHere
    , const uint32_t numIters
    , ConfigData& config
) {
    double myTime = cpuTime();
    std::string filename;

    //Create & dump matrix
    cout
    << "c Matrix size: "
    << getMatrix()->nrows << " x " << getMatrix()->ncols
    << endl;

    if (config.writePNG) {
        filename = "matrix-" + boost::lexical_cast<std::string>(numIters) + "-before.png";
        writePNG(filename);
        cout
        << "c Dumped matrix before iteration " << numIters
        << " to file '" << filename << "'"
        << endl;

    }

    //Gauss-eliminate matrix & dump
    vector<BoolePolynomial> newTruths;
    findTruths(newTruths, true);
    if (config.writePNG) {
        filename = "matrix-" + boost::lexical_cast<std::string>(numIters) + "-after.png";
        writePNG(filename);
        cout
        << "c Dumped matrix after iteration " << numIters
        << " to file '" << filename << "'"
        << endl;
    }

    //Add new truths, and simplify ANF
    if (newTruths.empty()) {
        cout << "No new truths found!" << endl;
        return false;
    }

    cout << "Found " << newTruths.size() << " new truth(s)" << endl;

    //Add and print new truths found
    for(vector<BoolePolynomial>::const_iterator
        it = newTruths.begin(), end = newTruths.end()
        ; it != end
        ; it++
    ) {
        if (config.verbosity >= 2) {
            cout << "New truth: " << *it << endl;
        }
        addNewTruthsHere.addBoolePolynomial(*it);
    }

    cout << "c Time to for XL: " << (cpuTime() - myTime) << endl;
    addNewTruthsHere.printStats(config.verbosity);

    return true;
}
