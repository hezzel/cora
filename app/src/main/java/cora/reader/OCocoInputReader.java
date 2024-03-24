/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.reader;

import java.io.IOException;
import java.util.ArrayList;

import charlie.parser.lib.ErrorCollector;
import charlie.parser.OCocoParser;
import charlie.parser.Parser.ParserProgram;
import cora.trs.TRS;

/**
 * This class reads text from string or file written in the .trs format that up until 2023 was used
 * by the international confluence competition; this is a simplification of the old human-readable
 * format of the international termination competition.
 * It handles both unsorted and many-sorted TRSs, by delegating to either OCocoUnsortedInputReader
 * or OCocoSortedInputReader, depending on the shape of the input string / file.
 */
public class OCocoInputReader {
  /**
   * Parses the given program, and returns the (sorted or unsorted) TRS that it defines.
   * If the string is not correctly formed, this may throw a ParseError.
   */
  public static TRS readTrsFromString(String str) {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = OCocoParser.readProgramFromString(str, collector);
    if (trs.fundecs().isEmpty()) return OCocoUnsortedInputReader.readParserProgram(trs, collector);
    else return OCocoSortedInputReader.readParserProgram(trs, collector);
  }

  /**
   * Parses the given file, which should be a .trs file in one of the two supported CoCo formats,
   * into a many-sorted TRS.
   * This may throw a ParseError, or an IOException if something goes wrong with the file reading.
   */
  public static TRS readTrsFromFile(String filename) throws IOException {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = OCocoParser.readProgramFromFile(filename, collector);
    if (trs.fundecs().isEmpty()) return OCocoUnsortedInputReader.readParserProgram(trs, collector);
    else return OCocoSortedInputReader.readParserProgram(trs, collector);
  }
}
