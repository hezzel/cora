/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import cora.exceptions.ParserException;
import cora.interfaces.terms.Term;
import cora.interfaces.rewriting.TRS;
import cora.parsers.CoraInputReader;
import cora.parsers.TrsInputReader;

public class Main {
  private static String getExtension(String filename) {
    int i = filename.lastIndexOf('.');
    if (i >= 0) return filename.substring(i+1);
    return "";
  }

  private static TRS readInput(String file) throws Exception {
    String extension = getExtension(file);
    if (extension.equals("trs") || extension.equals("mstrs")) {
      return TrsInputReader.readTrsFromFile(file);
    }
    if (extension.equals("cora")) {
      return CoraInputReader.readProgramFromFile(file);
    }
    throw new Exception("Unknown file extension: " + extension + ".");
  }

  public static void main(String[] args) {
    try {
      TRS trs = args.length > 0 ? readInput(args[0]) : readInput("test.cora");
      if (trs == null) return;

      System.out.print(trs.toString());
      System.out.print("Input term: ");
      String input = (new BufferedReader(new InputStreamReader(System.in))).readLine();
      Term term = CoraInputReader.readTermFromString(input, trs, null);
      do {
        term = trs.leftmostInnermostReduce(term);
        if (term != null) System.out.println("⇒ " + term.toString());
      } while (term != null);
    }
    catch (Exception e) {
      System.out.println("Exception: " + e.getMessage());
    }
  }
}
