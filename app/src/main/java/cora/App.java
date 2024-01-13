/**************************************************************************************************
 Copyright 2019, 2023 Cynthia Kop

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

import com.google.common.collect.ImmutableList;
import cora.config.Config;
import cora.reader.OCocoInputReader;
import cora.rewriting.TRS;
import cora.reader.CoraInputReader;
import cora.reader.OCocoInputReader;
import cora.termination.Horpo;
import cora.types.*;

import java.io.BufferedReader;
import java.io.InputStreamReader;
//import cora.ADT.* ;

/** Basic entry class: this reads a TRS and asks the user for a term, then reduces this term. */
public class App {
    private static String _inputFile;
    private static String _inputTerm;

    private static String getExtension(String filename) {
        int i = filename.lastIndexOf('.');
        if (i >= 0) return filename.substring(i+1);
        return "";
    }

    private static TRS readInput(String file) throws Exception {
        String extension = getExtension(file);
        if (extension.equals("trs")) return OCocoInputReader.readTrsFromFile(file);
        else return CoraInputReader.readProgramFromFile(file);
    }

    private static void readParameters(String[] args) {
        _inputFile = null;
        _inputTerm = null;
        if (args.length > 0) _inputFile = args[0];
        if (args.length > 1) _inputTerm = args[0];
    }

    public static void main(String[] args) {
        try {
            readParameters(args);

            if (_inputFile == null) {
                System.out.print("Input file: ");
                System.out.flush();
                _inputFile = (new BufferedReader(new InputStreamReader(System.in))).readLine();
            }
            TRS trs = readInput(_inputFile);
            if (trs == null) return;

      /*
      System.out.print(trs.toString());

      if (_inputTerm == null) {
        System.out.println("Input term: ");
        System.out.flush();
        _inputTerm = (new BufferedReader(new InputStreamReader(System.in))).readLine();
      }

      Term term = CoraInputReader.readTermFromString(_inputTerm, trs);

      do {
        term = trs.leftmostInnermostReduce(term);
        if (term != null) System.out.println("⇒ " + term.toString());
      } while (term != null);
      */
            if (Horpo.applicable(trs)) {
                Horpo.HorpoAnswer answer = Horpo.run(trs);
                if (answer == null) System.out.println("MAYBE");
                else System.out.println("YES\n\n" + trs.toString() + "\n" + answer.toString());
            }
            else System.out.println("Input is not an LCSTRS; no termination module is available.\n");
        }
        catch (Exception e) {
            System.out.println("Encountered an exception:\n" + e.getMessage());
        }
        catch (Error e) {
            System.out.println("Encountered an error:\n" + e.getMessage());
        }
    }
}
