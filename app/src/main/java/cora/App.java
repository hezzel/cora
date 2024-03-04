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

import cora.utils.Pair;
import cora.trs.TRS;
import cora.reader.OCocoInputReader;
import cora.reader.ITrsInputReader;
import cora.reader.CoraInputReader;
import cora.termination.Handler;
import cora.termination.Handler.Answer;
import cora.termination.Horpo;
import cora.termination.Request;
import cora.termination.dependency_pairs.certification.Informal;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.Optional;

/** Basic entry class: this reads a TRS and asks the user for a term, then reduces this term. */
public class App {
    private static String _inputFile;
    private static String _outputFile;
    private static Request.Technique _technique;

    private static String getExtension(String filename) {
        int i = filename.lastIndexOf('.');
        if (i >= 0) return filename.substring(i+1);
        return "";
    }

    private static TRS readInput(String file) throws Exception {
        String extension = getExtension(file);
        if (extension.equals("trs")) return OCocoInputReader.readTrsFromFile(file);
        else if (extension.equals("itrs")) return ITrsInputReader.readTrsFromFile(file);
        else return CoraInputReader.readTrsFromFile(file);
    }

    private static void readParameters(String[] args) {
      _inputFile = null;
      _outputFile = null;
      _technique = Request.Technique.DP;
      for (int i = 0; i < args.length; i++) {
        if (args[i].equals("-o") && i+1 < args.length) {
          _outputFile = args[i];
        }
        else if (args[i].equals("--horpo")) _technique = Request.Technique.HORPO;
        else _inputFile = args[i];
      }
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

            // Build a request object requesting DP method to be used
            Request req = new Request(trs, _technique);
            Handler handler = new Handler(req);

            Informal.getInstance().addProofStep("We want to prove termination of the following system:");
            Informal.getInstance().addProofStep(trs.toString());

            Pair<Answer, Optional<String>> response = handler.getResponse();
            System.out.println(response.fst() + "\n");

            response.snd().ifPresent(System.out::println);
            // TODO: write output proof to file if an output file is given
            System.exit(0);

//            if (Horpo.applicable(trs)) {
//                Horpo.HorpoAnswer answer = Horpo.run(trs);
//                if (answer == null) System.out.println("MAYBE");
//                else System.out.println("YES\n\n" + trs.toString() + "\n" + answer.toString());
//            }
//            else System.out.println("Input is not an LCSTRS; no termination module is available.\n");
        }
        catch (Exception e) {
            System.out.println("Encountered an exception:\n" + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        }
        catch (Error e) {
            System.out.println("Encountered an error:\n" + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        }
    }
}
