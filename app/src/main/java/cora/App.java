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

import charlie.exceptions.ParseError;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.trs.TRS;
import cora.reader.OCocoInputReader;
import cora.reader.ITrsInputReader;
import cora.reader.CoraInputReader;
import cora.io.*;
import cora.config.Settings;
import cora.reduction.Reducer;
import cora.termination.TerminationHandler;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.Optional;

/** Basic entry class: this reads a TRS and asks the user for a term, then reduces this term. */
public class App {
  private static String _inputFile;
  private static String _request;
  
  private static void readParameters(String[] args) {
    _inputFile = null;
    _request = null;
    for (int i = 0; i < args.length; i++) {
      if (args[i].equals("-r") && i+1 < args.length) {
        _request = args[i+1];
        i++;
      }
      else if (args[i].length() > 10 && args[i].substring(0,10).equals("--request=")) {
        _request = args[i].substring(10);
      }
      else if (args[i].charAt(0) == '-') {
        System.out.println("Unknown option: " + args[i]);
      }
      else if (_inputFile != null) {
        System.out.println("Only one input file should be given (received both " + _inputFile +
          " and " + args[i] + ").");
      }
      else _inputFile = args[i];
    }
  }

  private static String getExtension(String filename) {
    int i = filename.lastIndexOf('.');
    if (i >= 0) return filename.substring(i+1).toLowerCase();
    return "";
  }

  private static TRS readInput(String file) throws Exception {
    String extension = getExtension(file);
    if (extension.equals("trs")) return OCocoInputReader.readTrsFromFile(file);
    else if (extension.equals("itrs")) return ITrsInputReader.readTrsFromFile(file);
    else return CoraInputReader.readTrsFromFile(file);
  }

  private static ProofObject executeRequest(TRS trs) {
    if (_request == null || _request.toLowerCase().equals("termination")) {
      return TerminationHandler.proveTermination(trs);
    }
    else if (_request.toLowerCase().equals("horpo")) {
      return TerminationHandler.proveHorpoTermination(trs);
    }
    else if (_request.length() > 6 && _request.toLowerCase().substring(0,6).equals("reduce")) {
      String reduceme = _request.substring(7);
      Term start = CoraInputReader.readTerm(reduceme, trs);
      Reducer reducer = new Reducer(trs);
      return reducer.normalise(start);
    }
    return null;
  }

  public static void main(String[] args) {
    readParameters(args);
    if (_inputFile == null) {
      System.out.println("Please supply an input file.");
      return;
    }

    try {
      TRS trs = readInput(_inputFile);
      if (trs == null) return;
      ProofObject pobject = executeRequest(trs);
      System.out.println(pobject.queryAnswer());
      OutputModule om = DefaultOutputModule.createDefaultModule(trs);
      pobject.justify(om);
      om.printToStdout();
    }
    catch (Exception e) {
      System.out.println(e.getMessage());
      System.exit(1);
    }
    catch (ParseError e) {
      System.out.println(e.getMessage());
      System.exit(1);
    }
    catch (Error e) {
      System.out.println("Encountered an error:\n" + e.getMessage());
      e.printStackTrace();
      System.exit(1);
    }
  }
/*
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
*/
}
