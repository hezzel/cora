/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

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

import charlie.exceptions.ParseException;
import charlie.terms.Term;
import charlie.terms.TermFactory;
import charlie.trs.*;
import charlie.reader.*;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.smt.InternalSolverHandler;
import cora.reduction.Reducer;
import cora.termination.TerminationHandler;
import cora.Parameters.Request;

import java.io.IOException;
import java.io.File;
import java.nio.file.*;
import java.util.List;
import java.util.TreeSet;
import java.util.Set;

/** Basic entry class: this reads a TRS and asks the user for a term, then reduces this term. */
public class App {
  /** Main function: parses the parameters and starts up the program flow. */
  public static void main(String[] args) {
    try {
      Parameters parameters = new Parameters(args);
      parameters.setupSettings();
      Request req = parameters.queryRequest();
      TRS trs = readTRS(parameters.querySingleFile());
      ProofObject pobject = executeRequest(req, trs, parameters.queryModuleInput());
      if (pobject == null) System.exit(1);
      System.out.println(pobject.printAnswer());
      OutputModule om = parameters.queryOutputModule(trs);
      pobject.justify(om);
      om.printToStdout();
    }
    catch (Parameters.WrongParametersException e) {
      System.out.println(e.getMessage());
      System.exit(0);
    }
    catch (Exception e) {
      System.out.println("Encountered an error:\n" + e.getMessage());
      e.printStackTrace();
      System.exit(1);
    }
    catch (Error e) {
      System.out.println("Encountered an error:\n" + e.getMessage());
      e.printStackTrace();
      System.exit(1);
    }
  }

  /** Reads the given file as a TRS, and handles errors if they should arise. */
  private static TRS readTRS(String file) {
    try { return readInput(file); }
    catch (IOException e) {
      System.out.println(e.getMessage());
      System.exit(1);
    }
    catch (ParseException e) {
      System.out.println(e.getMessage());
      System.exit(1);
    }
    return null;
  }

  /** Reads the given file as a TRS */
  public static TRS readInput(String file) throws IOException {
    String extension = getExtension(file);
    if (extension.equals("trs")) return OCocoInputReader.readTrsFromFile(file);
    else if (extension.equals("itrs")) return ITrsInputReader.readTrsFromFile(file);
    else if (extension.equals("smt")) return readSmt(file);
    else return CoraInputReader.readTrsFromFile(file);
  }

  /** Determines the extension of a given filename ("" if it has no extension) */
  private static String getExtension(String filename) {
    int i = filename.lastIndexOf('.');
    if (i >= 0) return filename.substring(i+1).toLowerCase();
    return "";
  }

  /**
   * This function executes the given request on the given TRS, and returns the resulting proof
   * object.
   * (This only considers the requests that take a TRS as argument and return a Proof Object.)
   */
  private static ProofObject executeRequest(Request request, TRS trs, List<String> moduleInput) {
    return switch (request) {
      case Computability -> TerminationHandler.proveComputability(trs);
      case Smt -> InternalSolverHandler.proveSatisfiability(trs.queryRule(0).queryConstraint());
      case Print -> new ProofObject() {
        public Answer queryAnswer() { return Answer.YES; }
        public String printAnswer() { return ""; }
        public void justify(OutputModule o) { o.printTrs(trs); }
      };
      case Termination -> TerminationHandler.proveTermination(trs);
      case Reduce -> executeReduce(trs, moduleInput);
    };
  }

  /** Helper function for executeRequest: executes a Reduce request */
  private static ProofObject executeReduce(TRS trs, List<String> moduleInput) {
    if (moduleInput.size() != 1) {
      throw new RuntimeException("Parameters did not supply an input term!");
    }
    String txt = moduleInput.get(0);
    Term start;
    try { start = CoraInputReader.readTerm(txt, trs); }
    catch (ParseException e) {
      System.out.println("Exception reading input term " + txt + ":\n" + e.getMessage());
      return null;
    }
    Reducer reducer = new Reducer(trs);
    return reducer.normalise(start);
  }

  /**
   * Helper function for this temporary branch: this reads an SMT formula straight from a file.
   * It wraps it up as a TRS because that's convenient in the program flow.
   * Once all the testing is done, the Smt option should probably be removed altogether.
   */
  private static TRS readSmt(String file) throws IOException {
    Term formula = CoraInputReader.readFormulaFromFile(file);
    Alphabet alphabet = new Alphabet(Set.of());
    Term start = TermFactory.createConstant("start", 0);
    Rule rule = TrsFactory.createRule(start, start, formula);
    return TrsFactory.createTrs(alphabet, List.of(rule), TrsFactory.CORA);
  }
}

