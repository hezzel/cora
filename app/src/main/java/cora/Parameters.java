/**************************************************************************************************
 Copyright 2024 Cynthia Kop

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

import java.util.ArrayList;
import java.util.List;
import java.util.Collections;
import java.util.TreeSet;
import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.config.Settings;

/**
 * This object parses runtime parameters, to represent them in an easily queryable format.
 */
public class Parameters {
  private ArrayList<String> _files;
  private ArrayList<String> _input;
  private TreeSet<String> _disable;
  private OutputModule.Style _style;
  private Request _request;

  public enum Request { Print, Reduce, Termination, Computability };
  public class WrongParametersError extends Error {
    public WrongParametersError(String reason) { super("PARAMETERS ERROR: " + reason); }
  }

  /**
   * To make it possible to disable a technique using -d, do the following:
   * - The relevant class should implement:
   *     public static String queryDisabledCode()
   *   This should return a unique string identifying the technique.
   * - Add a call to the disableableTechniques() function to call queryDisabledCode() on the class.
   * - Add the code to the documentation.
   * - Add code in the primary access function for your technique to abort if
   *   config.Settings.disabled contains that code.
   *
   * Obviously, if you want to remove the code, you should reverse all four steps.
   *
   * If you _change_ the code, everything will keep working (assuming it doesn't overlap with
   * another code), so please make sure you do not forget to also change the documentation!
   */
  private TreeSet<String> disableableTechniques() {
    TreeSet<String> set = new TreeSet<String>();
    addTechnique(set, cora.termination.dependency_pairs.DPFramework.queryDisabledCode());
    addTechnique(set, cora.termination.dependency_pairs.processors.GraphProcessor.queryDisabledCode());
    addTechnique(set, cora.termination.dependency_pairs.processors.KasperProcessor.queryDisabledCode());
    addTechnique(set, cora.termination.dependency_pairs.processors.ReachabilityProcessor.queryDisabledCode());
    addTechnique(set, cora.termination.dependency_pairs.processors.SplittingProcessor.queryDisabledCode());
    addTechnique(set, cora.termination.dependency_pairs.processors.SubtermProcessor.queryDisabledCode());
    addTechnique(set, cora.termination.dependency_pairs.processors.TheoryArgumentsProcessor.queryDisabledCode());
    addTechnique(set, cora.termination.reduction_pairs.Horpo.queryDisabledCode());
    return set;
  }

  /** Helper function for disableableTechniques() */
  private static void addTechnique(TreeSet<String> set, String value) {
    if (set.contains(value)) {
      throw new Error("Disable value " + value + " is used by more than one technique!");
    }
    set.add(value);
  }

  /** Creates the Parameters object based on user-given runtime arguments. */
  public Parameters(String[] args) {
    _files = new ArrayList<String>();
    _input = new ArrayList<String>();
    _disable = new TreeSet<String>();
    _style = null;
    _request = null;

    for (int i = 0; i < args.length; ) {
      i = handleArgument(args, i);
    }

    if (_request == null) _request = Request.Termination;
  }

  /**
   * Helper function for the constructor.  This reads the given argument and any subseqent arguments
   * that belong with it, and returns the index of the argument we should consider next (which is
   * always greater than index).
   */
  private int handleArgument(String[] args, int index) {
    String arg = args[index];

    switch (arg) {
      case "-c": case "--computability":
        setRequest(Request.Computability);
        return index+1;
      case "-d": case "--disable":
        if (index + 1 == args.length) {
          throw new WrongParametersError("Parameter " + arg + " without anything to disable!");
        }
        for (String s : args[index+1].split(",")) _disable.add(s);
        return index+2;
      case "-p": case "--print":
        setRequest(Request.Print);
        return index+1;
      case "-y": case "--style":
        if (index + 1 == args.length) {
          throw new WrongParametersError("Parameter " + arg + " without given style!");
        }
        if (_style != null) throw new WrongParametersError("Two style parameters are given.");
        String st = args[index+1].toLowerCase();
        if (st.equals("plain")) _style = OutputModule.Style.Plain;
        else if (st.equals("unicode")) _style = OutputModule.Style.Unicode;
        else throw new WrongParametersError("Unknown style: " + args[index+1]);
        return index + 2;
      case "-r": case "--reduce":
        setRequest(Request.Reduce);
        String trm = "";
        for (index++; index < args.length; index++) trm += args[index];
        if (!trm.equals("")) _input.add(trm);
        return args.length;
      case "-t": case "--termination":
        setRequest(Request.Termination);
        return index+1;
      default:
        if (arg.length() == 0) return index+1;
        if (arg.charAt(0) == '-') {
          throw new WrongParametersError("Unknown runtime argument: " + arg + ".");
        }
        _files.add(arg);
        return index+1;
      }
  }

  /**
   * Sets the given request, if none has been set yet.  If one has already been set, a
   * WrongParametersError is thrown instead.
   */
  private void setRequest(Request req) {
    if (_request == null) _request = req;
    else if (_request != req) {
      throw new WrongParametersError("Cannot set request both to " + _request +  " and to " +
        req + ".");
    }
  }

  /** Sets up config.Settings based on what the input arguments were. */
  public void setupSettings() {
    TreeSet<String> codes = disableableTechniques();
    for (String d : _disable) {
      if (!codes.contains(d)) {
        throw new WrongParametersError("Unknown code for technique to disable: " + d);
      }
    }
    Settings.disabled = new TreeSet<String>(_disable);
  }

  /** Returns the task Cora is set to do. */
  public Request queryRequest() {
    return _request;
  }

  /** 
   * This verifies that the user supplied exactly one file (if not, a WrongParameterError is thrown)
   * and if so, returns it.
   */
  public String querySingleFile() {
    if (_files.size() == 0) throw new WrongParametersError("No input file given!");
    if (_files.size() >= 2) {
      throw new WrongParametersError("More than one input file given! " +
        "(" + _files.get(0) + " and " + _files.get(1) + ")");
    }
    return _files.get(0);
  }

  /** For commands that allow multiple files as input, this returns all the files we read. */
  public List<String> queryFiles() {
    return Collections.unmodifiableList(_files);
  }

  /**
   * This returns the extra parameters that the user supplied as input to whatever request they
   * made.
   */
  public List<String> queryModuleInput() {
    return Collections.unmodifiableList(_input);
  }

  /** This returns the OutputModule to be used for printing, once the given TRS is loaded. */
  public OutputModule queryOutputModule(TRS trs) {
    return switch (_style) {
      case null -> DefaultOutputModule.createDefaultModule(trs);
      case OutputModule.Style.Plain -> DefaultOutputModule.createPlainModule(trs);
      case OutputModule.Style.Unicode -> DefaultOutputModule.createUnicodeModule(trs);
    };
  }

  /**
   * This returns the OutputModule to be used for printing, when there is no TRS.  Note that if a
   * TRS is loaded, this may not properly print terms (if there is an overlap between variable and
   * function names).
   */
  public OutputModule queryOutputModule() {
    return switch (_style) {
      case null -> DefaultOutputModule.createDefaultModule();
      case OutputModule.Style.Plain -> DefaultOutputModule.createPlainModule();
      case OutputModule.Style.Unicode -> DefaultOutputModule.createUnicodeModule();
    };
  }
}
