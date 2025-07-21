/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine.deduction;

import java.util.ArrayList;
import java.util.Optional;
import charlie.util.Pair;
import charlie.terms.Renaming;
import charlie.terms.Replaceable;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/** The variant of Alter that is only used to change the names of variables. */
public final class DeductionAlterRename extends DeductionStep {
  private ArrayList<Pair<String,String>> _assignments;
  private Renaming _newRenaming;

  /** Creates the step, claiming the arguments as its own property. */
  private DeductionAlterRename(ProofState state, ProofContext context,
                               ArrayList<Pair<String,String>> assignments, Renaming renaming) {
    super(state, context);
    _assignments = assignments;
    _newRenaming = renaming;
  }

  /**
   * Creates a step to do the given renamings, or returns null if that fails.
   *
   * This will only succeed if the given names actually occur in the top equation's renaming, and
   * the new names do not.  The reassignments are parsed from start to finish, though: given an
   * equation that contains the variables x and z, the renaming x = y, z = x *is* allowed because
   * x is renamed before z.
   */
  public static DeductionAlterRename createStep(PartialProof proof, Optional<OutputModule> module,
                                                ArrayList<Pair<String,String>> mapping) {
    ProofState state = proof.getProofState();
    Renaming renaming = state.getTopEquation().getRenamingCopy();
    for (Pair<String,String> pair : mapping) {
      String original = pair.fst();
      String newname = pair.snd();

      Replaceable x = renaming.getReplaceable(original);
      if (x == null) {
        module.ifPresent(o -> o.println("Unknown variable name: %a.", original));
        return null;
      }

      if (original.equals(newname)) {
        module.ifPresent(o -> o.println("Cannot rename variable %a to itself.", original));
        return null;
      }

      if (renaming.getReplaceable(newname) != null) {
        module.ifPresent(o -> o.println("The name %a is already in use.", newname));
        return null;
      }

      if (!renaming.setName(x, newname)) {
        module.ifPresent(o -> o.println("The name %a is not available.", newname));
        return null;
      }
    }

    if (mapping.isEmpty()) {
      module.ifPresent(o -> o.println("Nothing given to rename."));
      return null;
    }

    return new DeductionAlterRename(state, proof.getContext(), mapping, renaming);
  }

  /** There's nothing heavy to check: if we can create this step, we can execute it. */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    return true;
  }

  /** Apply the deduction rule to the current proof state */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    return _state.replaceTopEquation(_state.getTopEquation().replace(
      _state.getTopEquation().getEquation(), _newRenaming, _state.getLastUsedIndex() + 1));
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("alter rename ");
    for (int i = 0; i < _assignments.size(); i++) {
      if (i != 0) printer.add(", ");
      printer.add(_assignments.get(i).fst(), " := ", _assignments.get(i).snd());
    }
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.print("We apply ALTER to rename variables using the substitution [");
    for (int i = 0; i < _assignments.size(); i++) {
      if (i != 0) module.print(", ");
      module.print("%a := %a", _assignments.get(i).fst(), _assignments.get(i).snd());
    }
    module.println("].");
  }
}

