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

package cora.rwinduction.command;

import java.util.ArrayList;
import charlie.util.FixedList;
import charlie.trs.IllegalRuleException;
import charlie.trs.Rule;
import charlie.trs.TrsFactory;
import charlie.trs.TRS;
import charlie.printer.Printer;
import cora.io.ProofObject;
import cora.io.OutputModule;
import cora.termination.TerminationHandler;
import cora.rwinduction.engine.OrdReq;
import cora.rwinduction.engine.ProofState;
import cora.rwinduction.parser.CommandParsingStatus;

/**
 * The environment command :check, which runs a termination check on the current ordering
 * requirements.
 */
public class CommandCheck extends Command {
  @Override
  public String queryName() {
    return ":check";
  }

  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of(":check", ":check brief", ":check verbose");
  }

  @Override
  public void printHelp(OutputModule module) {
    module.println("Checks if the ordering requirements so far are satisfied.  This is not " +
      "complete: there may be false negatives.  But if this answers that the requirements are " +
      "satisfiable, they are.");
    module.println("The verbosity parameter indicates whether the full proof should be printed.  " +
      "By default, it is not.");
  }

  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    ret.add(endOfCommandSuggestion());
    if (!args.equals("")) return ret;// they already gave one argument; we don't need another
    ret.add(new TabSuggestion("brief", "keyword"));
    ret.add(new TabSuggestion("verbose", "keyword"));
    return ret;
  }

  @Override
  protected boolean run(CommandParsingStatus input) {
    String txt = input.nextWord();
    int brevity;
    if (txt == null || txt.equals("")) brevity = 1;
    else if (txt.equals("brief")) brevity = 0;
    else if (txt.equals("verbose")) brevity = 2;
    else {
      _module.println("Illegal argument: %a", txt);
      return false;
    }
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: :check takes at most 1 argument.",
        input.currentPosition());
      return false;
    }

    if (brevity > 0) _module.println("Sending proof request to termination checker...");
    ProofObject po = createTerminationProof();
    switch (po.queryAnswer()) {
      case ProofObject.Answer.YES:
        _module.println("The current set of ordering requirements is indeed orientable.");
        if (_proof.isFinal()) _proof.finish(po);
        break;
      default:
        _module.println("Failed to find a proof that the current set of ordering requirements " +
          "is orientable.  You may need to use a more sophisticated approach.");
    }
    if (brevity >= 2) po.justify(_module);
    return true;
  }

  /** This does a proof attempt for termination, and returns the result. */
  private ProofObject createTerminationProof() {
    ArrayList<Rule> rules = new ArrayList<Rule>();
    for (Rule rule : _proof.getContext().getTRS().queryRules()) rules.add(rule);
    for (OrdReq req : _proof.getProofState().getOrderingRequirements()) {
      try { rules.add(makeRule(req)); }
      catch (IllegalRuleException e) {
        return new ProofObject() {
          public Answer queryAnswer() { return Answer.MAYBE; }
          public void justify(OutputModule out) {
            out.println("Failed to transform ordering requirement %a into a rule: %a.", req,
              Printer.makePrintable(e, req.queryRenaming()));
          }
        };
      }
    }
    TRS trs = _proof.getContext().getTRS().createDerivative(rules);
    return TerminationHandler.proveTermination(trs);
  }

  private Rule makeRule(OrdReq req) {
    return TrsFactory.createRule(req.getLhs(), req.getRhs(), req.getConstraint());
  }
}

