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

package cora.rwinduction;

import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.rwinduction.tui.*;
import java.util.List;

public class InteractiveRewritingInducter {
  private Inputter _input;
  private OutputModule _output;

  InteractiveRewritingInducter(Inputter input, OutputModule output) {
    _input = input;
    _output = output;
  }

  public static ProofObject run(List<String> inputs, OutputModule output) {
    Inputter inputter = new BasicInputter();
    //Inputter inputter = new ReplInputter();
    InteractiveRewritingInducter inducter = new InteractiveRewritingInducter(inputter, output);

    inducter.test();

    return null;
  }

  private void test() {
    while (true) {
      String str = _input.readLine("Next line please: ");
      if (str.equals(":quit")) {
        _input.close();
        return;
      }
      _output.println("I read: %a", str);
      _output.printToStdout();
      _output.clear();
    }
  }
}

