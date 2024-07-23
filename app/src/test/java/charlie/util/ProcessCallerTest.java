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

package charlie.util;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

/**
 * A helper class for manually testing the process caller.
 * (Do not automatically test it! Outside processes should not be called routinely during testing.)
 */
class ProcessCallerTest {
  /** @Test deliberately disabled.  Enable if you want to run the test. */
  //@Test
  void callingTest() {
    List<String> commands = new ArrayList<>(Arrays.asList("z3", "--version"));
    ProcessCaller pc = new ProcessCaller(commands, 1);
    try {
      Optional<String> result = pc.getResultAsString();
      System.out.println(result);
    }
    catch (Exception e) {
      System.out.println(e.getMessage());
      e.printStackTrace();
      assertTrue(false);
    }
  }

  @Test
  void ProcessCallerOSSupportedTest() {
    assertTrue(SystemUtils.isOSSupported());
  }
}
