/**************************************************************************************************
 Copyright 2022 Cynthia Kop 

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the 
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import org.junit.Test;
import static org.junit.Assert.*;

public class PositionTest {
  @Test
  public void testEmpty() {
    Position pos = new EmptyPosition();
    assertTrue(pos.toString().equals("ε"));
    assertTrue(pos.equals(new EmptyPosition()));
    assertTrue(pos.queryArgumentPosition() == -1);
    assertTrue(pos.queryTail() == null);
    assertTrue(pos.isEmpty());
  }

  @Test
  public void testArgument() {
    Position pos = new ArgumentPosition(0, new ArgumentPosition(37, new EmptyPosition()));
    assertTrue(pos.toString().equals("0.37.ε"));
    assertTrue(pos.queryArgumentPosition() == 0);
    assertTrue(pos.queryTail().queryArgumentPosition() == 37);
    assertFalse(pos.isEmpty());
  }
}

