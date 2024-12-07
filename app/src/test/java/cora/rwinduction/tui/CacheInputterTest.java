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

package cora.rwinduction.tui;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;

class CacheInputterTest {
  @Test
  public void testInputter() {
    CacheInputter inputter = new CacheInputter();
    inputter.cache("A");
    inputter.cache("B");
    inputter.cache("C");
    assertTrue(inputter.readLine().equals("C"));
    assertTrue(inputter.readLine("prompt").equals("B"));
    inputter.cache("D");
    assertTrue(inputter.readLine("").equals("D"));
    assertTrue(inputter.readLine().equals("A"));
    assertTrue(inputter.readLine().equals(":quit"));
    assertTrue(inputter.readLine().equals(":quit"));
  }

  @Test
  public void testCacheOnCache() {
    CacheInputter ainp = new CacheInputter();
    ainp.cache("A");
    CacheInputter binp = new CacheInputter(ainp);
    binp.cache("B");
    ainp.cache("C");
    ainp.cache("D");
    assertTrue(binp.readLine().equals("B"));
    assertTrue(binp.readLine().equals("D"));
    assertTrue(ainp.readLine().equals("C"));
    assertTrue(binp.readLine().equals("A"));
    assertTrue(binp.readLine().equals(":quit"));
  }

  @Test
  public void testCacheWithList() {
    Inputter inp = new CacheInputter(List.of("A", "B", "C"),
                      new CacheInputter(List.of("D"), new QuitInputter()));
    assertTrue(inp.readLine().equals("A"));
    assertTrue(inp.readLine().equals("B"));
    assertTrue(inp.readLine().equals("C"));
    assertTrue(inp.readLine().equals("D"));
    assertTrue(inp.readLine().equals(":quit"));
  }
}

