/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.smt;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class SValueTest {
  @Test
  public void testBasics() {
    SValue x = new SValue("test");
    assertTrue(x.evaluate().equals("test"));
    assertTrue(x.toString().equals("\"test\""));
    assertTrue(x.toSmtString().equals("\"test\""));
  }

  @Test
  public void testComparison() {
    SValue x = new SValue("bca");
    
    assertTrue(x.compareTo(new SValue("bca")) == 0);
    assertTrue(x.equals(new SValue("bca")));
    assertTrue(x.hashCode() == (new SValue("bca")).hashCode());

    assertTrue(x.compareTo(new SValue("abc")) > 0);
    assertFalse(x.equals(new SValue("abc")));
    assertTrue(x.hashCode() != (new SValue("abc")).hashCode());

    assertTrue(x.compareTo(new SValue("cab")) < 0);
    assertFalse(x.equals(new SValue("cab")));
  }

  @Test
  public void testEncode() {
    assertTrue(SValue.encode("abcd").equals("\"abcd\""));
    assertTrue(SValue.encode("abc\nd").equals("\"abc\\u{a}d\""));
    assertTrue(SValue.encode("∀∃1 →").equals("\"\\u{2200}\\u{2203}1 \\u{2192}\""));
    SValue x = new SValue("∀");
    assertTrue(x.toString().equals("\"\\u{2200}\""));
    assertTrue(x.toSmtString().equals("\"\\u{2200}\""));
  }
}
