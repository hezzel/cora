/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.smt;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;

public class MultiplicationTest {
  @Test
  public void testStaggeredCreation() {
    Multiplication prod = new Multiplication(new IValue(3),
      new Multiplication(new Addition(new IVar(12), new IVar(13)), new IValue(-2)));
    assertTrue(prod.numChildren() == 3);
    assertTrue(prod.queryChild(1).equals(new IValue(3)));
    assertTrue(prod.queryChild(2).equals(new Addition(new IVar(12), new IVar(13))));
    assertTrue(prod.queryChild(3).equals(new IValue(-2)));
  }

  @Test
  public void testToString() {
    ArrayList<IntegerExpression> args = new ArrayList<IntegerExpression>();
    args.add(new IValue(-3));
    args.add(new IValue(7));
    args.add(new IVar(0));
    IntegerExpression prod = new Multiplication(args);
    assertTrue(prod.toString().equals("(* (- 3) 7 i0)"));
  }

  @Test
  public void testLegalEvaluate() {
    IntegerExpression prod =
      new Multiplication(new IValue(3), new Multiplication(new IValue(12), new IValue(-2)));
    assertTrue(prod.evaluate() == -72);
  }

  @Test(expected = cora.exceptions.IndexingError.class)
  public void testQueryZeroChild() {
    Multiplication prod = new Multiplication(new IValue(0), new IVar(2));
    prod.queryChild(0);
  }

  @Test(expected = cora.exceptions.IndexingError.class)
  public void testQueryTooLargeChild() {
    Multiplication prod = new Multiplication(new IValue(0), new IVar(2));
    prod.queryChild(3);
  }
}
