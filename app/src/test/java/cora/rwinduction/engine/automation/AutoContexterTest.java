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

package cora.rwinduction.engine.automation;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;

import charlie.util.Pair;
import charlie.terms.position.Position;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.ProofContext;

class AutoContextTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "end :: Int -> Tree\n" +
      "cons :: Tree -> Tree -> Tree\n" +
      "merge :: Tree -> Tree -> Tree\n" +
      "merge(x, y) -> cons(x, y)\n"
    );
  }

  @Test
  public void testDifferences() {
    TRS trs = setupTRS();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Variable f = TermFactory.createVar("F", CoraInputReader.readType("Tree -> Tree -> Tree"));
    renaming.setName(f, "F");
    Term s = CoraInputReader.readTermAndUpdateNaming("cons(cons(cons(end(1), end(2)), " +
      "cons(end(3), merge(end(4), end(5)))), cons(end(6), y))", renaming, trs);
    Term t = CoraInputReader.readTermAndUpdateNaming("cons(cons(cons(end(1), end(i)), " +
      "F(end(3), cons(end(4), end(5)))), cons(y, end(7)))", renaming, trs);
    ArrayList<Position> posses = new ArrayList<Position>();
    ArrayList<Pair<Term,Term>> pairs = new ArrayList<Pair<Term,Term>>();
    AutoContexter.storeDifferences(s, t, new ProofContext(trs, lst -> renaming), posses, pairs);
    assertTrue(posses.size() == 4);
    assertTrue(pairs.size() == 4);

    assertTrue(posses.get(0).toString().equals("1.1.2.1"));
    assertTrue(pairs.get(0).fst().toString().equals("2"));
    assertTrue(pairs.get(0).snd().toString().equals("i"));

    assertTrue(posses.get(1).toString().equals("1.2"));
    assertTrue(pairs.get(1).fst().toString().equals("cons(end(3), merge(end(4), end(5)))"));
    assertTrue(pairs.get(1).snd().toString().equals("F(end(3), cons(end(4), end(5)))"));

    assertTrue(posses.get(2).toString().equals("2.1"));
    assertTrue(pairs.get(2).fst().toString().equals("end(6)"));
    assertTrue(pairs.get(2).snd().toString().equals("y"));

    assertTrue(posses.get(3).toString().equals("2.2"));
    assertTrue(pairs.get(3).fst().toString().equals("y"));
    assertTrue(pairs.get(3).snd().toString().equals("end(7)"));
  }
}

