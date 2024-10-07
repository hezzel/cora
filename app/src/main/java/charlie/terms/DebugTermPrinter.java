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

package charlie.terms;

import java.util.Arrays;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import java.util.function.Predicate;
import charlie.exceptions.UnexpectedPatternException;

/**
 * The DebugTermPrinter is a term printer that prints all replaceables by their actual index.
 * This makes it much easier to see when two variables are different, though it makes it harder to
 * predict what the variables will be called!
 */
public class DebugTermPrinter extends TermPrinter {
  public DebugTermPrinter() {
    super(Set.of());
  }

  /**
   * This function generates the name <kindchar><name><index> for the given replaceable.  The
   * "available" predicate, count and num are ignored, since this name should be inherently
   * unique.
   */
  protected String generateName(Replaceable x, Predicate<String> available, int count, int num) {
    String start = switch(x.queryReplaceableKind()) {
      case Replaceable.KIND_BINDER -> "B";
      case Replaceable.KIND_BASEVAR -> "V";
      case Replaceable.KIND_METAVAR -> "M";
      default -> "?";
    };
    return start + x.queryName() + "." + x.queryIndex();
  }
}

