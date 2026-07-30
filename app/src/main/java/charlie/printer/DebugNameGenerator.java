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

package charlie.printer;

import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Variable;
import charlie.terms.NameGenerator;

/**
 * The DebugNameGenerator is a NameGenerator that prints all replaceables by their actual index.
 * This makes it much easier to see when two variables are different, though it makes it harder to
 * predict what the variables will be called!
 */
public class DebugNameGenerator extends NameGenerator {
  public DebugNameGenerator() {
    super();
  }

  @Override
  protected String chooseNameForUniqueReplaceable(Replaceable r, String name) {
    return freeName(r);
  }

  @Override
  protected String chooseNameForAmbiguousReplaceable(Replaceable r, String name, int index) {
    return freeName(r);
  }

  @Override
  public String generateBoundName(MutableRenaming renaming, Variable binder) {
    String name = boundName(binder);
    renaming.setName(binder, name);
    return name;
  }

  private String freeName(Replaceable x) {
    String start = switch(x.queryReplaceableKind()) {
      case Replaceable.Kind.BINDER -> "I";
      case Replaceable.Kind.BASEVAR -> "V";
      case Replaceable.Kind.METAVAR -> "M";
    };
    return start + x.queryName() + "." + x.queryIndex();
  }

  private String boundName(Replaceable x) {
    return "B" + x.queryName() + "." + x.queryIndex();
  }
}

