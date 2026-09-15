/**************************************************************************************************
 Copyright 2025--2026 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.types;

import java.util.Objects;
import java.util.Set;
import charlie.util.NullStorageException;
import charlie.util.FixedList;

/**
 * A data type is built by a sort constructor applied to one or more arguments.
 * We do not consider data types as simple types, but for techniques that are defined only for
 * systems with simple types, we can view data types as a kind of sort, essentially flattening
 * the whole type into its representative string and viewing it as a base type.
 */
public record Data(String name, FixedList<Type> args) implements Type {
  public Data {
    if (name == null) throw new NullStorageException("Data", "name");
    if (args == null) throw new NullStorageException("Data", "arguments list");
    if (args.isEmpty()) throw new IllegalArgumentException("arguments list is empty; " +
      "to create a data type with no arguments, you should construct a Base instead");
  }

  @Override
  public boolean isDataType() {
    return true;
  }

  @Override
  public boolean isSort() {
    return true;
  }

  @Override
  public boolean isSimple() {
    return false;
  }

  @Override
  public boolean isZeroSort() {
    return args.stream().allMatch(Type::isZeroSort);
  }

  @Override
  public boolean isMonomorphic() {
    return args.stream().allMatch(Type::isMonomorphic);
  }

  @Override
  public int queryNumberSubtypes() {
    return this.args.size();
  }

  @Override
  public Type querySubtype(int index) {
    if (index <= 0 || index > this.args.size()) {
      throw new IndexOutOfBoundsException("Data::querySubtype called with index " + index +
        "on type [" + toString() + "] with " + this.args.size() + " elements.");
    }
    return this.args.get(index-1);
  }

  @Override
  public int queryTypeOrder() {
    return this.args.stream().map(Type::queryTypeOrder).reduce(0, (n,m) -> Math.max(n,m));
  }

  @Override
  public void storeTypeVariables(Set<TVar> storage) {
    for (Type arg : this.args) arg.storeTypeVariables(storage);
  }

  @Override
  public Type substitute(ISubstitution typeSubstitution) {
    FixedList.Builder<Type> argsBuilder = new FixedList.Builder<Type>();
    for (Type arg : this.args) argsBuilder.add(arg.substitute(typeSubstitution));
    return new Data(this.name, argsBuilder.build());
  }

  @Override
  public boolean match(Type other, MSubstitution typeSubstitution) {
    if (other instanceof Data(String n, FixedList<Type> l)) {
      if (!this.name.equals(n) || this.args.size() != l.size()) return false;
      for (int i = 0; i < this.args.size(); i++) {
        if (!this.args.get(i).match(l.get(i), typeSubstitution)) return false;
      }
      return true;
    }
    return false;
  }

  @Override
  public int compareTo(Type other) {
    if (other instanceof Data(String n, FixedList<Type> l)) {
      int k = this.name.compareTo(n);
      if (k == 0) k = this.args.size() - l.size();
      if (k != 0) return k;
      for (int i = 0; i < this.args.size(); i++) {
        k = this.args.get(i).compareTo(l.get(i));
        if (k != 0) return k;
      }
      return 0;
    }
    return 1;
  }

  @Override
  public String toString() {
    return TypePrinter.DEBUGPRINTER.print(this);
  }

  @Override
  public int hashCode() {
    return Objects.hash(this.name, this.args);
  }

  @Override
  public boolean equals(Type type) {
    if (type instanceof Data(String n, FixedList<Type> argTypes)) {
      return this.name.equals(n) && this.args.equals(argTypes);
    }
    return false;
  }

  @Override
  public boolean equals(Object other) {
    return other instanceof Type t && equals(t);
  }
}
