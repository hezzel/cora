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

import java.util.Set;
import charlie.util.NullStorageException;

/**
 * A type variable is a placeholder that can be instantiated by any other type.
 * Type variables are uniquely identified by their name; hence, creating multiple variables with
 * the same name yields instances of the same variable.
 */
public record TVar(String name) implements Type {
  public TVar {
    if (name == null) {
      throw new NullStorageException("TVar", "name");
    }   
  }

  @Override
  public boolean isVariableType() { return true; }

  @Override
  public boolean isSort() { return false; }

  @Override
  public boolean isSimple() { return false; }

  @Override
  public boolean isZeroSort() { return false; }

  @Override
  public boolean isMonomorphic() { return false; }

  @Override
  public int queryNumberSubtypes() { return 0; }

  @Override
  public Type querySubtype(int index) {
    throw new IndexOutOfBoundsException("TVar::subtype called (with index " + index + ")");
  }

  @Override
  public int queryTypeOrder() { return Integer.MAX_VALUE; }

  @Override
  public void storeTypeVariables(Set<TVar> storage) { storage.add(this); }

  @Override
  public Type substitute(ISubstitution typeSubstitution) {
    Type ret = typeSubstitution.get(this);
    if (ret == null) return this;
    else return ret;
  }

  @Override
  public boolean match(Type other, MSubstitution typeSubstitution) {
    Type mapped = typeSubstitution.get(this);
    if (mapped == null) return typeSubstitution.extend(this, other);
    return other.equals(mapped);
  }

  @Override
  public int compareTo(Type other) {
    return switch(other) {
      case Base(String n) -> 1;
      case TVar(String n) -> this.name.compareTo(n);
      default -> -1;
    };
  }

  @Override
  public String toString(){
    return "$" + name;
  }

  @Override
  public int hashCode() { return name.hashCode(); }

  @Override
  public boolean equals(Type type) {
    if (type instanceof TVar(String othername)) return this.name.equals(othername);
    return false;
  }

  @Override
  public boolean equals(Object other) {
    return other instanceof Type t && equals(t);
  }
}

