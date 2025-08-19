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

package charlie.terms.replaceable;

import java.util.Set;

/**
 * An ImmutableRenaming is a Renaming that cannot be altered by objects that it is given to.
 * The underlying MutableRenaming can still be altered by its owner, but by using an immutability
 * wrapper, one may ensure that other objects can only use it as intended.
 */
public class ImmutableRenaming implements Renaming {
  private MutableRenaming _wrapped;

  // the constructor is not public, since we should be created through makeImmutable()
  ImmutableRenaming(MutableRenaming wrapme) { _wrapped = wrapme; }

  public Set<Replaceable> domain() { return _wrapped.domain(); }
  public Set<String> range() { return _wrapped.range(); }
  public String getName(Replaceable x) { return _wrapped.getName(x); }
  public Replaceable getReplaceable(String name) { return _wrapped.getReplaceable(name); }
  public MutableRenaming copy() { return _wrapped.copy(); }
  public Renaming makeImmutable() { return this; }
}

