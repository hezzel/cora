/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.immutabledata;

import java.util.ArrayList;
import cora.interfaces.FunctionSymbol;
import cora.interfaces.Term;

public class FunctionalTerm implements Term {
  private FunctionSymbol _root;
  private ArrayList<Term> _args;

  public FunctionalTerm(FunctionSymbol root, ArrayList<Term> args) {
    _root = root;
    _args = new ArrayList<Term>(args);
  }

  public TermKind queryTermKind() {
    return TermKind.FUNCTIONALTERM;
  }

  public String toString() {
    String ret = _root.toString() + "(";
    for (int i = 0; i < _args.size(); i++) {
      if (i != 0) ret += ", ";
      ret += _args.get(i).toString();
    }
    ret += ")";
    return ret;
  }
}

