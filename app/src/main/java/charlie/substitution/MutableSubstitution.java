/**************************************************************************************************
 Copyright 2019--2026 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.substitution;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;
import charlie.util.NullStorageException;
import charlie.types.TVar;
import charlie.types.Type;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.*;

/**
 * A MutableSubstitution is a substitution that can have mappings added over time.
 * This includes both (meta-)variable and type-variable mappings.
 * For meta-variable mappings (but not for type variables), existing mappings may also be replaced
 * and deleted.
 *
 * POLYMORPHISM NOTE: The substitution always maintains the invariant that if a variable occurs in
 * the domain, then so does every type variable in its type.  This is why replacement of existing
 * mappings cannot be done for type variables, as it would interfere with this property.
 */
public class MutableSubstitution implements Substitution, Type.MSubstitution {
  private HashMap<Replaceable,Term> _mapping;
  private final HashMap<TVar,Type> _typeMapping;

  /**
   * Creates an empty mutable substitution, with neither variables nor type variables in its
   * domain.
   */
  public MutableSubstitution() {
    _mapping = new HashMap<Replaceable,Term>();
    _typeMapping = new HashMap<TVar,Type>();
  }

  /**
   * Creates a mutable substitution [x:=s].
   *
   * If the type of x contains type variables, then the mappings that are needed to match this to
   * the type of s are also added to the substitution.
   *
   * @see extend for possible Exceptions that might occur
   */
  public MutableSubstitution(Replaceable x, Term s) {
    _mapping = new HashMap<Replaceable,Term>();
    _typeMapping = new HashMap<TVar,Type>();
    extend(x, s);
  }

  /** Creates a mutable substitution with a copy of the mapping from the given substitution */
  private MutableSubstitution(MutableSubstitution copyme) {
    _mapping = new HashMap<Replaceable,Term>(copyme._mapping);
    _typeMapping = new HashMap<TVar,Type>(copyme._typeMapping);
  }

  /** Returns a copy of the current substitution */
  public MutableSubstitution copy() {
    return new MutableSubstitution(this);
  }

  /** @return the term that x is mapped to, or null if x is not mapped to anything */
  public Term get(Replaceable x) {
    return _mapping.get(x);
  }

  /** @return the type that alpha is mapped to, or null if alpha is not mapped to anything */
  public Type get(TVar alpha) {
    return _typeMapping.get(alpha);
  }

  /**
   * Returns the Term that x is mapped to; if x is not in the domain, then the term corresponding
   * to x is returned instead.
   */
  public Term getReplacement(Replaceable x) {
    Term ret = _mapping.get(x);
    if (ret != null) return ret;
    return TermFactory.makeTerm(x);
  }

  /**
   * Returns the Type that alpha is mapped to; if alpha is not in the domain, then alpha itself is
   * returned instead.
   */
  public Type getReplacement(TVar alpha) {
    Type ret = _typeMapping.get(alpha);
    return ret == null ? alpha : ret;
  }

  /**
   * This returns the set of variables and meta-variables which are mapped to something
   * (possibly themselves).
   */
  public final Set<Replaceable> domain() {
    return _mapping.keySet();
  }

  /** Returns the set of type variables which are mapped to something (possibly themselves). */
  public Set<TVar> typeDomain() {
    return _typeMapping.keySet();
  }

  /**
   * Adds the key/value pair to the type component of the substitution.
   * If the key is already mapped to a different value, a DuplicateMappingInSubstitutionException
   * is thrown.
   * If the key is already mapped to the same value, false is returned (and nothing is done).
   * If the key is not yet in the domain, the extension succeeds and true is returned.
   */
  public boolean extend(TVar key, Type value) {
    if (key == null) throw new NullStorageException("MutableSubstitution", "type key");
    if (value == null) throw new NullStorageException("MutableSubstitution", "type value");
    Type existing = _typeMapping.get(key);
    if (existing != null) {
      if (existing.equals(value)) return false;
      throw new DuplicateMappingInSubstitutionException(key, existing, value);
    }
    _typeMapping.put(key, value);
    return true;
  }

  /**
   * Adds the key/value pair to the substitution.
   *
   * If the key is already mapped to a different value, a DuplicateMappingInSubstitutionException
   * is thrown.
   * If the key is already mapped to the same value, false is returned (and nothing is done).
   * If the key is not yet in the domain and the types match, the extension succeeds and true is
   * returned.
   * 
   * If the type of key and value do not match, a TypingException will be thrown instead.  (This
   * check does not happen if the key is already mapped.)
   *
   * POLYMORPHISM NOTE: if the type of key has type variables in it, then the type component of
   * the substitution may be expanded so that the type of key matches the type of value, and only
   * if this is not possible a TypingException will be thrown.  For example, if the current
   * substitution is γ:
   * - if key = X_{α → β} and value is a term of type Int → Bool → Bool, and γ(α) = Int while
   *   β is not in the domain, then this call to extend will set γ(β) := Bool → Bool and
   *   γ(X) = value
   * - if key = X_{α → β} and value :: Int → Bool → Bool, and γ(β) = β, then the substitution
   *   cannot be extended for the type to match, so a TypingException is thrown
   * Hence, we preserve the invariant that if a variable is in the domain, then all its type
   * variables are as well.  These type variable mappings are not removed if the variable should
   * ever be removed from the domain!
   */
  public boolean extend(Replaceable key, Term value) {
    if (key == null) throw new NullStorageException("MutableSubstitution", "key");
    if (value == null) throw new NullStorageException("MutableSubstitution", "value");
    Term existing = _mapping.get(key);
    if (existing != null) {
      if (existing.equals(value)) return false;
      throw new DuplicateMappingInSubstitutionException(key, existing, value);
    }
    arityCheck(key, value);
    extendType(key, value);
    _mapping.put(key, value);
    return true;
  }

  /**
   * Adds the key/value pair to the substitution, replacing the mapping that is currently there.
   *
   * If the key is not yet in the domain, then this operates like extend.
   * If the key is in the domain, then the given value overrides its value.
   *
   * In both cases an appropriate type- and aritycheck is done.
   *
   * POLYMORPHISM NOTE: if the key already exists in the domain, then necessarily all type variables
   * in its type are also mapped.  These are NOT replaced by changing the value; hence, value should
   * have the same type as the existing mapping for key.
   */
  public void replace(Replaceable key, Term value) {
    if (key == null) throw new NullStorageException("MutableSubstitution", "key");
    if (_mapping.get(key) == null) {
      extend(key, value);
      return;
    }

    if (value == null) throw new NullStorageException("MutableSubstitution", "value");

    arityCheck(key, value);

    if (!value.queryType().equals(_mapping.get(key).queryType())) {
      throw new TypingException("Cannot replace mapping for ", key,
        key.isMonomorphic() ? " (of type " : " (of instantiated type ",
        _mapping.get(key).queryType(), ") to value ", value, " (of type ", value.queryType(),
        ") in substitution.");
    }
    _mapping.put(key, value);
  }

  /**
   * Helper function for extend: given that key has arity n, this checks if the given term value
   * has a shape λx_1...x_n.sub (where sub is still allowed to be an abstraction).
   *
   * If so, nothing happens.  If not, a TypingException is thrown.
   */
  private void arityCheck(Replaceable key, Term value) {
    int arity = key.queryArity();
    Term tmp = value;
    while (arity > 0) {
      if (!tmp.isAbstraction()) {
      throw new TypingException("Cannot map meta-variable ", key, " (with arity " +
        key.queryArity() + ") to value ", value, " in substitution: the value should be an " +
        "abstraction with at least " + key.queryArity() + " abstracted variables.");
      }
      arity--;
      tmp = tmp.queryAbstractionSubterm();
    }
  }

  /**
   * Helper function for extend: this checks if we can extend the type variable component of the
   * present substitution γ so that type(key) γ = type(value) γ.
   * If not, a TypingException is thrown since key cannot be mapped to value.  The current
   * substitution is not changed.
   * If so, the present substitution is extended accordingly!
   */
  private void extendType(Replaceable key, Term value) {
    if (key.isMonomorphic()) {
      if (key.queryType().equals(value.queryType())) return;  // they're equal, nothing to extend
    }
    else {
      MutableSubstitution newtypes = new MutableSubstitution();
      if (key.queryType().match(value.queryType(), newtypes)) {
        for (TVar alpha : newtypes.typeDomain()) {
          Type t = _typeMapping.get(alpha);
          if (t != null && !t.equals(newtypes.get(alpha))) {
            throw new TypingException("Cannot instantiate the type ", key.queryType(), " of key ",
              key, " in substitution to type ", value.queryType(), " since a prior mapping " +
              "assigned type variable ", alpha, " to ", _typeMapping.get(alpha), " instead of ",
              newtypes.get(alpha), ".");
          }
        }
        for (TVar alpha : newtypes.typeDomain()) {
          _typeMapping.put(alpha, newtypes.get(alpha));
        }
        return; // we've finished extending
      }
    }
    // fallthrough for both cases!
    throw new TypingException("Cannot map key ", key, " (of type ", key.queryType(), ") to " +
      "value ", value, " (of type ", value.queryType(), ") in substitution.");
  }

  /** Applies the current substitution to the given type and returns the result. */
  public Type applySubstitution(Type type) {
    return type.substitute(this);
  }

  /** Applies the current substitution to the given term and returns the result. */
  public Term applySubstitution(Term term) {
    if (term.isVariable()) return substituteVariable(term.queryVariable());
    else if (term.isConstant()) return substituteConstant(term.queryRoot());
    else if (term.isMetaApplication()) {
      return substituteMetaApplication(term.queryMetaVariable(), term.listMetaArguments());
    }
    else if (term.isApplication()) {
      return substituteApplication(term.queryHead(), term.listArguments());
    }
    else if (term.isAbstraction()) {
      return substituteAbstraction(term.queryVariable(), term.queryAbstractionSubterm());
    }
    else throw new IllegalArgumentException("MutableSubstitution::applySubstitution called " +
      "with a term that does not have any of the standard term shapes!");
  }

  /**
   * If a variable or meta-variable is NOT substituted, then the substitution can only be applied
   * on it if all its type variables are unaltered by the substitution.
   * Hence, it is for instance not allowed to have a variable x_α and apply a substitution
   * [α:=β] on it; it *would* be allowed to apply either [α:=β,x_α:=y_β] or [α:=α].
   *
   * This function checks if this requirement is satisfied, and if not, throws
   * a PolymorphicSubstitutionException.
   */
  private void checkLegalNonSubstitution(Replaceable x) {
    for (TVar alpha : x.queryTypeVars()) {
      if (!getReplacement(alpha).equals(alpha)) {
        throw new PolymorphicSubstitutionException(x, alpha);
      }
    }
  }

  /**
   * This function deletes the given variable or meta-variable from the domain.
   *
   * This function is primarily provided to allow for temporarily adding mappings to *monomorphic*
   * substitutions, or to handle abstractions in various settings, where it is sometimes necessary
   * to temporarily add the binder to the substitution.
   *
   * POLYMORPHISM NOTE: in a polymorphic system, the combination of extend/delete works somewhat
   * counterintuitive: deleting a variable x does not remove any type variable in the type of x,
   * even if those type variables were only added because x was added to the substitution!
   */
  public void delete(Variable x) {
    _mapping.remove(x);
  }

  /**
   * This returns get(x), or x itself if x is not substituted.
   *
   * POLYMORPHISM NOTE: if x is not substituted, but does have type variables which are substituted
   * this will throw a PolymorphicSubstitutionException because it is not possible to apply the
   * substitution properly.  For a substitution applied on a non-monomorphic term, it is mandatory
   * that all polymorphic variables should be in the domain of the substitution.
   */
  private Term substituteVariable(Variable x) {
    Term ret = _mapping.get(x);
    if (ret != null) return ret;
    checkLegalNonSubstitution(x);
    return x;
  }

  /**
   * If f is monomorphic, this returns f unmodified.
   *
   * If f is not monomorphic, so we can write f_σ for some polymorphic type σ, then this returns
   * f_{σγ}, where γ is the type component of the current substitution.
   */
  private Term substituteConstant(FunctionSymbol f) {
    if (f.isMonomorphic()) return f;
    return f.substituteType(this);
  }

  /**
   * If z is substituted to λx1...xn.t, this returns t[x1:=arg1,...,xn:=argsn].  If z is not
   * substituted, this returns z[args1 subst, ..., argsn subst].
   *
   * POLYMORPHISM NOTE: if z is not substituted, but does have type variables which are substituted,
   * this will throw a PolymorphicSubstitutionException because it is not possible to apply the
   * substitution properly.  For a substitution applied on a non-monomorphic term, it is mandatory
   * that all polymorphic meta-variables should be in the domain of the substitution.
   */
  private Term substituteMetaApplication(MetaVariable z, ArrayList<Term> args) {
    // set the args to the substituted arguments
    for (int i = 0; i < args.size(); i++) args.set(i, applySubstitution(args.get(i)));
    // if we're not substituting Z, then just create a new meta-application with the updated args
    Term value = _mapping.get(z);
    if (value == null) {
      checkLegalNonSubstitution(z);
      return TermFactory.createMeta(z, args);
    }
    // if Z is mapped to λx1...xn.t, then create t[x1:=args1,...,xn:=argsn]
    MutableSubstitution delta = new MutableSubstitution();
    Term origvalue = value;
    for (int i = 0; i < args.size(); i++) {
      if (!value.isAbstraction()) {
        throw new TypingException("Arity error when trying to substitute ", z, " by ", origvalue,
          ": meta-variable takes " + args.size() + " arguments, so there should be at least " +
          "this many abstractions!");
      }
      Variable x = value.queryVariable();
      value = value.queryAbstractionSubterm();
      delta.extend(x, args.get(i));
    }
    return delta.applySubstitution(value);
  }

  private Term substituteApplication(Term head, ArrayList<Term> args) {
    head = applySubstitution(head);
    for (int i = 0; i < args.size(); i++) args.set(i, applySubstitution(args.get(i)));
    return head.apply(args);
  }

  private Term substituteAbstraction(Variable binder, Term subterm) {
    Type t = binder.queryType();
    if (!binder.isMonomorphic()) t = t.substitute(this);
    Variable freshvar = TermFactory.createBinder(binder.queryName(), t);
    Term previous = _mapping.get(binder);
    _mapping.put(binder, freshvar);
    Term subtermSubstitute = null;
    RuntimeException exc = null;
    try { subtermSubstitute = applySubstitution(subterm); }
    catch (RuntimeException e) { exc = e; }
    if (previous == null) _mapping.remove(binder);
    else _mapping.put(binder, previous);
    // forward the possible exception now that we've restored the substitution
    if (exc != null) throw exc;
    return TermFactory.createAbstraction(freshvar, subtermSubstitute);
  }

  /**
   * This puts an immutable wrapper around the current substitution and returns the result.
   * Note that the current substitution itself can still be modified.
   */
  public Substitution makeImmutable() {
    return new ImmutableSubstitution(this);
  }

  /** Purely for debugging purposes! */
  public String toString() {
    if (_typeMapping.isEmpty()) return _mapping.toString();
    else return _typeMapping.toString() + "\n" + _mapping.toString();
  }
}
