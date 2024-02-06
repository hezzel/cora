package cora.termination.dependency_pairs;

import cora.rewriting.Rule;
import cora.rewriting.TRS;
import cora.terms.*;
import cora.types.*;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 *
 */
public class DPGenerator {

  /**
   * This property sets the output sort used in the DP method for marked symbols.
   */
  static Type dpSort = TypeFactory.createSort("DP_SORT");
  List<Term> sharpSymbols = new ArrayList<>();

  /**
   * Given a type A1 => ... => An => B this method returns a list of variables X1, ..., Xn
   * such that each variable Xi is of type Ai.
   * <p>If the given type is not an arrow type then the returned list is empty.</p>
   *
   * @param ty
   * @throws NullPointerException if ty is null
   */
  @Contract(pure = true)
  public static @NotNull List<Variable> generateVars(Type ty) {
    Objects.requireNonNull(ty, "Null argument given to DPGenerator::generateVars.");

    List<Variable> acc = new ArrayList<>();
    // Notice that the variable while_ty starts with ty, and then we mutate it to the right hand side
    // of the arrow. Eventually we will get to a sort or product, which guarantees that
    // the whole recursion will be terminated.
    // I would advise using this technique instead of a
    // while (true) { .. } construct.
    Type while_ty = ty;

    while (while_ty instanceof Arrow(Type left, Type right)) {
      acc.add(TermFactory.createVar(left));
      while_ty = right;
    }
    return acc;
  }

  /**
   * Given a type A1 => ... => An => B with b a sort or product type.
   * This method returns the type A1 => ... => An => dpSort.
   * Where dpSort is a static sort used in the
   * Dependency Pairs framework.
   */
  @Contract(pure = true)
  static Type generateDpType(@NotNull Type ty) {
    return switch (ty) {
      case Base(_), Product(_) -> dpSort;
      case Arrow(Type left, Type right) ->
        TypeFactory.createArrow(left, generateDpType(right));
    };
  }

  /**
   * Given a function symbol f : A1 => ... => An => B, this method generates a new
   * function symbol f# : A1 => ... => An => dp_sort.
   */
  @Contract(pure = true)
  static @NotNull FunctionSymbol generateSharpFn(@NotNull FunctionSymbol fn) {
    return TermFactory.createConstant(
      fn.queryHead().toString().concat("#"),
      DPGenerator.generateDpType(fn.queryHead().queryType())
    );
  }

  @Contract(pure = true)
  static @NotNull Term generateSharpTm(@NotNull Term tm) {
    FunctionSymbol newHead = generateSharpFn(tm.queryRoot());
    return newHead.apply(tm.queryArguments());
  }

  /**
   * This method applies a term of (possibly) arrow type to freshly generated variables until
   * it is of base type.
   * <p><b>Example:</b>
   * take f : A1 => A2 => A3 => a, with a being a sort.
   * then {@code fakeEta(f) = f(X{0}, X{1}, X{2})}, of course the generated variables should be of type
   * A1, A2, and A3, respectively.
   * <br />
   * In the case that {@code f} is applied to some other terms the result is analogous.
   * So, {@code fakeEta(f(s)) = f(s, X{0}, X{1}) }, assuming s is a term of type A1.
   * </p>
   * If the argument is already of base type, this function returns it unaltered.
   */
  @Contract(pure = true)
  static @NotNull Term fakeEta(@NotNull Term tm) {
    Type tmTy = tm.queryType();
    List<Variable> vars = DPGenerator.generateVars(tmTy);
    List<Term> varsCasted = vars.stream().map( x -> (Term) x).toList();
    return tm.apply(varsCasted);
  }

  /**
   * @param tm
   * @return
   */
  static @NotNull Term generateSharpEta(Term tm) {
    Term fSharp = DPGenerator.generateSharpFn(tm.queryRoot());
    return DPGenerator.fakeEta(fSharp.apply(tm.queryArguments()));
  }

  // TODO this probably isn't to be here
  static @NotNull boolean isDefined(TRS trs, FunctionSymbol fn) {
    for(Rule r : trs.queryRules()){
      if (r.queryLeftSide().queryRoot().equals(fn))
        return true;
    }
    return false;
  }

  // TODO this probably isn't to be here
  static @NotNull boolean isConstructor(TRS trs, FunctionSymbol tm) {
    return !isDefined(trs, tm);
  }

  // Computes the initial set V, defined in definition 5 (cade paper)
  // a DP l -> r [Phi] should have the following set of initial variables
  // Var(Phi) cup (Var(r) \ Var(l))
  // TODO Implementation notice: this needs to get refactored, it just blindly convert
  //   the result of calling vars() to lists... But I want streams easily!
  //   so we pay the price in a bit of performance here. Deadline approaching,
  //   so...
  private static List<Variable> computeInitialVSet(Term lhs, Term rhs, Term constraint) {

    List<Variable> lhsVars =
      StreamSupport
        .stream(lhs.vars().spliterator(), false)
        .toList();

    List<Variable> rhsVars =
      StreamSupport
        .stream(lhs.vars().spliterator(), false)
        .toList();

    //TODO also not so efficient, fix this
    List<Variable> lVars =
      rhsVars
        .stream()
        .filter(x -> !lhsVars.contains(x))
        .toList();

    List<Variable> constraintsVars =
      StreamSupport
        .stream(constraint.vars().spliterator(), false)
        .toList();

    return Stream.concat(constraintsVars.stream(), lVars.stream()).toList();
  }

  static @NotNull List<Term> generateCandidates(@NotNull TRS trs, @NotNull Term tm) {
    // In each case below we will have to recursively compute the
    // U_{i = 1}^k genRightCandidates(si), for the arguments si, of the rhs,
    // so we compute it beforehand.
    List<Term> argsCandidateApp = tm
      .queryArguments()
      .stream()
      .map(t -> DPGenerator.generateCandidates(trs, t).stream())
      .reduce(Stream.empty(), Stream::concat)
      .toList();

    // Case x (s1 ... sn), we return the candidates of each argument
    if (tm.isApplication() && tm.queryHead().isVariable()) {
      return argsCandidateApp;
    }
    // Case c (s1, ..., sn), we return the candidates of each argument
    else if (tm.isApplication() && isConstructor(trs, tm.queryRoot())) {
      return argsCandidateApp;
    }
    // Case for: (| s1, ..., sn |), we return the candidates of each argument
    else if (tm.isTuple()) {
      return tm
        .queryTupleArguments()
        .stream()
        .flatMap(t -> DPGenerator.generateCandidates(trs, t).stream())
        .collect(Collectors.toList());
    }
    // Case for: g(s1, ..., sn) with g a defined symbol and n > 0
    else if (tm.isApplication() && isDefined(trs, tm.queryRoot())) {
      return Stream.concat(
        argsCandidateApp.stream(),
        Stream.of(DPGenerator.generateSharpEta(tm))
      ).toList();
    } else if (tm.isConstant() && isDefined(trs, tm.queryRoot())) {
      return List.of(generateSharpEta(tm));
    }
    // If none of the cases above is true, we return an empty list.
    return List.of();
  }

  static Problem generateProblemFromRule(TRS trs, Rule rule) {
    Term lhs = rule.queryLeftSide();
    Term rhs = rule.queryRightSide();
    Term ctr = rule.queryConstraint();
    List<Term> freshDpVars = DPGenerator
      .generateVars(lhs.queryType())
      .stream()
      .map(x -> (Term) x)
      .toList();

    Term dpLeft = generateSharpTm(lhs).apply(freshDpVars);
    Term dpRight = rhs.apply(freshDpVars);

    List<Term> candRight = generateCandidates(trs, dpRight);

    return new Problem (
      candRight
        .stream()
        .map(candidates ->
          new DP(dpLeft, candidates, ctr, computeInitialVSet(dpLeft, candidates, ctr))
        ).toList(),
      trs
    );
  }

  public static Problem generateProblemFromTrs(TRS trs) {
    List<Rule> rules = new ArrayList<Rule>();
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      rules.add(trs.queryRule(i));
    }
    return new Problem (
      rules
        .stream()
        .flatMap(
          rule ->
            DPGenerator.generateProblemFromRule(trs, rule).getDPList().stream()
        )
        .toList(),
      trs
    );
  }
}
