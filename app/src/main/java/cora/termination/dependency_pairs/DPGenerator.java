package cora.termination.dependency_pairs;

import cora.rewriting.Rule;
import cora.rewriting.TRS;
import cora.terms.FunctionSymbol;
import cora.terms.Term;
import cora.terms.TermFactory;
import cora.terms.TheoryFactory;
import cora.types.*;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 *
 */
class DPGenerator {

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
  static @NotNull List<Term> generateVars(Type ty) {
    Objects.requireNonNull(ty, "Null argument given to DPGenerator::generateVars.");

    List<Term> acc = new ArrayList<>();
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
    List<Term> newVars = DPGenerator.generateVars(tmTy);
    return tm.apply(newVars);
  }

  /**
   * @param tm
   * @return
   */
  static @NotNull Term generateSharpEta(Term tm) {
    Term fSharp = DPGenerator.generateSharpFn(tm.queryRoot());
    return DPGenerator.fakeEta(fSharp.apply(tm.queryArguments()));
  }

  static @NotNull boolean isConstructor(Term tm) {
    return false;
  }

  static @NotNull boolean isDefined(FunctionSymbol tm) {
    return true;
  }

  static @NotNull List<Term> generateCandidates(@NotNull Term tm) {
    // In each case below we will have to recursively compute the
    // U_{i = 1}^k genRightCandidates(si), for the arguments si, of the rhs,
    // so we compute it beforehand.
    List<Term> argsCandidateApp = tm
      .queryArguments()
      .stream()
      .map(t -> DPGenerator.generateCandidates(t).stream())
      .reduce(Stream.empty(), Stream::concat)
      .toList();

    // Case x (s1 ... sn), we return the candidates of each argument
    if (tm.isApplication() && tm.queryHead().isVariable()) {
      return argsCandidateApp;
    }
    // Case c (s1, ..., sn), we return the candidates of each argument
    else if (tm.isApplication() && isConstructor(tm.queryHead())) {
      return argsCandidateApp;
    }
    // Case for: (| s1, ..., sn |), we return the candidates of each argument
    else if (tm.isTuple()) {
      return tm
        .queryTupleArguments()
        .stream()
        .flatMap(t -> DPGenerator.generateCandidates(t).stream())
        .collect(Collectors.toList());
    }
    // Case for: g(s1, ..., sn) with g a defined symbol and n > 0
    else if (tm.isApplication() && isDefined(tm.queryRoot())) {
      return Stream.concat(
        argsCandidateApp.stream(),
        Stream.of(DPGenerator.generateSharpEta(tm))
      ).toList();
    } else if (tm.isConstant() && isDefined(tm.queryRoot())) {
      return List.of(generateSharpEta(tm));
    }
    // If none of the cases above is true, we return an empty list.
    return List.of();
  }

  static Problem generateProblemFromRule(Rule rule) {
    Term lhs = rule.queryLeftSide();
    Term rhs = rule.queryRightSide();
    List<Term> freshDpVars = DPGenerator.generateVars(lhs.queryType());
    Term dpLeft = lhs.apply(freshDpVars);
    Term dpRight = rhs.apply(freshDpVars);

    List<Term> candRight = generateCandidates(dpRight);

    return new Problem(
      candRight
        .stream()
        .map(t -> new DP(dpLeft, t, TheoryFactory.createValue(true)))
        .toList()
    );
  }

  static Problem generateProblemFromTrs(TRS trs) {
    List<Rule> rules = new ArrayList<Rule>();
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      rules.add(trs.queryRule(i));
    }
    return new Problem (
      rules
        .stream()
        .flatMap(rule -> DPGenerator.generateProblemFromRule(rule).getDPList().stream())
        .collect(Collectors.toList())
    );
  }
}
