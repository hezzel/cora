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

package cora.smt;

import charlie.smt.*;
import java.lang.Iterable;
import java.util.Iterator;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class InternalSolver implements SmtSolver {

  /**
   * TODO: this is the place where all the work needs to be done.
   * Figure out if we should return YES(Valuation val), NO(), or MAYBE(String reason).
   */
  public SmtSolver.Answer checkSatisfiability(SmtProblem problem) {
    //return new Answer.YES(new Valuation());
    Constraint constraints = problem.queryCombinedConstraint();
    ArrayList<Constraint> children = new ArrayList<>();
    if (constraints instanceof Conjunction) {
      Conjunction conjunction = (Conjunction) constraints;
      for (int i = 1; i <= conjunction.numChildren(); i++){
        children.add(conjunction.queryChild(i));
      }
    }
    ArrayList<IntegerExpression> expressions = new ArrayList<IntegerExpression>();
    for (int i =0; i < children.size(); i++){
      Constraint child = children.get(i);
      if (child instanceof Is0){
        Is0 func = (Is0) child;
        expressions.add(func.queryExpression().simplify());
      }
      else if (child instanceof Geq0){
        Geq0 func = (Geq0) child;
        expressions.add(func.queryExpression().simplify());
      }
    }
    //for every expression except the objective function we add a slack variable
    for (int i = 1; i < expressions.size(); i++){
      expressions.set(i, addSlackVariable(problem, expressions.get(i)));
    }
    ArrayList<ArrayList<Double>> simpTab = makeSimplexTableau (problem, expressions);
    simplexMethod(simpTab);
    return new Answer.MAYBE("not implemented yet");

  }

  /**
   * TODO: this should return true if we can prove that the given problem is valid, and false if
   * we cannot prove validity.  Note that if we let phi be the negation of the problem (use:
   * problem.queryCombinedConstraint().negate()), then we have validity exactly if we can show that
   * phi is NOT satisfiabile.
   */
  public boolean checkValidity(SmtProblem problem) {
    return !checkSatisfiability(problem).isYes();
  }


  public IntegerExpression addSlackVariable (SmtProblem problem, IntegerExpression expr){
    return SmtFactory.createAddition(SmtFactory.createMultiplication(SmtFactory.createValue(-1), problem.createIntegerVariable()), expr).simplify();
  }

  public void collectVariables(Set<IVar> vars, IntegerExpression expr) {
    switch (expr) {
      case IVar x: vars.add(x); return;
      case IValue v: return;
      case CMult cm:
        if (cm.queryChild() instanceof IVar x) vars.add(x);
        else throw new Error("This won't work if we mutliply constants by things other than variables!");
        return;
      case Addition a:
        for (int i = 1; i <= a.numChildren(); i++) collectVariables(vars, a.queryChild(i));
        return;
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }

  int getCount(IVar x, IntegerExpression expr) {
    switch(expr) {
      case IVar y: if (x.equals(y)) return 1; else return 0;
      case IValue v: return 0;
      case CMult cm: if (cm.queryChild().equals(x)) return cm.queryConstant(); else return 0;
      case Addition a:
        for (int i = 1; i <= a.numChildren(); i++) {
          int tmp = getCount(x, a.queryChild(i));
          if (tmp != 0) return tmp;
        }
        return 0;
      default: throw new Error("expression does not have the expected shape!");
    }
  }

  public void collectConstants(ArrayList<Double> list, IntegerExpression expr){
    switch (expr) {
      case IVar x: return;
      case IValue v: list.add((double)v.queryValue());return;
      case CMult cm: return;
      case Addition a:
        for (int i = 1; i <= a.numChildren(); i++) collectConstants(list, a.queryChild(i));
        return;
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }

  public ArrayList<ArrayList<Double>> makeSimplexTableau (SmtProblem problem, ArrayList<IntegerExpression> expressions){
    ArrayList<ArrayList<Double>> simplexTableau = new ArrayList<>();
    System.out.println(expressions);
    Set<IVar> vars = new HashSet<IVar>();
    for (IntegerExpression expr : expressions){
      collectVariables(vars, expr);
    }
    IntegerExpression obj_func = expressions.get(0);
    expressions.remove(0);

    System.out.println(vars);
    
    for (IntegerExpression expr : expressions){
      ArrayList<Double> row = new ArrayList<>();
      for (IVar var : vars){
        row.add( (double)getCount(var, expr)*-1);
      }
      ArrayList<Double> list = new ArrayList<>();
      collectConstants(list, expr);
      for (Double d : list){
        row.add(d);
      }
      simplexTableau.add(row);
    }
    ArrayList<Double> objFuncRow = new ArrayList<>();
    for (IVar var: vars){
      objFuncRow.add((double)getCount(var, obj_func));
    }
    objFuncRow.add(0.0);
    simplexTableau.add(objFuncRow);

    return simplexTableau;
  }

  public Boolean pivotFound (ArrayList<ArrayList<Double>> matrix){
    //returns true if there is a negative number in the objective row
    for (double i : matrix.get(matrix.size()-1)){
      if (i < 0){
        return true;
      }
    }
    return false;
  }

  public int pivotColumn(ArrayList<ArrayList<Double>> matrix){
    //returns index of lowest value in objective row
    int lowestElementIndex = 0;
    for (int i = 1; i < matrix.get(matrix.size()-1).size()-1; i++){
      if (matrix.get(matrix.size()-1).get(i) < matrix.get(matrix.size()-1).get(lowestElementIndex)){
        lowestElementIndex = i;
      }
    }
    return lowestElementIndex;
  }

  public int pivotRow (int pivotColumn, ArrayList<ArrayList<Double>> matrix){
    double lowestQuotient = matrix.get(0).get(matrix.get(0).size()-1)/ matrix.get(0).get(pivotColumn);
    int lowestQuotientIndex = 0;    
    for (int i =1; i < matrix.size()-1; i++){
      if (matrix.get(i).get(pivotColumn) != 0){
        if (matrix.get(i).get(matrix.get(i).size()-1) / matrix.get(i).get(pivotColumn) < lowestQuotient){
          lowestQuotientIndex = i;
        }
      }

    }
    return lowestQuotientIndex;
  }

  public void printSimplexTableau (ArrayList<ArrayList<Double>> simpTab){
    for (int i =0; i < simpTab.size(); i++){
      System.out.print("[ ");
      for (int j =0; j < simpTab.get(i).size(); j++){
        System.out.print(simpTab.get(i).get(j) + ", ");
      }
      System.out.println("] ");
    }
  }

  public ArrayList<ArrayList<Double>> step (ArrayList<ArrayList<Double>> matrix, int pivotColumn, int pivotRow){
    double factor = matrix.get(pivotRow).get(pivotColumn);
    for (int i = 0; i < matrix.size(); i++){
      for (int j =0; j < matrix.get(i).size(); j++){
        double newValue = matrix.get(i).get(j)/factor;
        matrix.get(i).set(j, newValue);
      }
    }
    for (int i =0; i < matrix.size(); i++){
      if (i != pivotRow){
        factor = matrix.get(i).get(pivotColumn);
        System.out.println ("subtracting " + factor + " times, row " + pivotRow + " from row " + i);
        for (int j =0; j < matrix.get(i).size(); j++){
          double newValue = matrix.get(i).get(j)-(factor*matrix.get(pivotRow).get(j));
          matrix.get(i).set(j,newValue);
        }

      }
    }
    printSimplexTableau(matrix);
    return matrix;
  }

  public void simplexMethod(ArrayList<ArrayList<Double>> simpTab){
    while (pivotFound(simpTab)){
      printSimplexTableau (simpTab);
      int pivotColumn= pivotColumn(simpTab);
      int pivotRow = pivotRow(pivotColumn, simpTab);

      System.out.println("pivot row and column: " + pivotRow + " " + pivotColumn);
      simpTab = step(simpTab, pivotColumn, pivotRow);
    }
  }
}
