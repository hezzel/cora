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


  class SimplexTableau{
    ArrayList<Integer> objectiveFunction;
    ArrayList<ArrayList<Integer>> constraints;
    ArrayList<Integer> constants;

    public SimplexTableau (ArrayList<Integer> objectiveFunction, ArrayList<ArrayList<Integer>> constraints, ArrayList<Integer> constants){
      this.objectiveFunction = objectiveFunction;
      this.constraints = constraints;
      this.constants = constants;
    } 
  }



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
    for (int i = 1; i < expressions.size(); i++){
      expressions.set(i, addSlackVariable(problem, expressions.get(i)));
    }
    makeSimplexTableau (problem, expressions);
    return new Answer.MAYBE("not implemented yet");

  }

  public IntegerExpression addSlackVariable (SmtProblem problem, IntegerExpression expr){
    return SmtFactory.createAddition(SmtFactory.createMultiplication(SmtFactory.createValue(-1), problem.createIntegerVariable()), expr).simplify();
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

  public void collectConstants(ArrayList<Integer> list, IntegerExpression expr){
    switch (expr) {
      case IVar x: return;
      case IValue v: list.add(v.queryValue());return;
      case CMult cm: return;
      case Addition a:
        for (int i = 1; i <= a.numChildren(); i++) collectConstants(list, a.queryChild(i));
        return;
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }

  public void makeSimplexTableau (SmtProblem problem, ArrayList<IntegerExpression> expressions){
    System.out.println(expressions);
    Set<IVar> vars = new HashSet<IVar>();
    for (IntegerExpression expr : expressions){
      collectVariables(vars, expr);
    }
    IntegerExpression obj_func = expressions.get(0);
    expressions.remove(0);

    System.out.println(vars);
    ArrayList<ArrayList<Integer>> simplexTableau =  new ArrayList<>(); 
    
    for (IntegerExpression expr : expressions){
      ArrayList<Integer> row = new ArrayList<>();
      for (IVar var : vars){
        row.add(getCount(var, expr)*-1);
      }
      simplexTableau.add(row);
    }
    ArrayList<Integer> objFuncRow = new ArrayList<>();
    for (IVar var: vars){
      objFuncRow.add(getCount(var, obj_func));
    }
    ArrayList<Integer> constants = new ArrayList<>();
    for (IntegerExpression expr : expressions){
      collectConstants(constants, expr);
    }
    // is dit nodig???
    //constants.add(0);
    System.out.println(simplexTableau);
    System.out.println(objFuncRow);
    System.out.println(constants);
    SimplexTableau simpTab = new SimplexTableau(objFuncRow, simplexTableau, constants);
    simplexMethod(simpTab);
  }

  public Boolean pivotFound (ArrayList<ArrayList<Double>> matrix){
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
    System.out.println("we start with: " + lowestQuotient);
    int lowestQuotientIndex = 0;    
    for (int i =1; i < matrix.size()-1; i++){
      System.out.println ("gonna check: " + matrix.get(i).get(matrix.get(i).size()-1) + " divided by " + matrix.get(i).get(pivotColumn));
      
      if (matrix.get(i).get(matrix.get(i).size()-1) / matrix.get(i).get(pivotColumn) < lowestQuotient){
        lowestQuotientIndex = i;
      }
    }
    return lowestQuotientIndex;
  }

  public ArrayList<ArrayList<Double>> transformToMatrix (SimplexTableau simpTab){
    ArrayList<ArrayList<Double>> list = new ArrayList<>();
    for (int k =0; k < simpTab.constraints.size(); k++){
      ArrayList<Double> temp = new ArrayList<>();
      for (int j =0; j< simpTab.constraints.get(k).size(); j++){
        double d = simpTab.constraints.get(k).get(j);
        System.out.println(d);
        temp.add(d);
      }
      double constant = simpTab.constants.get(k);
      temp.add(constant);
      list.add(temp);
    }
    ArrayList<Double> temp = new ArrayList<>();
    for (int i : simpTab.objectiveFunction){
      double d = i;
      temp.add(d);
    }
    temp.add(0.0);
    list.add(temp);
    return list;
  }

  public ArrayList<ArrayList<Double>> step (ArrayList<ArrayList<Double>> matrix, int pivotColumn, int pivotRow){
    for (int i = 0; i < matrix.size(); i++){
      for (int j =0; j < matrix.get(i).size(); j++){

        double newValue = matrix.get(i).get(j)/matrix.get(pivotRow).get(pivotColumn);
        matrix.get(i).set(j, newValue);
      }
    }
    System.out.println("pivot is 1: " + matrix);
    for (int i =0; i < matrix.size(); i++){
      if (i != pivotRow){
        double factor = matrix.get(i).get(pivotColumn);
        for (int j =0; j < matrix.get(i).size(); j++){
          double newValue = matrix.get(i).get(j)-(factor*matrix.get(pivotRow).get(j));
          matrix.get(i).set(j,newValue);
        }

      }
    }
    System.out.println(matrix);
    return matrix;
  }



  public void simplexMethod(SimplexTableau simpTab){
    ArrayList<ArrayList<Double>> matrix = transformToMatrix(simpTab);
    if (pivotFound(matrix)){
      System.out.println (matrix);
      int pivotColumn= pivotColumn(matrix);
      int pivotRow = pivotRow(pivotColumn, matrix);

      System.out.println("pivot row and column: " + pivotRow + " " + pivotColumn);
      matrix = step(matrix, pivotColumn, pivotRow);
      //next make all entries in pivot column zero except pivot element
    }
  }
}
