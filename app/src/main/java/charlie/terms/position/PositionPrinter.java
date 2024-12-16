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

package charlie.terms.position;

/**
 * PositionPrinters are used in the overall output process of the tool.  This class provides a
 * default implementation, but is meant to be inherited.
 */
public class PositionPrinter {
  /**
   * Returns a string representation of the given position (using the other print method).
   * This is only supplied as a public access function, and is not meant to be overridden.
   */
  public final String print(Position pos) {
    StringBuilder builder = new StringBuilder();
    print(pos, builder);
    return builder.toString();
  }

  /**
   * This is the main public access function.  Call this to ensure that the given position is
   * printed to the given string builder.
   * 
   * To define your own PositionPrinter, you can either override this method directly -- in which
   * case there is no need to override any of the other methods in the class -- or directly override
   * (some of) the functions it calls, which are printEmptyPos, printChopPos, printCompositionPos,
   * printArgumentPos, printLambdaPos, and printMetaPos.
   */
  public void print(Position pos, StringBuilder builder) {
    switch (pos) {
      case FinalPos(int chopcount):
        if (chopcount == 0) printEmptyPos(builder);
        else printChopPos(chopcount, builder);
        break;
      case ArgumentPos(int index, Position tail):
        printArgumentPos(index, builder);
        printTail(tail, builder);
        break;
      case LambdaPos(Position tail):
        printLambdaPos(builder);
        printTail(tail, builder);
        break;
      case MetaPos(int index, Position tail):
        printMetaPos(index, builder);
        printTail(tail, builder);
    }
  }

  /**
   * Override this function to change how empty positions are printed (if print is left unmasked).
   * The default functionality is to print the unicode symbol ε.
   */
  protected void printEmptyPos(StringBuilder builder) {
    builder.append(queryEmptyPositionSymbol());
  }

  /**
   * Override this function to change how the end of a partial position with chop count k is
   * printed.  The default functionality is to print ☆k.  Note that this is only called for k ≥ 1,
   * since k = 0 will cause printEmptyPos to be called instead.
   */
  protected void printChopPos(int chopcount, StringBuilder builder) {
    builder.append(queryChopSymbol() + chopcount);
  }

  /**
   * Override this function to change the way composite positions are printed.  As it is, for a
   * position <something><tail>, first the <something> is printed using printArgumentPos,
   * printLambdaPos, or printMetaPos, and then printTail is called separately.  By default, this
   * prints <queryCompositeSymbol>tail, or nothing if the tail is empty.
   * Alternatively, override the print command if you want to do something truly different for
   * composite positions.
   */
  protected void printTail(Position tail, StringBuilder builder) {
    if (!tail.isEmpty()) {
      builder.append(queryCompositeSymbol());
      print(tail, builder);
    }
  }

  /**
   * For an argument / tuple position <index>.<tail>, this function is called to print the index
   * (unless the print function is masked).
   */
  protected void printArgumentPos(int index, StringBuilder builder) {
    builder.append("" + index);
  }

  /**
   * This function prints "0" to the string builder, to represent the start of a lambda position
   * (unless the print function is masked).
   */
  protected void printLambdaPos(StringBuilder builder) {
    builder.append("0");
  }

  /**
   * For a meta position !index.tail, this function is called to print the index (unless the print
   * function is masked).  By default, this prints !index.
   */
  protected void printMetaPos(int index, StringBuilder builder) {
    builder.append("!" + index);
  }

  /**
   * This returns the symbol that is by default used to print empty positions (if print and
   * printEmptyPos are not masked).  By default returns "ε".
   */
  protected String queryEmptyPositionSymbol() {
    return "ε";
  }

  /**
   * This returns the symbol that is by default used to print chop positions (so preceding the
   * actual chopcount, if print and printChopPos are not masked).  By default returns "☆".
   */
  protected String queryChopSymbol() {
    return "☆";
  }

  /**
   * This returns the symbol that is by default used as the separated between head and tail for
   * composite positions, if print and printTail are not masked.  By default returns ".".
   */
  protected String queryCompositeSymbol() {
    return ".";
  }
}

