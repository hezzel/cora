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

package cora.io;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;

public class PageBuilderTest {
  @Test
  public void testTable() {
    PageBuilder.Table table = new PageBuilder.Table();
    assertTrue(table.numRows() == 0);
    assertTrue(table.numColumns() == 0);
    assertTrue(table.getColumnSize(0) == 0);

    table.addCell("x");
    table.addCell("");
    table.addCell("adjfa;");
    assertTrue(table.numRows() == 1);
    assertTrue(table.numColumns() == 3);
    assertTrue(table.getColumnSize(0) == 1);
    assertTrue(table.getColumnSize(1) == 0);
    assertTrue(table.getColumnSize(2) == 6);
    
    table.endRow();
    assertTrue(table.numRows() == 1);
    assertTrue(table.numColumns() == 3);
    ArrayList<Integer> sizes = table.getColumnSizes();
    assertTrue(sizes.get(0) == 1);
    assertTrue(sizes.get(1) == 0);
    assertTrue(sizes.get(2) == 6);

    table.addCell("50");
    assertTrue(table.numRows() == 2);
    assertTrue(table.numColumns() == 3);
    assertTrue(table.getColumnSize(0) == 2);
    assertTrue(table.getColumnSize(1) == 0);
    assertTrue(table.getColumnSize(2) == 6);

    assertTrue(table.getCellContents(0,0).equals("x"));
    assertTrue(table.getCellContents(0,1).equals(""));
    assertTrue(table.getCellContents(0,2).equals("adjfa;"));
    assertTrue(table.getCellContents(1,0).equals("50"));
    assertTrue(table.getCellContents(1,1).equals(""));
    assertTrue(table.getCellContents(1,2).equals(""));

    assertThrows(IndexOutOfBoundsException.class, () -> table.getCellContents(-1, 1));
    assertThrows(IndexOutOfBoundsException.class, () -> table.getCellContents(2, 1));
    assertThrows(IndexOutOfBoundsException.class, () -> table.getCellContents(0, -1));
    assertThrows(IndexOutOfBoundsException.class, () -> table.getCellContents(0, 3));
  }

  @Test
  public void testTextPageBuilder() {
    TextPageBuilder builder = new TextPageBuilder();
    builder.addParagraph("Hello world!");
    builder.addParagraph("This one has\n   a newline in it.");
    PageBuilder.Table table = new TextPageBuilder.Table();
    table.addCell("*");
    table.addCell("column");
    table.endRow();
    table.addCell("*");
    table.addCell("x");
    table.addCell("haha");
    table.endRow();
    table.addCell("");
    table.addCell("");
    table.addCell("?");
    builder.addTable(table);
    builder.addParagraph("And this is where it ends.");
    assertTrue(builder.toString().equals(
      "Hello world!\n\n" +
      "This one has\n   a newline in it.\n\n" +
      "  * column\n" +
      "  * x      haha\n" +
      "           ?\n\n" +
      "And this is where it ends.\n\n"));
  }
}

