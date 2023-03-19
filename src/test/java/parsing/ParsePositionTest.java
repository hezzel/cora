package cora.parsing;

import org.junit.Test;
import static org.junit.Assert.*;

public class ParsePositionTest {
  @Test
  public void testFullParsePosition() {
    ParsePosition position = new ParsePosition("test.trs", 3, 9);
    assertTrue(position.getFile().equals("test.trs"));
    assertTrue(position.getLine() == 3);
    assertTrue(position.getPosition() == 9);
    assertTrue(position.toString().equals("test.trs:3:9"));
  }

  @Test
  public void testParsePositionWithoutFile() {
    ParsePosition position = new ParsePosition(null, 3, 9);
    assertTrue(position.getFile() == null);
    assertTrue(position.getLine() == 3);
    assertTrue(position.getPosition() == 9);
    assertTrue(position.toString().equals("3:9"));
  }

  @Test
  public void testParsePositionWithoutFileOrLine() {
    ParsePosition position = new ParsePosition(null, 0, 42);
    assertTrue(position.getFile() == null);
    assertTrue(position.getLine() == 0);
    assertTrue(position.getPosition() == 42);
    assertTrue(position.toString().equals("42"));
  }

  @Test
  public void testParsePositionWithoutLine() {
    ParsePosition position = new ParsePosition("file.trs", 0, 42);
    assertTrue(position.getFile() == "file.trs");
    assertTrue(position.getLine() == 0);
    assertTrue(position.getPosition() == 42);
    assertTrue(position.toString().equals("file.trs:0:42"));
  }

  @Test
  public void testParsePositionWithoutPos() {
    ParsePosition position = new ParsePosition(null, 0, 0);
    assertTrue(position.getFile() == null);
    assertTrue(position.getLine() == 0);
    assertTrue(position.getPosition() == 0);
    assertTrue(position.toString().equals("<unknown position>"));
    position = new ParsePosition(null, 3, 0);
    assertTrue(position.toString().equals("3:<unknown position>"));
    position = new ParsePosition("abc.txt", -1, 0);
    assertTrue(position.toString().equals("abc.txt:-1:<unknown position>"));
  }

  @Test
  public void testIncreasePosition() {
    ParsePosition p1 = new ParsePosition(3, 7);
    ParsePosition p2 = p1.increasePosition(2);
    assertTrue(p2.getFile() == null);
    assertTrue(p2.getLine() == 3);
    assertTrue(p2.getPosition() == 9);
  }
}

