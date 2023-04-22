package cora.parsing.lib;

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

  @Test
  public void testBeforeWithFile() {
    ParsePosition pos = new ParsePosition("file.trs", 7, 18);
    assertFalse(pos.before(new ParsePosition(null, 12, 100)));
    assertFalse(pos.before(new ParsePosition("other.trs", 12, 100)));
    assertFalse(pos.before(new ParsePosition("file.trs", 0, 100)));
    assertFalse(pos.before(new ParsePosition("file.trs", 2, 100)));
    assertTrue(pos.before(new ParsePosition("file.trs", 8, 1)));
    assertTrue(pos.before(new ParsePosition("file.trs", 7, 100)));
    assertFalse(pos.before(new ParsePosition("file.trs", 7, 17)));
    assertFalse(pos.before(new ParsePosition("file.trs", 7, 18)));
  }

  @Test
  public void testBeforeWithLineButNoFile() {
    ParsePosition pos = new ParsePosition(null, 7, 18);
    assertFalse(pos.before(new ParsePosition("file.trs", 9, 100)));
    assertFalse(pos.before(new ParsePosition(null, 0, 100)));
    assertFalse(pos.before(new ParsePosition(null, 6, 10)));
    assertTrue(pos.before(new ParsePosition(null, 12, 3)));
    assertFalse(pos.before(new ParsePosition(null, 7, 18)));
    assertTrue(pos.before(new ParsePosition(null, 7, 19)));
  }

  @Test
  public void testBeforeWithNoLine() {
    ParsePosition pos = new ParsePosition(null, 0, 18);
    assertFalse(pos.before(new ParsePosition("file.trs", 9, 100)));
    assertFalse(pos.before(new ParsePosition(null, 9, 100)));
    assertFalse(pos.before(new ParsePosition(null, 0, 17)));
    assertFalse(pos.before(new ParsePosition(null, 0, 18)));
    assertTrue(pos.before(new ParsePosition(null, 0, 19)));
  }
}

