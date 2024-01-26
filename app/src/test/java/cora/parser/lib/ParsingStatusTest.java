package cora.parser.lib;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.LinkedList;
import cora.exceptions.ParseError;

public class ParsingStatusTest {
  private class TestTokenQueue implements TokenQueue {
    LinkedList<Token> tokens;
    public TestTokenQueue() { tokens = new LinkedList<Token>(); }
    public void add(String name) { push(new Token(new ParsePosition(1+tokens.size()), name, " ")); }
    public void push(Token tok) { tokens.push(tok); }
    public Token nextToken() throws LexerException {
      if (tokens.isEmpty()) return Token.eofToken(new ParsePosition(10));
      Token t = tokens.pop();
      if (t.getName().equals("ERROR")) throw new LexerException(t, "Encountered an error.");
      return t;
    }
  }

  @Test
  public void testNextToken() {
    TestTokenQueue tq = new TestTokenQueue();
    tq.add("BING");
    tq.add("BING");
    tq.add("SPACE");
    ParsingStatus ps = new ParsingStatus(tq, 20);
    assertTrue(ps.nextToken().getName().equals("SPACE"));
    assertTrue(ps.nextToken().getName().equals("BING"));
    assertTrue(ps.nextToken().getName().equals("BING"));
    assertTrue(ps.nextToken().isEof());
    ps.throwCollectedErrors();  // does nothing, as there have not been any errors
  }

  @Test
  public void testTokensWithErrors() {
    TestTokenQueue tq = new TestTokenQueue();
    tq.add("BING");
    tq.add("ERROR");
    tq.add("BONG");
    tq.add("SPACE");
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus ps = new ParsingStatus(tq, collector);
    assertTrue(ps.nextToken().getName().equals("SPACE"));
    assertTrue(ps.nextToken().getName().equals("BONG"));
    assertTrue(ps.nextToken().getName().equals("BING"));  // no ERROR is passed on
    assertTrue(ps.nextToken().isEof());
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(collector.queryCollectedMessages().equals("2: Encountered an error.\n"));
  }

  @Test
  public void testAddError() {
    TestTokenQueue tq = new TestTokenQueue();
    tq.add("ERROR");
    tq.add("AA");
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus ps = new ParsingStatus(tq, collector);
    Token tok = ps.peekNext();
    ps.storeError("Meep!", tok);
    ps.storeError("Flop.", tok);
    ps.storeError("Blah.", null);
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals("2: Meep!\nBlah.\n"));
    ps.nextToken();
    assertTrue(collector.queryErrorCount() == 2);
    ps.nextToken();
    assertTrue(collector.queryErrorCount() == 3);
  }

  @Test
  public void testAddErrorAt() {
    TestTokenQueue tq = new TestTokenQueue();
    tq.add("ERROR");
    tq.add("AA");
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus ps = new ParsingStatus(tq, collector);
    Token tok = ps.peekNext();
    int k1 = ps.queryErrorPosition();
    ps.storeError("Meep!", tok);
    int k2 = ps.queryErrorPosition();
    ps.storeError("Flop.", tok);
    ps.storeError("Flop2.", tok, k2);
    ps.storeError("Blah.", null, k1);
    assertTrue(collector.queryErrorCount() == 3);
    assertTrue(collector.queryCollectedMessages().equals("Blah.\n2: Meep!\n2: Flop2.\n"));
    ps.nextToken();
    assertTrue(collector.queryErrorCount() == 3);
    ps.nextToken();
    assertTrue(collector.queryErrorCount() == 4);
  }

  @Test
  public void testOneErrorTooMany() {
    TestTokenQueue tq = new TestTokenQueue();
    tq.add("AA");
    tq.add("ERROR");
    ErrorCollector collector = new ErrorCollector(3);
    ParsingStatus ps = new ParsingStatus(tq, collector);
    ps.storeError("Test.", null);
    ps.nextToken();
    try { ps.storeError("Bing",null); }
    catch (ParseError e) { return; }
    assertTrue(false);
  }

  @Test
  public void testPeekNext() {
    TestTokenQueue tq = new TestTokenQueue();
    tq.add("AA");
    tq.add("ERROR");
    tq.add("BB");
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus ps = new ParsingStatus(tq, collector);
    assertTrue(ps.peekNext().toString().equals("3:   (BB)"));
    assertTrue(ps.nextTokenIs("BB"));
    assertTrue(ps.nextToken().toString().equals("3:   (BB)"));
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(ps.peekNext().toString().equals("1:   (AA)"));
    assertTrue(collector.queryErrorCount() == 1);
    ps.peekNext();
    ps.nextTokenIs("BB");
    assertTrue(collector.queryErrorCount() == 1);
  }

  @Test
  public void testNextAre() {
    TestTokenQueue tq = new TestTokenQueue();
    tq.add("AA");
    tq.add("ERROR");
    tq.add("BB");
    tq.add("CC");
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus ps = new ParsingStatus(tq, collector);
    assertTrue(ps.nextTokensAre(new String[] { "CC", "BB" }));
    assertTrue(collector.queryErrorCount() == 0);
    assertFalse(ps.nextTokensAre(new String[] { "CC", "AA", "BB" }));
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(ps.nextTokensAre(new String[] { "CC", "BB", "AA" }));
    assertTrue(collector.queryErrorCount() == 1);
    ps.nextToken();
    assertTrue(ps.nextTokensAre(new String[] { "BB", "AA" }));
    assertTrue(collector.queryErrorCount() == 1);
  }

  @Test
  public void testReadNextIf() {
    TestTokenQueue tq = new TestTokenQueue();
    tq.add("AA");
    tq.add("ERROR");
    tq.add("BB");
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus ps = new ParsingStatus(tq, collector);
    assertTrue(ps.readNextIf("XX") == null);
    assertTrue(ps.readNextIf("BB") != null);
    assertTrue(collector.queryErrorCount() == 0);
    assertTrue(ps.readNextIf("BB") == null);
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(ps.readNextIf("AA").getName().equals("AA"));
    assertTrue(collector.queryErrorCount() == 1);
    assertTrue(ps.nextToken().isEof());
    assertTrue(ps.readNextIf("EOF").isEof());
    assertTrue(ps.readNextIf("XX") == null);
  }

  @Test
  public void testExpect() {
    TestTokenQueue tq = new TestTokenQueue();
    tq.add("AA");
    tq.add("BB");
    ErrorCollector collector = new ErrorCollector(10);
    ParsingStatus ps = new ParsingStatus(tq, collector);
    assertTrue(ps.expect("BB", "a bb token") != null);
    assertTrue(collector.queryErrorCount() == 0);
    ps.nextToken();
    assertTrue(ps.expect("BB", "a bb token") == null);
    assertTrue(collector.queryErrorCount() == 1);
  }
}

