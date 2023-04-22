package cora.parsing.lib;

import org.junit.Test;
import static org.junit.Assert.*;

public class TokenFinderTest {
  @Test
  public void testSimpleTokens() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER" });
    Token a = tf.matchStart("xyz1a 11341", 0, new ParsePosition("a", 1, 3));
    Token b = tf.matchStart("aa12341{a", 1, new ParsePosition(1));
    Token c = tf.matchStart("10ja }", 0, new ParsePosition(12));
    assertTrue(a.getName().equals("IDENTIFIER"));
    assertTrue(a.getText().equals("xyz1a"));
    assertTrue(a.getPosition().toString().equals("a:1:3"));
    assertTrue(b.getName().equals("IDENTIFIER"));
    assertTrue(b.getText().equals("a12341"));
    assertTrue(b.getPosition().toString().equals("1"));
    assertTrue(c.getName().equals("INTEGER"));
    assertTrue(c.getText().equals("10"));
    assertTrue(c.getPosition().toString().equals("12"));
  }

  @Test
  public void testUnicodeTokens() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[^\\s]", "NONWHITE",
                                       "[∀∃]+", "QUANT" });
    ParsePosition p = new ParsePosition(1);
    Token a = tf.matchStart("λx.ε ∃∀λ", 0, p);
    Token b = tf.matchStart("λx.ε ∃∀λ", 5, p);
    Token c = tf.matchStart("λx.ε ∃∀λ", 6, p);
    assertTrue(a.getName().equals("NONWHITE"));
    assertTrue(a.getText().equals("λ"));
    assertTrue(b.getName().equals("QUANT"));
    assertTrue(b.getText().equals("∃∀"));
    assertTrue(c.getName().equals("NONWHITE"));
    assertTrue(c.getText().equals("∀"));
  }

  @Test
  public void testCatchAll() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "[a-zA-Z_][a-z0-9A-Z_]*", "IDENTIFIER",
                                       "0|[1-9][0-9]*", "INTEGER" });
    ParsePosition p = new ParsePosition(1);
    Token a = tf.matchStart("∀∀\r\n\na", 0, p);
    Token b = tf.matchStart("∀∀\r\n\na", 2, p);
    assertTrue(a.getName().equals("CATCHALL"));
    assertTrue(a.getText().equals("∀"));
    assertTrue(b.getName().equals("CATCHALL"));
    assertTrue(b.getText().equals("\r\n"));
  }

  @Test
  public void testMatchEmptyString() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "a*", "A",
                                       "b+", "B" });
    ParsePosition p = new ParsePosition(3);
    Token a = tf.matchStart("aaabak", 0, p);
    Token b = tf.matchStart("bbaaaba", 0, p);
    Token c = tf.matchStart("c", 0, p);
    Token d = tf.matchStart("bbaaabac", 7, p);
    Token e = tf.matchStart("bbaaabac", 8, p);
    Token f = tf.matchStart("", 0, p);
    assertTrue(a.getName().equals("A"));
    assertTrue(a.getText().equals("aaa"));
    assertTrue(b.getName().equals("B"));
    assertTrue(b.getText().equals("bb"));
    assertTrue(c.getName().equals("CATCHALL"));
    assertTrue(c.getText().equals("c"));
    assertTrue(d.getName().equals("CATCHALL"));
    assertTrue(d.getText().equals("c"));
    assertTrue(e == null);
    assertTrue(f == null);
  }

  @Test
  public void testFirstMatchNotLongestMatch() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "a*", "A",
                                       "aaab+", "B" });
    ParsePosition p = new ParsePosition(42);
    Token a = tf.matchStart("aaabak", 0, p);
    assertTrue(a.getName().equals("B"));
    assertTrue(a.getText().equals("aaab"));
  }

  @Test
  public void testTwoEqualSizeMatches() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "a..", "A",
                                       ".*b", "B" });
    ParsePosition p = new ParsePosition(37);
    Token a = tf.matchStart("acbd", 0, p);
    assertTrue(a.getName().equals("A"));
    assertTrue(a.getText().equals("acb"));
  }

  @Test
  public void testBoundaries() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "^(a|b)*", "A",
                                       "(a|b)*$", "B" });
    ParsePosition p = new ParsePosition(3);
    Token a = tf.matchStart("abcba", 0, p);
    Token b = tf.matchStart("abcba", 2, p);
    Token c = tf.matchStart("abcba", 3, p);
    Token d = tf.matchStart("abcba\nbb", 3, p);
    Token e = tf.matchStart("abcba\nbb\na", 6, p);
    Token f = tf.matchStart("abcba\nbb\na", 9, p);
    Token g = tf.matchStart("abcba\nbb\na\n", 9, p);
    assertTrue(a.getName().equals("A"));
    assertTrue(a.getText().equals("ab"));
    assertTrue(b.getName().equals("CATCHALL"));
    assertTrue(c.getName().equals("B"));
    assertTrue(c.getText().equals("ba"));
    assertTrue(d.getName().equals("CATCHALL"));
    assertTrue(e.getName().equals("CATCHALL"));
    assertTrue(f.getName().equals("B"));
    assertTrue(f.getText().equals("a"));
    assertTrue(g.getName().equals("B"));
    assertTrue(g.getText().equals("a"));
  }

  @Test
  public void testNewLine() {
    TokenFinder tf = new TokenFinder(new String[] { "\\{(.|\n)*\\}", "BRACED" });
    ParsePosition p = new ParsePosition(5);
    Token a = tf.matchStart("abcd{efg\nhijklm}nop\nd", 4, p);
    assertTrue(a.getName().equals("BRACED"));
    assertTrue(a.getText().equals("{efg\nhijklm}"));
  }

  @Test
  public void testTwoTokensWithSameName() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "a+", "AORB",
                                       "b+", "AORB",
                                       "(ab)+", "MIXED" });
    Token a = tf.matchStart("aaabbbabaa", 0, null);
    Token b = tf.matchStart("aaabbbabaa", 3, null);
    Token c = tf.matchStart("aaabbbabaa", 6, null);
    Token d = tf.matchStart("aaabbbabaa", 7, null);
    assertTrue(a.getName().equals("AORB"));
    assertTrue(a.getText().equals("aaa"));
    assertTrue(b.getName().equals("AORB"));
    assertTrue(b.getText().equals("bbb"));
    assertTrue(c.getName().equals("MIXED"));
    assertTrue(c.getText().equals("ab"));
    assertTrue(d.getName().equals("AORB"));
    assertTrue(d.getText().equals("b"));
  }

  @Test
  public void testTwoTokensWithSameExpression() {
    TokenFinder tf = new TokenFinder(new String[] {
                                       "a+", "A",
                                       "a+", "B" });
    Token a = tf.matchStart("aaabbbabaa", 0, null);
    assertTrue(a.getName().equals("A"));
    assertTrue(a.getText().equals("aaa"));
  }
}

