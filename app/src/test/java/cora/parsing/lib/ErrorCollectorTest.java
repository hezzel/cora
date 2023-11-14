package cora.parsing.lib;

import org.junit.Test;
import static org.junit.Assert.*;

public class ErrorCollectorTest {
  @Test
  public void testBasics() {
    ErrorCollector collector = new ErrorCollector(3);
    collector.addError("AAA");
    collector.addError("BBB");
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals("AAA\nBBB\n"));
  }

  @Test
  public void testMaxMessages() {
    ErrorCollector collector = new ErrorCollector(2);
    collector.addError("AAA");
    collector.addError("BBB");
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals("AAA\nBBB\n"));
  }

  @Test
  public void testAddBefore() {
    ErrorCollector collector = new ErrorCollector(5);
    collector.addError("AAA");
    collector.addError("BBB");
    collector.addErrorBefore(1, "CCC");
    assertTrue(collector.queryErrorCount() == 3);
    collector.addErrorBefore(-1, "DDD");
    collector.addErrorBefore(5, "EEE");
    assertTrue(collector.queryErrorCount() == 5);
    assertTrue(collector.queryCollectedMessages().equals("DDD\nAAA\nCCC\nBBB\nEEE\n"));
    collector.addErrorBefore(2, "FFF");
    assertTrue(collector.queryErrorCount() == 5);
    assertTrue(collector.queryCollectedMessages().equals("DDD\nAAA\nCCC\nBBB\nEEE\n"));
  }

  @Test
  public void testTooManyMessages() {
    ErrorCollector collector = new ErrorCollector(2);
    collector.addError("AAA");
    collector.addError("BBB");
    collector.addError("CCC");
    assertTrue(collector.queryErrorCount() == 2);
    assertTrue(collector.queryCollectedMessages().equals("AAA\nBBB\n"));
  }
}

