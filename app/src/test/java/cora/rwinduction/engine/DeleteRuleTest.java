package cora.rwinduction.engine;

import charlie.exceptions.IndexingException;
import charlie.reader.CoraInputReader;
import charlie.reader.OCocoInputReader;
import charlie.terms.Term;
import org.junit.jupiter.api.Test;

import java.io.Reader;

import static org.junit.jupiter.api.Assertions.*;

class DeleteRuleTest {

  DeleteRule deleteRule = new DeleteRule();

  @Test
  void testIsApplicableOutOfBounds() {

    ProofState empty = ProofState.createEmptyState();

    RuleArguments delArgs = new RuleArguments(empty, 0);

    // try to remove something from an empty context
    assertThrows(IndexingException.class, () -> deleteRule.isApplicable(delArgs));
  }
}
