package cora.rwinduction.engine;

import charlie.trs.TRS;

import java.util.ArrayDeque;
import java.util.Deque;

class ProverContext {

  private TRS _initialSystem;

  private TRS _currentSystem;

  private Deque<ProofState> _proofStates = new ArrayDeque<>();

}
