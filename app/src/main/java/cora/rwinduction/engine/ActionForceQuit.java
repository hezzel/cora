package cora.rwinduction.engine;

import com.google.common.collect.ImmutableList;

class ActionForceQuit implements Action{

  @Override
  public void run(String args) {
    System.exit(0);
  }

  @Override
  public String descriptor() {
    return "";
  }


  @Override
  public ImmutableList<String> callDescriptor() {
    return null;
  }

  @Override
  public ImmutableList<String> argDescriptor() {
    return null;
  }
}
