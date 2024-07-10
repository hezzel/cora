package cora.rwinduction.engine;

import charlie.util.Pair;
import com.google.common.collect.ImmutableList;

interface RunnableArguments {

  /**
   * Returns a short description of the runnable.
   */
  String descriptor();

  /**
   * Returns an immutable list of strings describing how to call the runnable.
   */
  ImmutableList<Pair<String, String>> callDescriptor();

  /**
   * Returns an immutable list of strings describing the arguments the runnable receives.
   * @return
   */
  ImmutableList<String> argDescriptor();

}
