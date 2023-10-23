/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parsing.lib;

import java.util.ArrayList;

/**
 * An ErrorCollector keeps track of a number of errors during parsing, which allows the user to
 * continue after a failure and print them all at once.
 */
public class ErrorCollector {
  private ArrayList<String> _messages;
  private int _maxErrorCount;

  /** Set up an ErrorCollector which keeps track of at most [max] messages. */
  public ErrorCollector(int max) {
    _messages = new ArrayList<String>();
    if (max < 1) max = 1;
    _maxErrorCount = max;
  }

  /** Adds an Error to be stored in the ErrorCollector. */
  public void addError(String message) {
    if (_messages.size() < _maxErrorCount) _messages.add(message);
  }

  /**
   * Adds an Error to be stored in the ErrorCollector, at the given index.
   * If the index is too high, it will simply be stored at the end.
   */
  public void addErrorBefore(int pos, String message) {
    if (_messages.size() < _maxErrorCount) {
      if (pos < 0) pos = 0;
      if (pos > _messages.size()) pos = _messages.size();
      _messages.add(pos, message);
    }
  }

  /** Returns the number of stored errors. There have been errors if and only if this ≥ 1. */
  public int queryErrorCount() {
    return _messages.size();
  }

  /** Returns whether or not we have reached the maximum number of errors. */
  public boolean queryFull() {
    return _messages.size() >= _maxErrorCount;
  }

  /** Returns a string representing the errors we have encounterd, separated by newlines. */
  public String queryCollectedMessages() {
    StringBuilder ret = new StringBuilder();
    for (int i = 0; i < _messages.size(); i++) ret.append(_messages.get(i) + "\n");
    return ret.toString();
  }
}

