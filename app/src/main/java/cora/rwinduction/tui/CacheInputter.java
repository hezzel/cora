/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.tui;

import java.util.List;
import java.util.ListIterator;
import java.util.Scanner;
import java.util.Stack;

/**
 * The CacheInputter adapts a given Inputter by first returning a list of stored strings, and only
 * once the pre-given list is exhausted, returning the result of the given Inputter.
 */
public class CacheInputter implements Inputter {
  private Inputter _child;
  private Stack<String> _cache;

  /**
   * Creates a Cache Inputter that first returns everything in the given list (in that order),
   * and then passes control to the child.
   */
  public CacheInputter(List<String> cached, Inputter child) {
    _child = child;
    _cache = new Stack<String>();
    ListIterator<String> li = cached.listIterator(cached.size());
    while (li.hasPrevious()) _cache.push(li.previous());
  }

  public CacheInputter(Inputter child) {
    _child = child;
    _cache = new Stack<String>();
  }

  /** Creates a Cache Inputter that returns :quit after getting through all the cached input. */
  public CacheInputter() {
    _child = new QuitInputter();
    _cache = new Stack<String>();
  }

  /**
   * Stores the given string as the line to be returned next.  It is allowed to call this multiple
   * times; all cached strings will be returned, in reverse order of caching them.
   */
  public void cache(String str) {
    _cache.push(str);
  }

  public String readLine() {
    if (_cache.empty()) return _child.readLine();
    return _cache.pop();
  }

  public String readLine(String prompt) {
    if (_cache.empty()) return _child.readLine(prompt);
    return _cache.pop();
  }

  public void close() {
    _child.close();
  }
}

