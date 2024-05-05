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

package charlie.util;

/**
 * When some process in Cora runs into an Exception or Error, they may pass it on to the caller, or
 * they may wish to handle it on the spot.  However ,the latter option runs the risk of hiding that
 * an error took place.  This handler can be used to log the error to ensure that errors are
 * noticed during testing.
 */
public class ExceptionLogger {
  private static boolean _enabled = true;

  /** If disabled, errors will be ignored.  Use this for example when demonstrating to end users. */
  public static void disable() { _enabled = false; }

  /** If enabled, errors will be handled as usual again.  (Only needed after disable().) */
  public static void enable() { _enabled = true; }

  /** Prints the given message to stderr, followed by a stack trace of the Exception. */
  public static void log(String message, Exception e) {
    System.err.println(message);
    e.printStackTrace();
  }

  /** Prints the given message to stderr, followed by a stack trace of the Error. */
  public static void log(String message, Error e) {
    System.err.println(message);
    e.printStackTrace();
  }

  /** Prints the error message for the given exception to stderr, followed by a stack trace. */
  public static void log(Exception e) {
    log(e.getMessage(), e);
  }
}
