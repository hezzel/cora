/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.exceptions;

/**
 * A NullStorageException is thrown when either we try to create an object with a null argument, or
 * an existing object is updated with a null argument.  Either way, a null object would be stored
 * where null is not expected, which could cause problems later in the program.
 */
public class NullStorageException extends RuntimeException {
  public NullStorageException(String classname, String message) {
    super("Trying to store a null argument in " + classname + ": " + message + ".");
  }
}

