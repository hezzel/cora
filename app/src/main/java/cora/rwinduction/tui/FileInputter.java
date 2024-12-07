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

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.Scanner;
import java.util.Stack;
import charlie.util.ExceptionLogger;

/**
 * The FileInputter adapts a given Inputter by first reading input from a file, and only once the
 * file is emptied out, returning the result of the given Inputter.
 */
public class FileInputter implements Inputter {
  private Inputter _child;
  private BufferedReader _reader;

  public FileInputter(String filename, Inputter child) throws IOException {
    _child = child;
    _reader = new BufferedReader(new FileReader(filename));
  }

  /** Creates a File Inputter that returns :quit after getting through the file. */
  public FileInputter(String filename) throws IOException {
    _child = new QuitInputter();
    _reader = new BufferedReader(new FileReader(filename));
  }

  private String tryReadFromReader() {
    if (_reader == null) return null;
    try {
      String line = _reader.readLine();
      if (line != null) return line;
    }
    catch (IOException e) {
      ExceptionLogger.log("Encountered IOException while trying to read from file.", e);
    }
    _reader = null;
    return null;
  }

  public String readLine() {
    String ret = tryReadFromReader();
    if (ret != null) return ret;
    return _child.readLine();
  }

  public String readLine(String prompt) {
    String ret = tryReadFromReader();
    if (ret != null) return ret;
    return _child.readLine(prompt);
  }

  public void close() {
    _child.close();
  }
}

