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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * A utility that is used to call an external process (without writing a file).
 */
public class ProcessCaller {
  private final int _timeout;
  private final ProcessBuilder _processBuilder;

  /**
   * Create a process caller for the given command / argument list, with the given timeout
   * (in seconds)
   */
  public ProcessCaller(List<String> cmd, int timeout) {
    _timeout = timeout;

    List<String> systemCommands =
      ProcessCaller.callSystemBash();
    systemCommands.addAll(cmd);

    _processBuilder = new ProcessBuilder(systemCommands);
    _processBuilder.redirectErrorStream(true);
  }

  /**
   * This sets a timeout handler and runs the process.  If the process times out, then this is
   * immediately handled, and null is returned.  Otherwise, the process is returned, so its input
   * stream can be read.
   */
  private Process callProcess() throws IOException, InterruptedException {
    Process process = null;
    process = _processBuilder.start();

    final boolean exited = process.waitFor(_timeout, TimeUnit.SECONDS);
    if (!exited) {
      // we did not finish within the timeout
      process.destroy();
      Runtime.getRuntime().exit(1);
      return null;
    }

    return process;
  }

  /**
   * This function calls the process, waits for it to complete or time out, and returns the result
   * as an InputStream.
   */
  public Optional<InputStream> getResultAsInputStream() throws IOException, InterruptedException {
    Process process = callProcess();
    if (process == null) return Optional.empty();
//    process.onExit().get();
    return Optional.of(process.getInputStream());
  }

  /**
   * This function calls the process, waits for it to complete or time out, reads the result into a
   * string and returns it.
   */
  public Optional<String> getResultAsString() throws IOException, InterruptedException,
    ExecutionException {
    Process process = callProcess();
    if (process == null) return Optional.empty();
    process.onExit().get();
    String processResult = bufferToString(process.getInputStream());
    return Optional.of(processResult);
  }

  /**
   * Helper function for getResultAsString: this reads the given input stream into a String.
   */
  private static String bufferToString(InputStream inputStream) throws IOException {
    BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream));
    return reader.lines().collect(Collectors.joining(System.lineSeparator()));
  }

  static List<String> callSystemBash() {
    if (SystemUtils.IS_OS_WINDOWS) {
      return new ArrayList<>(List.of("Powershell", "-Command"));
    }
    if (SystemUtils.IS_UNIX_LIKE) {
      return new ArrayList<>(List.of("/bin/sh", "-c"));
    }
    return List.of();
  }

  public static String callSystemEcho(String echoString) {
    if (SystemUtils.IS_OS_WINDOWS) {
      return "Write-Output '" + echoString + "'";
    }
    if (SystemUtils.IS_UNIX_LIKE) {
      return "echo \"" + echoString + "\"";
    }
    return echoString;
  }

}
