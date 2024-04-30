package charlie.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

public class ProcessCaller {
  private List<String> _command;
  private int _timeout;

  private ProcessBuilder _processBuilder;

  public ProcessCaller(List<String> cmd, int timeout) {
    _command = cmd;
    _timeout = timeout;

    _processBuilder = new ProcessBuilder(_command);
    _processBuilder.redirectErrorStream(true);
//    _processBuilder.inheritIO();
  }

//  Implement a timeout handler that whenever the process times out,
//  this handler is called.
  private Process callProcess() {

    Process process = null;
    try {
      process = _processBuilder.start();
    } catch (IOException e) {
      throw new RuntimeException(e);
    }

    try {
      final boolean exited = process.waitFor(_timeout, TimeUnit.SECONDS);
      if(!exited) {
        System.err.println(STR."RUNTIME TIMEOUT: \{_command.getFirst()} did not finish " +
          STR."within \{_timeout} seconds, exiting.");
        process.destroy();
        Runtime.getRuntime().exit(1);
      }
    } catch (final InterruptedException ex) {
      System.err.println(STR."ERROR: \{_command.getFirst()}process had not finished before its thread got interrupted, exiting application now.");
      ex.printStackTrace();
    }

    return process;
  }

  public InputStream getInputStream() {
    Process process = callProcess();

    return process.getInputStream();
  }

  public String inputStreamToString() {
    Process process = callProcess();
    String processResult = "";
    try {
      process.onExit().get();
      processResult = bufferToString(process.getInputStream());
    } catch (InterruptedException | ExecutionException e) {
      System.err.println("IO Exception caught");
      e.printStackTrace();
    }
    return processResult;
  }

  private static String bufferToString(InputStream inputStream) {
    String ret = "";

    try (BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream))) {
      ret = reader.lines()
        .collect(Collectors.joining(System.lineSeparator()));
    } catch (IOException e) {
      System.err.println("Caught IOException when reading process InputStreamBuffer. See the stack trace below.");
      e.printStackTrace();
    }
    return ret;
  }

}
