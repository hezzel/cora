package charlie.util;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class ProcessCallerTest {

  @Test
  void callingTest() {

    List<String> commands = new ArrayList<>(Arrays.asList("z3", "--version"));

    ProcessCaller pc = new ProcessCaller(commands, 1);

    String result = pc.inputStreamToString();

    System.out.println(result);

  }

}
