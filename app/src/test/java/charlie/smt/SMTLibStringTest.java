package charlie.smt;

import charlie.util.ProcessCaller;
import org.junit.jupiter.api.Test;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import static org.junit.jupiter.api.Assertions.*;

class SMTLibStringTest {

  @Test
  void buildSmtlibString() {

    SmtProblem smtProblem = new SmtProblem();

    IVar iVar = SmtFactory.createIntegerVariable(smtProblem);
    IVar iVar2 = SmtFactory.createIntegerVariable(smtProblem);

    Constraint c = SmtFactory.createGeq(iVar, iVar2);

    smtProblem.require(c);

    SMTLibString file = new SMTLibString(SMTLibString.Version.V26, SMTLibString.Logic.QFNIA);

    System.out.println(file.buildSmtlibString(smtProblem));

    List<String> command = new ArrayList<>();
    command.add("/bin/sh");
    command.add("-c");
//    command.add("echo \"(set-logic QF_NIA) (assert true) (check-sat) (get-model) \" | z3 -in");
//    command.add("z3");
//    command.add("-smt2");
//    command.add("--version");
    command.add (
      "echo \"" +
      file.buildSmtlibString(smtProblem) +
      " \" " +
        "| z3 -in "
    );

    ProcessCaller pc = new ProcessCaller(command, 100);

    InputStream inputStream = pc.getInputStream();

    Scanner scanner = new Scanner(inputStream);
    while (scanner.hasNextLine()) {
      System.out.println(scanner.nextLine());
    }


//    String result = pc.inputStreamToString();

//    System.out.println(result);



  }
}
