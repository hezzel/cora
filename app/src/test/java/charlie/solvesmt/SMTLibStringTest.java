package charlie.solvesmt;
import charlie.smt.*;
import charlie.util.ProcessCaller;
import org.junit.jupiter.api.Test;
import java.util.ArrayList;
import java.util.List;

class SMTLibStringTest {

  @Test
  void buildSmtlibString() {

    SmtProblem smtProblem = new SmtProblem();

    IVar iVar = SmtFactory.createIntegerVariable(smtProblem);
    IVar iVar2 = SmtFactory.createIntegerVariable(smtProblem);

    Constraint c = SmtFactory.createGeq(iVar, iVar2);

    smtProblem.require(c);

//    SMTLibString file = new SMTLibString(SMTLibString.Version.V26, SMTLibString.Logic.QFNIA);

//    System.out.println(file.buildSmtlibString(smtProblem));

    ProcessSmtSolver solver = new ProcessSmtSolver();

    SmtSolver.Answer a = solver.checkSatisfiability(smtProblem);

    boolean b = solver.checkValidity(smtProblem);

    System.out.println("Satisfiability problem: " + a);
    System.out.println("Validity problem: " + b);

//    System.out.println(pc.inputStreamToString());

//    InputStream inputStream = pc.getInputStream();
//
//    Scanner scanner = new Scanner(inputStream);
//    while (scanner.hasNextLine()) {
//      System.out.println(scanner.nextLine());
//    }


//    String result = pc.inputStreamToString();

//    System.out.println(result);



  }
}
