package cora.rwinduction.tui;

import charlie.reader.CoraInputReader;
import charlie.trs.TRS;
import cora.io.DefaultOutputModule;
import cora.io.OutputModule;
import cora.rwinduction.engine.Interpreter;
import cora.rwinduction.engine.Prover;
import cora.rwinduction.engine.data.ProverContext;
import org.jline.console.ArgDesc;
import org.jline.console.CmdDesc;
import org.jline.reader.*;
import org.jline.reader.impl.DefaultHighlighter;
import org.jline.reader.impl.DefaultParser;
import org.jline.reader.impl.completer.ArgumentCompleter;
import org.jline.reader.impl.completer.StringsCompleter;
import org.jline.terminal.Terminal;
import org.jline.terminal.TerminalBuilder;
import org.jline.widget.AutosuggestionWidgets;

import java.io.IOException;
import org.jline.utils.AttributedString;
import org.jline.widget.TailTipWidgets;

import java.util.*;

public class KeyStrokeListener {

  public void test() {
    try (Terminal terminal = TerminalBuilder.terminal()) {
      terminal.enterRawMode();

      terminal.writer().println("Terminal: " + terminal);
      terminal.writer()
        .println("Type characters, which will be echoed to the console. Q will exit.");
      terminal.writer().println();
      terminal.writer().flush();

      Completer testCompleter = new ArgumentCompleter(
        new StringsCompleter("simplify"),
        new StringsCompleter("delete"),
        new StringsCompleter("widget"),
        new StringsCompleter(":quit")
      );

      LineReader lineReader = LineReaderBuilder.builder()
        .terminal(terminal)
        .completer(testCompleter)
        .highlighter(new DefaultHighlighter())
        .parser(new DefaultParser())
        .build();

      // Enable tail-end explanations of each command
      Map<String, CmdDesc> tailTips = new HashMap<>();
      Map<String, List<AttributedString>> widgetsOpts = new HashMap<>();
      List<AttributedString> mainDescription =
        Arrays.asList(
          new AttributedString("widget -N new-widget [function-name]"),
          new AttributedString("widget -d ...")
        );

      widgetsOpts.put("-N", Arrays.asList(new AttributedString("Create new widget")));
      widgetsOpts.put("-D", Arrays.asList(new AttributedString("Delete widgets")));
      widgetsOpts.put("-A", Arrays.asList(new AttributedString("Create alias to widget")));
      widgetsOpts.put("-U", Arrays.asList(new AttributedString("Push characters to the stack")));
      widgetsOpts.put("-l", Arrays.asList(new AttributedString("List user-defined widgets")));

      CmdDesc desc = new CmdDesc(
        mainDescription,
        ArgDesc.doArgNames(Arrays.asList("args", "options")),
        widgetsOpts
      );

      tailTips.put("widget", desc);

      TailTipWidgets tailTipWidgets =
        new TailTipWidgets(lineReader, tailTips, 10, TailTipWidgets.TipType.TAIL_TIP);

      tailTipWidgets.enable();

      // Enable auto-suggestions for commands
      AutosuggestionWidgets autosuggestionWidgets = new AutosuggestionWidgets(lineReader);
      autosuggestionWidgets.enable();

      TRS trs = CoraInputReader.readTrsFromString (
        "sum :: Int -> Int\n" +
        "sum(x) -> 0         | x ≤ 0\n" +
        "sum(x) -> x + sum(x - 1) | x > 0"
      );

//      Prover prover =
//        new Prover(new ProverContext(trs, DefaultOutputModule.createUnicodeModule(trs)));

//      OutputModule outputModule = prover.getProverContext().getOutputModule();

      while (true) {
        String c = lineReader.readLine("> ");

        System.out.println(c.trim().split("simplify 1 0.256 with [x := f(x)]"));


//        outputModule.printTrs(trs);
//        outputModule.printToStdout();
//        outputModule.clear();

        Interpreter.interpreter.accept(c);

        if (c == null) break;
      }
    } catch (UserInterruptException e) {
      System.out.println("User interrupted");

    } catch (EndOfFileException e) {
      return;
    } catch (IOException e) {
      e.printStackTrace();
    }
  }
}
