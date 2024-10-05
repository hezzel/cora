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

package cora;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.config.Settings;

class ParametersTest {
  @Test
  public void testRequestTermination() {
    Parameters param = new Parameters(new String[] { "-y", "plain", "--termination", "xx" });
    assertTrue(param.queryRequest() == Parameters.Request.Termination);
    assertTrue(param.querySingleFile().equals("xx"));
    param = new Parameters(new String[] { "a", "", "-t" });
    assertTrue(param.queryRequest() == Parameters.Request.Termination);
    assertTrue(param.querySingleFile().equals("a"));
  }

  @Test
  public void testRequestPrinting() {
    Parameters param = new Parameters(new String[] { "-p", "test" });
    assertTrue(param.queryRequest() == Parameters.Request.Print);
    assertTrue(param.querySingleFile().equals("test"));
    param = new Parameters(new String[] { "--print" });
    assertTrue(param.queryRequest() == Parameters.Request.Print);
  }

  @Test
  public void testRequestReduction() {
    Parameters param = new Parameters(new String[] { "input", "-r", "f", "(x", "-y", ")" });
    assertTrue(param.queryRequest() == Parameters.Request.Reduce);
    assertTrue(param.querySingleFile().equals("input"));
    assertTrue(param.queryModuleInput().size() == 1);
    assertTrue(param.queryModuleInput().get(0).equals("f(x-y)"));
  }

  @Test
  public void testRequestNothing() {
    Parameters param = new Parameters(new String[] { "input", "more input" });
    assertTrue(param.queryRequest() == Parameters.Request.Termination);
  }

  @Test
  public void testMultipleRequests() {
    assertThrows(Parameters.WrongParametersException.class, () ->
      new Parameters(new String[] { "x", "--print", "--horpo" }));
    Parameters param = new Parameters(new String[] { "--print", "test", "-p" });
    assertTrue(param.queryRequest() == Parameters.Request.Print);
    assertTrue(param.querySingleFile().equals("test"));
  }

  @Test
  public void testRequestPlainStyle() {
    Parameters param = new Parameters(new String[] { "--print", "test", "-y", "plain" });
    OutputModule m = param.queryOutputModule();
    m.print("%{alpha}");
    assertTrue(m.toString().equals("alpha"));
  }

  @Test
  public void testRequestUnicodeStyle() {
    Parameters param = new Parameters(new String[] { "--print", "test", "-y", "UNICODE" });
    OutputModule m = param.queryOutputModule(CoraInputReader.readTrsFromString(""));
    m.print("%{alpha}");
    assertTrue(m.toString().equals("α"));
  }

  @Test
  public void testRequestNoStyle() {
    Parameters param = new Parameters(new String[] { "--print", "test", "-y", "UNICODE" });
    OutputModule m = param.queryOutputModule();
    m.print("%{alpha}");
    assertTrue(m.toString().equals("α"));
  }

  @Test
  public void testRequestBadStyle() {
    assertThrows(Parameters.WrongParametersException.class, () ->
      new Parameters(new String[] { "--style", "pain" }));
  }

  @Test
  public void testRequestFullStrategy() {
    Parameters param = new Parameters(new String[] { "--strategy", "full" });
    param.setupSettings();
    assertTrue(Settings.queryRewritingStrategy() == Settings.Strategy.Full);
  }

  @Test
  public void testRequestInnermostStrategy() {
    Parameters param = new Parameters(new String[] { "--strategy", "innermost" });
    param.setupSettings();
    assertTrue(Settings.queryRewritingStrategy() == Settings.Strategy.Innermost);
  }

  @Test
  public void testRequestCBVStrategy() {
    Parameters param = new Parameters(new String[] { "--print", "-g", "cbv" });
    param.setupSettings();
    assertTrue(Settings.queryRewritingStrategy() == Settings.Strategy.CallByValue);
    param = new Parameters(new String[] { "--strategy", "call-by-value" });
    param.setupSettings();
    assertTrue(Settings.queryRewritingStrategy() == Settings.Strategy.CallByValue);
  }

  @Test
  public void testRequestNoStrategy() {
    Parameters param = new Parameters(new String[] { "--print" });
    param.setupSettings();
    assertTrue(Settings.queryRewritingStrategy() == Settings.Strategy.Full);
  }

  @Test
  public void testRequestStrategyWithoutStrategy() {
    assertThrows(Parameters.WrongParametersException.class, () ->
      new Parameters(new String[] { "--print", "-g" }) );
  }

  @Test
  public void testRequestBadStrategy() {
    assertThrows(Parameters.WrongParametersException.class, () ->
      new Parameters(new String[] { "--print", "--strategy", "inner" }) );
  }

  @Test
  public void testRequestDoubleStrategy() {
    assertThrows(Parameters.WrongParametersException.class, () ->
      new Parameters(new String[] { "-g", "cbv", "--print", "--strategy", "call-by-value" }) );
  }

  @Test
  public void testFileRequests() {
    Parameters param = new Parameters(new String[] { "--termination" }); // no files
    assertThrows(Parameters.WrongParametersException.class, () -> param.querySingleFile());
    assertTrue(param.queryFiles().size() == 0);
    Parameters param2 = new Parameters(new String[] { "file1", "--print", "file2" }); // two files
    assertThrows(Parameters.WrongParametersException.class, () -> param2.querySingleFile());
    assertTrue(param2.queryFiles().size() == 2);
    assertTrue(param2.queryFiles().get(0).equals("file1"));
    assertTrue(param2.queryFiles().get(1).equals("file2"));
  }

  @Test
  public void testIllegalParameters() {
    assertThrows(Parameters.WrongParametersException.class, () ->
      new Parameters(new String[] { "--style", "plain", "-myfile.txt" }));
  }

  @Test
  public void testDisable() {
    Parameters param = new Parameters(new String[] {
      "myfile", "-d", "dp,graph", "--disable", "dp,imap" });
    param.setupSettings();
    assertTrue(Settings.isDisabled("dp"));
    assertTrue(Settings.isDisabled("graph"));
    assertTrue(Settings.isDisabled("imap"));
    assertFalse(Settings.isDisabled("subcrit"));
  }

  @Test
  public void testIllegalDisable() {
    Parameters param = new Parameters(new String[] { "myfile", "-d", "dp,extra,graph" });
    assertThrows(Parameters.WrongParametersException.class, () -> param.setupSettings());
  }
}

