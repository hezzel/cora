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
    assertTrue(param.queryRequest() == Parameters.Request.Smt);
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
    assertTrue(Settings.disabled.size() == 3);
    assertTrue(Settings.disabled.contains("dp"));
    assertTrue(Settings.disabled.contains("graph"));
    assertTrue(Settings.disabled.contains("imap"));
  }

  @Test
  public void testIllegalDisable() {
    Parameters param = new Parameters(new String[] { "myfile", "-d", "dp,extra,graph" });
    assertThrows(Parameters.WrongParametersException.class, () -> param.setupSettings());
  }
}

