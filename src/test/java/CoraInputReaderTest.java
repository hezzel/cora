/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

import org.junit.Test;
import static org.junit.Assert.*;
import cora.exceptions.ParserException;
import cora.interfaces.types.Type;
import cora.parsers.CoraInputReader;

public class CoraInputReaderTest {
  @Test
  public void testReadTypeValidType() throws ParserException {
    String str = "a -> (b -> cd) -> e";
    Type type = CoraInputReader.readTypeFromString(str);
    assertTrue(type.queryTypeKind() == Type.TypeKind.ARROWTYPE);
    Type a = type.queryArrowInputType();
    Type bcde = type.queryArrowOutputType();
    assertTrue(a.queryTypeKind() == Type.TypeKind.BASETYPE);
    assertTrue(bcde.queryTypeKind() == Type.TypeKind.ARROWTYPE);
    Type bcd = bcde.queryArrowInputType();
    assertTrue(bcd.queryTypeKind() == Type.TypeKind.ARROWTYPE);
    assertTrue(bcd.queryArrowInputType().toString().equals("b"));
    assertTrue(bcd.queryArrowOutputType().toString().equals("cd"));
    Type e = bcde.queryArrowOutputType();
    assertTrue(e.queryTypeKind() == Type.TypeKind.BASETYPE);
  }
}

