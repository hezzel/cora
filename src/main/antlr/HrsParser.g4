/**************************************************************************************************
 Copyright 2020 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

/** This is a parser for the standard .hrs format of the confluence competition. */
parser grammar HrsParser;

@header {
package cora.parsers;
}

options {
  tokenVocab = HrsLexer;
}

type                : IDENTIFIER
                    | IDENTIFIER ARROW type
                    | BRACKETOPEN type BRACKETCLOSE
                    | BRACKETOPEN type BRACKETCLOSE ARROW type
                    ;

fulltype            : type EOF ;

sig                 : 
                    | IDENTIFIER DECLARE type sig
                    ;

signature           : VARSDECSTART sig BRACKETCLOSE FUNSDECSTART sig BRACKETCLOSE
                    | FUNSDECSTART sig BRACKETCLOSE VARSDECSTART sig BRACKETCLOSE
                    ;

term                : basicterm* (basicterm | abstraction) ;

abstraction         : LAMBDA IDENTIFIER* DOT term ;

basicterm           : IDENTIFIER
                    | BRACKETOPEN termlist BRACKETCLOSE
                    ;

termlist            : term
                    | term COMMA termlist
                    ;

fullterm            : term EOF ;
                    
hrsrule             : term ARROW term ;

ruleslist           :
                    | hrsrule
                    | hrsrule COMMA ruleslist
                    ;

hrs                 : signature RULESDECSTART ruleslist BRACKETCLOSE EOF ;

