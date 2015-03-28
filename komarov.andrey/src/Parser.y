{
module Parser (
       parse
) where

import Lexer
import AST

}

%name parse
%tokentype { Token }
%error { parseError }

%token
        '('             { TokenLParen }
        ')'             { TokenRParen }
        '{'             { TokenLBrace }
        '}'             { TokenRBrace }
        '['             { TokenLBracket }
        ']'             { TokenRBracket }
        '+'             { TokenAdd }
        '-'             { TokenSub }
        '*'             { TokenMul }
        '&'             { TokenAmp }
        '<'             { TokenLess }
        '>'             { TokenGreater }
        '=='            { TokenEqual }
        '<='            { TokenLessEq }
        '>='            { TokenGreaterEq }
        '!='            { TokenNotEqual }
        '&&'            { TokenAnd }
        '||'            { TokenOr }
        '='             { TokenAssign }
        ';'             { TokenSemicolon }
        if              { TokenIf }
        else            { TokenElse }
        while           { TokenWhile }
        return          { TokenReturn }
        num             { TokenNum $$ }
        true            { TokenTrue }
        false           { TokenFalse }
        var             { TokenVar $$ }
        ','             { TokenComma }

%left ','
%right '='
%left '||' '&&'
%nonassoc '==' '!='
%nonassoc '<' '>' '<=' '>='
%left '+' '-'
%left '*'
%left '&' DEREF CAST
%nonassoc '[' ']'


%%

Prog            : TopLevelDefs                  { Program $1 }

TopLevelDefs    : {- empty -}                   { [] }
                | TopLevel TopLevelDefs         { $1:$2 }

TopLevel        : VarDecl                       { $1 }
                | ForwardDecl                   { $1 }
                | FuncDef                       { $1 }

VarDecl         : Type var ';'                  { VarDecl $1 $2 }

ForwardDecl     : Type var '(' FuncArgs ')' ';' { ForwardDecl $2 $1 (map fst $4) }

FuncDef         : Type var '(' FuncArgs ')' '{' Stmts '}' { FuncDef $2 $1 $4 $7 }

Expr            : var                           { EVar $1 }
                | num                           { EInt $1 }
                | true                          { EBool True }
                | false                         { EBool False }
                | '(' Expr ')'                  { $2 }
                | Expr '+' Expr                 { EAdd $1 $3 }
                | Expr '-' Expr                 { ESub $1 $3 }
                | Expr '*' Expr                 { EMul $1 $3 }
                | Expr '<' Expr                 { ELess $1 $3 }
                | Expr '>' Expr                 { EGreater $1 $3 }
                | Expr '==' Expr                { EEqual $1 $3 }
                | Expr '<=' Expr                { ELessEq $1 $3 }
                | Expr '>=' Expr                { EGreaterEq $1 $3 }
                | Expr '!=' Expr                { ENotEqual $1 $3 }
                | Expr '&&' Expr                { EAnd $1 $3 }
                | Expr '||' Expr                { EOr $1 $3 }
                | var '(' FuncCallList ')'      { ECall $1 $3 }
                | '&' Expr                      { EAddr $2 }
                | '*' Expr %prec DEREF          { EDeref $2 }
                | Expr '[' Expr ']'             { EArray $1 $3 }
                | Expr '=' Expr                 { EAssign $1 $3 }
                | '(' Type ')' Expr %prec CAST  { ECast $2 $4 }

FuncCallList    : {- empty -}                   { [] }
                | Expr                          { [$1] }
                | Expr ',' FuncCallList         { $1:$3 }

Stmt            : '{' Stmts '}'                 { SBlock $2 }
                | Type var ';'                  { SVarDecl $1 $2 }
                | Expr ';'                      { SRawExpr $1 }
                | if '(' Expr ')' Stmt else Stmt  { SIfThenElse $3 $5 $7 }
                | while '(' Expr ')' Stmt       { SWhile $3 $5 }
                | return Expr ';'               { SReturn $2 }

Stmts           : {- empty -}                   { [] }
                | Stmt Stmts                    { $1:$2 }

FuncArgs        : {- empty -}                   { [] }
                | Type var                      { [($1, $2)] }
                | Type var ',' FuncArgs         { ($1, $2):$4 }

Type            : var                           { Simple $1 }
                | '*' Type                      { Pointer $2 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"
}
