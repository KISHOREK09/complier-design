%{
#include <stdio.h>
#include <string.h>

#define MAX_LEN 100

int keyword_count = 0;
int identifier_count = 0;
%}

DIGIT       [0-9]
LETTER      [a-zA-Z]
ID          {LETTER}({LETTER}|{DIGIT})*
KEYWORD     if|else|while|for|int|float|char|void|return|break|continue|switch|case|default|do|sizeof|struct|typedef|auto|extern|register|static|const|volatile|unsigned|signed|long|short|double|_Bool|_Complex|_Imaginary
SPACE       [ \t\n]

%%

{KEYWORD}   { printf("KEYWORD: %s\n", yytext); keyword_count++; }
{ID}        { printf("IDENTIFIER: %s\n", yytext); identifier_count++; }
{SPACE}     ;  // Ignore spaces, tabs, and newlines

.           ;

%%

int main() {
    char input[MAX_LEN];
    printf("Enter a program:\n");

    while (fgets(input, MAX_LEN, stdin) != NULL) {
        yy_scan_string(input);
        yylex();
    }

    printf("Number of Keywords: %d\n", keyword_count);
    printf("Number of Identifiers: %d\n", identifier_count);

    return 0;
}
