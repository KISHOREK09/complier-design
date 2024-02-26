%{
#include <stdio.h>
%}

VOWEL       [aeiouAEIOU]
LETTER      [a-zA-Z]

%%

^{VOWEL}{LETTER}*   { printf("Valid String: %s\n", yytext); }
.                   { printf("Invalid String: %s\n", yytext); }

%%

int main() {
    printf("Enter a string:\n");
    yylex();
    return 0;
}
