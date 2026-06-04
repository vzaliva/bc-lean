; highlights.scm for GNU bc

(comment) @comment
(string) @string
(number) @number
(identifier) @identifier

[
  "define" "auto" "if" "else" "while" "for" "break" "continue" "return"
  "quit" "halt" "print" "warranty" "limits" "void" "read" "random"
  "length" "sqrt" "scale" "ibase" "obase" "last" "history"
] @keyword

[
  "+" "-" "*" "/" "%" "^"
  "&&" "||" "!"
  "==" "!=" "<=" ">=" "<" ">"
  "=" "+=" "-=" "*=" "/=" "%=" "^="
  "++" "--"
  ";" "," "." "(" ")" "{" "}" "[" "]"
] @operator
