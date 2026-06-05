; highlights.scm for POSIX bc

(comment) @comment
(string) @string
(number) @number
(identifier) @identifier

[
  "define" "auto" "if" "while" "for" "break" "return"
  "quit" "length" "sqrt" "scale" "ibase" "obase"
] @keyword

[
  "+" "-" "*" "/" "%" "^"
  "==" "!=" "<=" ">=" "<" ">"
  "=" "+=" "-=" "*=" "/=" "%=" "^="
  "++" "--"
  ";" "," "." "(" ")" "{" "}" "[" "]"
] @operator
