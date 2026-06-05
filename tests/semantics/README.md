# Future semantics/context fixtures

These files are not parser fixtures. They cover POSIX context-sensitive or
semantic cases such as `return` and `break` placement. Do not include them in
`make parser-test`, `make test`, or AST golden updates until a
semantics/context-checking phase is added.
