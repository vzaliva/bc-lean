/**
 * @file GNU bc 1.07.1 grammar for tree-sitter
 * @license GPL-3.0-or-later
 *
 * Derived from bc-1.07.1/bc/bc.y and bc-1.07.1/bc/scan.l
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

module.exports = grammar({
  name: "bc",

  extras: $ => [
    /[ \t\r\f]+/,
    $.block_comment,
    $.line_comment,
    $.line_continuation,
  ],

  conflicts: $ => [
    [$._body_item],
    [$.primary_expression, $.named_expression],
  ],

  rules: {
    source_file: $ => repeat($._top_level_item),

    _top_level_item: $ => choice(
      $.function_definition,
      $.newline,
      seq($.statement_sequence, $.newline),
    ),

    statement_sequence: $ => prec.left(repeat1(choice(
      seq($.statement, optional(";")),
      ";",
    ))),

    function_definition: $ => seq(
      "define",
      optional("void"),
      field("name", $.identifier),
      "(",
      optional($.parameter_list),
      ")",
      optional($.newline),
      "{",
      repeat($._body_item),
      "}",
    ),

    _body_item: $ => choice(
      seq($.statement_sequence, optional($.newline)),
      $.newline,
    ),

    parameter_list: $ => $.define_list,

    define_list: $ => seq(
      $.define_item,
      repeat(seq(",", $.define_item)),
    ),

    define_item: $ => choice(
      field("name", $.identifier),
      seq(field("name", $.identifier), "[", "]"),
      seq("*", field("name", $.identifier), "[", "]"),
      seq("&", field("name", $.identifier), "[", "]"),
    ),

    statement: $ => choice(
      $.expression_statement,
      $.string_statement,
      $.auto_statement,
      $.if_statement,
      $.while_statement,
      $.for_statement,
      $.break_statement,
      $.continue_statement,
      $.return_statement,
      $.quit_statement,
      $.halt_statement,
      $.print_statement,
      $.warranty_statement,
      $.limits_statement,
      $.block_statement,
    ),

    expression_statement: $ => $.expression,

    string_statement: $ => $.string,

    auto_statement: $ => seq(
      "auto",
      $.define_list,
    ),

    if_statement: $ => prec.right(seq(
      "if",
      "(",
      field("condition", $.expression),
      ")",
      optional($.newline),
      field("consequence", $.statement),
      optional(field("alternative", $.else_clause)),
    )),

    else_clause: $ => seq(
      "else",
      optional($.newline),
      $.statement,
    ),

    while_statement: $ => seq(
      "while",
      "(",
      field("condition", $.expression),
      ")",
      optional($.newline),
      field("body", $.statement),
    ),

    for_statement: $ => seq(
      "for",
      "(",
      field("init", optional($.expression)),
      ";",
      field("condition", optional($.expression)),
      ";",
      field("update", optional($.expression)),
      ")",
      optional($.newline),
      field("body", $.statement),
    ),

    break_statement: $ => "break",
    continue_statement: $ => "continue",
    quit_statement: $ => "quit",
    halt_statement: $ => "halt",
    warranty_statement: $ => "warranty",
    limits_statement: $ => "limits",

    return_statement: $ => prec.left(seq(
      "return",
      optional($.expression),
    )),

    print_statement: $ => seq(
      "print",
      $.print_list,
    ),

    print_list: $ => seq(
      $.print_element,
      repeat(seq(",", $.print_element)),
    ),

    print_element: $ => choice($.string, $.expression),

    block_statement: $ => seq(
      "{",
      repeat($._body_item),
      "}",
    ),

    expression: $ => choice(
      $.assignment_expression,
      $.logical_or_expression,
    ),

    assignment_expression: $ => prec.right(1, seq(
      field("left", $.named_expression),
      field("operator", $.assign_op),
      field("right", $.expression),
    )),

    assign_op: $ => choice(
      "=", "+=", "-=", "*=", "/=", "%=", "^=",
    ),

    logical_or_expression: $ => prec.left(2, seq(
      $.logical_and_expression,
      repeat(seq(
        "||",
        field("right", $.logical_and_expression),
      )),
    )),

    logical_and_expression: $ => prec.left(3, seq(
      $.logical_not_expression,
      repeat(seq(
        "&&",
        field("right", $.logical_not_expression),
      )),
    )),

    logical_not_expression: $ => choice(
      prec(4, seq("!", field("operand", $.relational_expression))),
      $.relational_expression,
    ),

    relational_expression: $ => prec.left(5, seq(
      $.additive_expression,
      repeat(seq(
        field("operator", $.rel_op),
        field("right", $.additive_expression),
      )),
    )),

    rel_op: $ => choice("==", "!=", "<=", ">=", "<", ">"),

    additive_expression: $ => prec.left(6, seq(
      $.multiplicative_expression,
      repeat(seq(
        field("operator", choice("+", "-")),
        field("right", $.multiplicative_expression),
      )),
    )),

    multiplicative_expression: $ => prec.left(7, seq(
      $.power_expression,
      repeat(seq(
        field("operator", choice("*", "/", "%")),
        field("right", $.power_expression),
      )),
    )),

    power_expression: $ => prec.right(8, seq(
      $.unary_expression,
      repeat(seq(
        "^",
        field("right", $.unary_expression),
      )),
    )),

    unary_expression: $ => choice(
      prec(9, seq(
        field("operator", "-"),
        field("operand", $.unary_expression),
      )),
      prec(9, seq(
        field("operator", choice("++", "--")),
        field("operand", $.named_expression),
      )),
      $.postfix_expression,
    ),

    postfix_expression: $ => choice(
      prec(10, seq(
        field("operand", $.named_expression),
        field("operator", choice("++", "--")),
      )),
      $.primary_expression,
    ),

    primary_expression: $ => choice(
      $.number,
      $.identifier,
      $.array_element,
      $.special_variable,
      $.function_call,
      $.builtin_call,
      $.parenthesized_expression,
    ),

    array_element: $ => seq(
      field("array", $.identifier),
      "[",
      field("index", $.expression),
      "]",
    ),

    special_variable: $ => prec(1, choice(
      "ibase",
      "obase",
      "scale",
      "last",
      "history",
      ".",
    )),

    function_call: $ => prec(2, seq(
      field("name", $.identifier),
      "(",
      optional($.argument_list),
      ")",
    )),

    argument_list: $ => seq(
      $.argument,
      repeat(seq(",", $.argument)),
    ),

    argument: $ => choice(
      $.expression,
      seq(field("array", $.identifier), "[", "]"),
    ),

    builtin_call: $ => prec(2, choice(
      seq("length", "(", field("argument", $.expression), ")"),
      seq("sqrt", "(", field("argument", $.expression), ")"),
      seq("scale", "(", field("argument", $.expression), ")"),
      seq("read", "(", ")"),
      seq("random", "(", ")"),
    )),

    parenthesized_expression: $ => seq(
      "(",
      $.expression,
      ")",
    ),

    named_expression: $ => choice(
      $.identifier,
      $.array_element,
      $.special_variable,
    ),

    identifier: $ => token(prec(-1, /[a-z][a-z0-9_]*/)),

    number: $ => token(seq(
      choice(
        seq(/[0-9A-Z]+/, optional(seq(
          /(\\\r?\n[0-9A-Z]+)*/,
          optional(seq(".", optional(/[0-9A-Z]+/))),
        ))),
        seq(".", /[0-9A-Z]+/),
      ),
    )),

    string: $ => seq(
      '"',
      repeat(choice(
        /[^"\\]/,
        /\\./,
        /\n/,
      )),
      '"',
    ),

    block_comment: $ => token(seq(
      "/*",
      repeat(choice(
        /[^*]/,
        /\*[^/]/,
      )),
      "*/",
    )),

    line_comment: $ => token(seq(
      "#",
      /[^\n]*/,
    )),

    line_continuation: $ => token(/\\\r?\n/),

    newline: $ => /\n/,
  },
});
