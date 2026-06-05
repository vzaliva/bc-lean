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
    $.line_continuation,
  ],

  rules: {
    source_file: $ => repeat($._top_level_item),

    _top_level_item: $ => choice(
      $.function_definition,
      $.newline,
      seq($.statement_sequence, $.newline),
    ),

    statement_sequence: $ => prec.left(choice(
      $.statement,
      seq(optional($.statement), repeat1(seq(";", optional($.statement)))),
    )),

    function_definition: $ => seq(
      "define",
      field("name", $.identifier),
      "(",
      optional($.parameter_list),
      ")",
      "{",
      repeat($._body_item),
      optional($.statement_sequence),
      "}",
    ),

    _body_item: $ => choice(
      seq($.statement_sequence, $.newline),
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
    ),

    statement: $ => choice(
      $.expression_statement,
      $.string_statement,
      $.auto_statement,
      $.if_statement,
      $.while_statement,
      $.for_statement,
      $.break_statement,
      $.return_statement,
      $.quit_statement,
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
    )),

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
      field("init", $.expression),
      ";",
      field("condition", $.expression),
      ";",
      field("update", $.expression),
      ")",
      optional($.newline),
      field("body", $.statement),
    ),

    break_statement: $ => "break",
    quit_statement: $ => "quit",

    return_statement: $ => prec.left(seq(
      "return",
      optional(seq("(", field("value", $.expression), ")")),
    )),

    block_statement: $ => seq(
      "{",
      repeat($._body_item),
      optional($.statement_sequence),
      "}",
    ),

    expression: $ => choice(
      $.assignment_expression,
      $.relational_expression,
    ),

    assignment_expression: $ => prec.right(1, seq(
      field("left", $.named_expression),
      field("operator", $.assign_op),
      field("right", $.expression),
    )),

    assign_op: $ => choice(
      "=", "+=", "-=", "*=", "/=", "%=", "^=",
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

    identifier: $ => token(prec(-1, /[a-z]/)),

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
      repeat(/[^"]/),
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

    line_continuation: $ => token(/\\\r?\n/),

    newline: $ => /\n/,
  },
});
