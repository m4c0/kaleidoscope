#include <cctype>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace k {
  enum token {
    tok_eof = -1,

    tok_def = -2,
    tok_extern = -3,

    tok_identifier = -4,
    tok_number = -5,
  };

  static std::string identifier_str;
  static double num_val;

  static int last_char = ' ';

  static int get_tok() {
    while (std::isspace(last_char)) {
      last_char = getchar();
    }

    if (std::isalpha(last_char)) {
      identifier_str = last_char;
      while (std::isalnum((last_char = getchar()))) {
        identifier_str += last_char;
      }

      if (identifier_str == "def") return tok_def;
      if (identifier_str == "extern") return tok_extern;
      return tok_identifier;
    }

    if (std::isdigit(last_char) || last_char == '.') {
      std::string num_str;
      do {
        num_str += last_char;
        last_char = getchar();
      } while (std::isdigit(last_char) || last_char == '.');
      return tok_number;
    }

    if (last_char == '#') {
      do {
        last_char = getchar();
      } while (last_char != EOF && last_char != '\n' && last_char != '\r');

      if (last_char != EOF) return get_tok();
    }

    if (last_char == EOF) {
      return tok_eof;
    }

    int this_char = last_char;
    last_char = getchar();
    return this_char;
  }

  static int cur_tok;
  static int get_next_token() {
    cur_tok = get_tok();
    return cur_tok;
  }
}
namespace k::ast {
  class expr {
  public:
    virtual ~expr() = default;
  };

  class number_expr : public expr {
    double m_val;

  public:
    explicit number_expr(double val) : m_val(val) {
    }
  };

  class var_expr : public expr {
    std::string m_name;

  public:
    explicit var_expr(const std::string & name) : m_name(name) {
    }
  };

  class binary_expr : public expr {
    char m_op;
    std::unique_ptr<expr> m_lhs, m_rhs;

  public:
    binary_expr(char op, std::unique_ptr<expr> lhs, std::unique_ptr<expr> rhs)
      : m_op(op)
      , m_lhs(std::move(lhs))
      , m_rhs(std::move(rhs)) {
    }
  };

  class call_expr : public expr {
    std::string m_callee;
    std::vector<std::unique_ptr<expr>> m_args;

  public:
    call_expr(const std::string & callee, std::vector<std::unique_ptr<expr>> args)
      : m_callee(callee)
      , m_args(std::move(args)) {
    }
  };

  class prototype {
    std::string m_name;
    std::vector<std::string> m_args;

  public:
    prototype(const std::string & name, std::vector<std::string> args) : m_name(name), m_args(args) {
    }

    [[nodiscard]] constexpr const auto & name() const {
      return m_name;
    }
  };

  class function {
    std::unique_ptr<prototype> m_proto;
    std::unique_ptr<expr> m_body;

  public:
    function(std::unique_ptr<prototype> proto, std::unique_ptr<expr> body)
      : m_proto(std::move(proto))
      , m_body(std::move(body)) {
    }
  };

  static std::unique_ptr<expr> log_error(const char * str) {
    return nullptr;
  }
  static std::unique_ptr<prototype> log_error_p(const char * str) {
    log_error(str);
    return nullptr;
  }

  static std::unique_ptr<expr> parse_number_expr() {
    auto res = std::make_unique<number_expr>(num_val);
    get_next_token();
    return res;
  }

  static std::unique_ptr<expr> parse_expr();
  static std::unique_ptr<expr> parse_parent_expr() {
    get_next_token(); // (
    auto v = parse_expr();
    if (!v) return nullptr;

    if (cur_tok != ')') return log_error("expected ')'");
    get_next_token(); //)
    return v;
  }

  static std::unique_ptr<expr> parse_identifier_expr() {
    auto id_name = identifier_str;
    get_next_token(); // id

    if (cur_tok != '(') return std::make_unique<var_expr>(id_name);
    get_next_token(); // (

    std::vector<std::unique_ptr<expr>> args;
    if (cur_tok != ')') {
      while (true) {
        if (auto arg = parse_expr()) {
          args.push_back(std::move(arg));
        } else {
          return nullptr;
        }
        if (cur_tok == ')') break;
        if (cur_tok != ',') return log_error("expected ')' or ',' in argument list");

        get_next_token();
      }
    }

    get_next_token(); // ')'

    return std::make_unique<call_expr>(id_name, std::move(args));
  }

  static std::unique_ptr<expr> parse_primary() {
    switch (cur_tok) {
    case tok_identifier:
      return parse_identifier_expr();
    case tok_number:
      return parse_number_expr();
    case '(':
      return parse_parent_expr();
    default:
      return log_error("unknown token when expecting an expression");
    }
  }

  static std::map<char, int> binop_precedence {
    { '<', 10 },
    { '+', 20 },
    { '-', 20 },
    { '*', 40 },
  };
  static int get_tok_precedence() {
    if (!isascii(cur_tok)) return -1;

    auto v = binop_precedence.find(cur_tok);
    if (v == binop_precedence.end()) return -1;

    return v->second;
  }

  static std::unique_ptr<expr> parse_binop_rhs(int expr_prec, std::unique_ptr<expr> lhs) {
    while (true) {
      int tok_prec = get_tok_precedence();
      if (tok_prec < expr_prec) return lhs;

      int binop = cur_tok;
      get_next_token(); // binop

      auto rhs = parse_primary();
      if (!rhs) return nullptr;

      int next_prec = get_tok_precedence();
      if (tok_prec < next_prec) {
        rhs = parse_binop_rhs(tok_prec + 1, std::move(rhs));
        if (!rhs) return nullptr;
      }

      lhs = std::make_unique<binary_expr>(binop, std::move(lhs), std::move(rhs));
    }
  }
  static std::unique_ptr<expr> parse_expr() {
    auto lhs = parse_primary();
    if (!lhs) return nullptr;

    return parse_binop_rhs(0, std::move(lhs));
  }

  static std::unique_ptr<prototype> parse_prototype() {
    if (cur_tok != tok_identifier) return log_error_p("expected function name in prototype");

    std::string fn_name = identifier_str;
    get_next_token();

    if (cur_tok != '(') return log_error_p("expected '(' in prototype");

    std::vector<std::string> arg_names;
    while (get_next_token() == tok_identifier) {
      arg_names.push_back(identifier_str);
    }
    if (cur_tok != ')') return log_error_p("expected ')' in prototype");

    get_next_token(); // )

    return std::make_unique<prototype>(fn_name, std::move(arg_names));
  }

  static std::unique_ptr<function> parse_definition() {
    get_next_token(); // def

    auto proto = parse_prototype();
    if (!proto) return nullptr;

    if (auto e = parse_expr()) return std::make_unique<function>(std::move(proto), std::move(e));

    return nullptr;
  }

  static std::unique_ptr<prototype> parse_extern() {
    get_next_token(); // extern
    return parse_prototype();
  }

  static std::unique_ptr<function> parse_top_level_expr() {
    if (auto e = parse_expr()) {
      auto proto = std::make_unique<prototype>("", std::vector<std::string>());
      return std::make_unique<function>(std::move(proto), std::move(e));
    }
    return nullptr;
  }

  static void handle_definition() {
    if (parse_definition()) {
      std::cerr << "def\n";
    } else {
      get_next_token();
    }
  }
  static void handle_extern() {
    if (parse_extern()) {
      std::cerr << "extern\n";
    } else {
      get_next_token();
    }
  }
  static void handle_top_level_expr() {
    if (parse_top_level_expr()) {
      std::cerr << "top level\n";
    } else {
      get_next_token();
    }
  }
  static void main_loop() {
    std::cerr << "ready> ";
    get_next_token();

    while (1) {
      switch (cur_tok) {
      case tok_eof:
        return;
      case ';': // ignore top-level semicolons
        std::cerr << "ready> ";
        get_next_token();
        break;
      case tok_def:
        handle_definition();
        break;
      case tok_extern:
        handle_extern();
        break;
      default:
        handle_top_level_expr();
        break;
      }
    }
  }
}

int main() {
  k::ast::main_loop();
}
