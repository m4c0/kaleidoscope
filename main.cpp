#include <cctype>
#include <iostream>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/IPO.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
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

      num_val = strtod(num_str.c_str(), nullptr);
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
    virtual llvm::Value * codegen() = 0;
  };

  class number_expr : public expr {
    double m_val;

  public:
    explicit number_expr(double val) : m_val(val) {
    }
    virtual llvm::Value * codegen();
  };

  class var_expr : public expr {
    std::string m_name;

  public:
    explicit var_expr(const std::string & name) : m_name(name) {
    }
    virtual llvm::Value * codegen();
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
    virtual llvm::Value * codegen();
  };

  class call_expr : public expr {
    std::string m_callee;
    std::vector<std::unique_ptr<expr>> m_args;

  public:
    call_expr(const std::string & callee, std::vector<std::unique_ptr<expr>> args)
      : m_callee(callee)
      , m_args(std::move(args)) {
    }
    virtual llvm::Value * codegen();
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
    virtual llvm::Function * codegen();
  };

  class function {
    std::unique_ptr<prototype> m_proto;
    std::unique_ptr<expr> m_body;

  public:
    function(std::unique_ptr<prototype> proto, std::unique_ptr<expr> body)
      : m_proto(std::move(proto))
      , m_body(std::move(body)) {
    }
    virtual llvm::Function * codegen();
  };

  static std::unique_ptr<expr> log_error(const char * str) {
    std::cerr << str << "\n";
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
    if (auto fn = parse_definition()) {
      if (auto ir = fn->codegen()) {
        ir->print(llvm::errs());
        std::cerr << "\n";
      }
    } else {
      get_next_token();
    }
  }
  static void handle_extern() {
    if (auto fn = parse_extern()) {
      if (auto ir = fn->codegen()) {
        ir->print(llvm::errs());
        std::cerr << "\n";
      }
    } else {
      get_next_token();
    }
  }
  static void handle_top_level_expr() {
    if (auto e = parse_top_level_expr()) {
      if (auto ir = e->codegen()) {
        ir->print(llvm::errs());
        std::cerr << "\n";
        ir->eraseFromParent();
      }
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
namespace k::cgen {
  static llvm::LLVMContext ctx {};
  static llvm::IRBuilder<> builder { ctx };
  static llvm::Module mod { "k jit", ctx };
  static llvm::legacy::PassManager pm;
  static llvm::legacy::FunctionPassManager fpm { &mod };
  static std::map<std::string, llvm::Value *> scope;

  static llvm::Function * log_error_f(const char * str) {
    std::cerr << str << "\n";
    return nullptr;
  }
  static llvm::Value * log_error_v(const char * str) {
    std::cerr << str << "\n";
    return nullptr;
  }

  static void setup_fpm() {
    llvm::PassManagerBuilder b;
    b.OptLevel = 3;
    b.SizeLevel = 0;
    b.Inliner = llvm::createFunctionInliningPass(3, 0, false);
    b.populateFunctionPassManager(fpm);
    b.populateModulePassManager(pm);

    pm.add(llvm::createVerifierPass());
    fpm.doInitialization();
  }
}

llvm::Value * k::ast::number_expr::codegen() {
  return llvm::ConstantFP::get(k::cgen::ctx, llvm::APFloat(m_val));
}
llvm::Value * k::ast::var_expr::codegen() {
  auto it = k::cgen::scope.find(m_name);
  if (it == k::cgen::scope.end()) {
    return k::cgen::log_error_v("unknown variable name");
  }
  return it->second;
}
llvm::Value * k::ast::binary_expr::codegen() {
  auto * l = m_lhs->codegen();
  auto * r = m_rhs->codegen();
  if (!l || !r) return nullptr;

  switch (m_op) {
  case '+':
    return k::cgen::builder.CreateFAdd(l, r, "addtmp");
  case '-':
    return k::cgen::builder.CreateFSub(l, r, "subtmp");
  case '*':
    return k::cgen::builder.CreateFMul(l, r, "multmp");
  case '<': {
    auto * c = k::cgen::builder.CreateFCmpULT(l, r, "cmptmp");
    return k::cgen::builder.CreateUIToFP(c, llvm::Type::getDoubleTy(k::cgen::ctx), "booltmp");
  }
  default:
    return k::cgen::log_error_v("invalid binary op");
  }
}
llvm::Value * k::ast::call_expr::codegen() {
  auto * callee = k::cgen::mod.getFunction(m_callee);
  if (!callee) return k::cgen::log_error_v("unknown function referenced");
  if (callee->arg_size() != m_args.size()) return k::cgen::log_error_v("incorrect number of arguments passed");

  std::vector<llvm::Value *> args;
  for (unsigned i = 0, e = m_args.size(); i != e; ++i) {
    args.push_back(m_args[i]->codegen());
    if (!args.back()) return nullptr;
  }

  return k::cgen::builder.CreateCall(callee, args, "calltmp");
}

llvm::Function * k::ast::prototype::codegen() {
  auto * dt = llvm::Type::getDoubleTy(k::cgen::ctx);
  std::vector<llvm::Type *> dbls { m_args.size(), dt };
  llvm::FunctionType * ft = llvm::FunctionType::get(dt, dbls, false);
  llvm::Function * f = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, m_name, k::cgen::mod);

  unsigned idx = 0;
  for (auto & arg : f->args()) {
    arg.setName(m_args[idx++]);
  }

  return f;
}
llvm::Function * k::ast::function::codegen() {
  auto * f = k::cgen::mod.getFunction(m_proto->name());
  if (!f) f = m_proto->codegen();
  if (!f) return nullptr;
  if (!f->empty()) return k::cgen::log_error_f("function can't be redefined");

  auto * bb = llvm::BasicBlock::Create(k::cgen::ctx, "entry", f);
  k::cgen::builder.SetInsertPoint(bb);

  k::cgen::scope.clear();
  for (auto & arg : f->args()) {
    k::cgen::scope[arg.getName().str()] = &arg;
  }

  if (llvm::Value * ret = m_body->codegen()) {
    k::cgen::builder.CreateRet(ret);
    llvm::verifyFunction(*f);
    k::cgen::fpm.run(*f);
    k::cgen::pm.run(k::cgen::mod);
    return f;
  }

  f->eraseFromParent();
  return nullptr;
}

int main() {
  k::cgen::setup_fpm();

  k::ast::main_loop();
  k::cgen::mod.print(llvm::errs(), nullptr);
}
