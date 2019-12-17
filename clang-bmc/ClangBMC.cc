#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/STLExtras.h"
#include <fstream>
#include <unordered_map>
#include <vector>
using namespace llvm;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;

static cl::OptionCategory BMCCategory("clang-bmc options");
static cl::opt<int> MaxDepth("depth", cl::desc("<max_depth>"), cl::Optional,
                             cl::init(7), cl::cat(BMCCategory));
namespace {

struct Formula {
  std::vector<std::string> Clauses;
  std::unordered_map<std::string, int> SSATable;
  std::vector<unsigned int> LineNum;
  void print() {
    errs() << "path: size " << Clauses.size() << ' ';
    for (auto &Elem : Clauses)
      errs() << Elem << ' ';
    errs() << "\nSSATable: ";
    for (auto &Elem : SSATable)
      errs() << Elem.first << ' ' << Elem.second << ' ';
    errs() << '\n';
  }
};

void unaryOp(const Stmt *stmt, std::vector<std::string> &Clause,
             std::unordered_map<std::string, int> &SSATable) {
  auto *U = cast<UnaryOperator>(stmt);
  std::string formula;
  auto *E = U->getSubExpr();
  auto *DRE = cast<DeclRefExpr>(E);
  auto *VD = cast<VarDecl>(DRE->getDecl());
  std::string Var = VD->getQualifiedNameAsString();
  auto R = std::to_string(SSATable[Var]);
  formula.append(Var + std::to_string(++SSATable[Var]) + "==" + Var + R);
  if (U->isIncrementOp()) {
    formula.append("+1");
  } else if (U->isDecrementOp()) {
    formula.append("-1");
  }
}

void processRHSSelfIncOrDec(const Stmt *stmt, std::vector<std::string> &Clause,
                            std::unordered_map<std::string, int> &SSATable,
                            bool Pre) {
  auto *B = cast<BinaryOperator>(stmt);
  auto *RHS = B->getRHS();
  std::string formula;
  if (auto *UOP = dyn_cast<UnaryOperator>(RHS)) {
    if (Pre && !UOP->isPrefix())
      return;
    if (!Pre && !UOP->isPostfix())
      return;
    auto *E = UOP->getSubExpr();
    auto *DRE = cast<DeclRefExpr>(E);
    auto *VD = cast<VarDecl>(DRE->getDecl());
    std::string Var = VD->getQualifiedNameAsString();
    auto R = std::to_string(SSATable[Var]);

    formula.append(Var + std::to_string(++SSATable[Var]) + "==" + Var + R);
    if (UOP->isIncrementOp()) {
      formula.append("+1");
    } else if (UOP->isDecrementOp()) {
      formula.append("-1");
    }
    Clause.push_back(formula);
  }
}

std::string binaryOp(const Stmt *stmt,
                     std::unordered_map<std::string, int> &SSATable) {
  auto *B = cast<BinaryOperator>(stmt);
  auto *RHS = B->getRHS();
  std::string R;
  if (auto *Implicit = dyn_cast<ImplicitCastExpr>(RHS))
    RHS = Implicit->getSubExpr();
  if (auto *BOP = dyn_cast<BinaryOperator>(RHS)) {
    R = binaryOp(BOP, SSATable);
  } else if (auto *UOP = dyn_cast<UnaryOperator>(RHS)) {
    auto *E = UOP->getSubExpr();
    auto *DRE = cast<DeclRefExpr>(E);
    auto *VD = cast<VarDecl>(DRE->getDecl());
    std::string Var = VD->getQualifiedNameAsString();
    R = Var + std::to_string(SSATable[Var]);
  } else if (auto *IntLit = dyn_cast<IntegerLiteral>(RHS)) {
    R = IntLit->getValue().toString(10, false);
  } else if (auto *DRE = dyn_cast<DeclRefExpr>(RHS)) {
    if (auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
      std::string Var = VD->getQualifiedNameAsString();
      R = Var + std::to_string(SSATable[Var]);
    }
  }

  auto *LHS = B->getLHS();
  std::string L, Var;
  if (auto *Implicit = dyn_cast<ImplicitCastExpr>(LHS))
    LHS = Implicit->getSubExpr();
  if (auto *BOP = dyn_cast<BinaryOperator>(LHS)) {
    Var = binaryOp(BOP, SSATable);
  } else if (auto *DRE = dyn_cast<DeclRefExpr>(LHS)) {
    if (auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
      Var = VD->getQualifiedNameAsString();
  }
  L = B->isAssignmentOp()
          ? Var + std::to_string(++SSATable[Var]) + "=="
          : Var + std::to_string(SSATable[Var]) + B->getOpcodeStr().str();
  return L + R;
}

void declStmt(const Stmt *stmt, std::vector<std::string> &Clause,
              std::unordered_map<std::string, int> &SSATable) {
  auto *DST = cast<DeclStmt>(stmt);
  auto DS = DST->decls();
  for (const auto D : DS) {
    std::string formula;
    if (auto *VDC = dyn_cast<VarDecl>(D)) {
      auto Var = VDC->getQualifiedNameAsString();
      auto *Init = VDC->getInit();
      if (Init) {
        formula.append(Var + std::to_string(SSATable[Var]));
        if (auto *IntLit = dyn_cast<IntegerLiteral>(Init))
          formula.append(IntLit->getValue().toString(10, false));
      } else {
        SSATable[Var];
      }
    }
    // only var decl
    if (!formula.empty())
      Clause.push_back(formula);
  }
}

// generating ssa form formula here
void processStmt(const Stmt *stmt, std::vector<std::string> &Clause,
                 std::unordered_map<std::string, int> &SSATable) {
  switch (stmt->getStmtClass()) {
  case Stmt::BinaryOperatorClass:
    processRHSSelfIncOrDec(stmt, Clause, SSATable, true);
    Clause.push_back(binaryOp(stmt, SSATable));
    processRHSSelfIncOrDec(stmt, Clause, SSATable, false);
    break;
  case Stmt::DeclStmtClass:
    declStmt(stmt, Clause, SSATable);
    break;
  case Stmt::UnaryOperatorClass:
    unaryOp(stmt, Clause, SSATable);
    break;
  }
}

void generateAndRunZ3Code(std::vector<Formula> &Fs) {
  int FileNum = 0;
  for (auto &F : Fs) {
    F.print();
    std::error_code EC;
    std::string FileName = "Z3_code" + std::to_string(FileNum) + ".cc";
    raw_fd_ostream OS(FileName, EC);
    OS << "#include <z3++.h>\n"
          "#include <iostream>\n"
          "#include <string>\n"
          "using namespace z3;\n"
          "int main() {\n"
          "    context c;\n";

    OS << "    std::string LineNums = \"";
    for (auto &L : F.LineNum)
      OS << L << ' ';
    OS << "\";\n";

    for (auto &C : F.SSATable) {
      for (int i = 0; i <= C.second; ++i)
        OS << "    expr " << C.first << i << " = c.int_const(\"" << C.first << i
           << "\");\n";
    }

    OS << "    solver s(c);\n";

    int num = 1;
    for (auto &Clause : F.Clauses) {
      OS << "    expr conjecture" << num << " = " << Clause << ";\n";
      OS << "    s.add(conjecture" << num << ");\n";
      ++num;
    }

    OS << "    s.check();\n";
    OS << R"(    switch (s.check()) {
                             case unsat:
                                 break;
                             case sat:
                                 std::cout <<"this path is not valid\n";
                                 std::cout <<"line numbers are: "<< LineNums << '\n';
                                 break;
                             case unknown:
                                 std::cout <<"unknown\n";
                                 std::cout <<"line numbers are: "<< LineNums << '\n';
                                 break;
                     })";
    OS << "\n}\n";
    OS.flush();

    std::system(("g++ " + FileName + " -o z3 -lz3").data());
    std::system("./z3");
    std::system("rm z3 ");

    ++FileNum;
  }
}

Optional<std::string> caseStmtVal(CaseStmt *CaseSt) {
  if (!CaseSt->getLHS())
    return None;
  auto *ConstSt = cast<ConstantExpr>(CaseSt->getLHS());
  auto *CaseVal = ConstSt->getSubExpr();
  if (auto *IntLit = dyn_cast<IntegerLiteral>(CaseVal))
    return IntLit->getValue().toString(10, false);
  return None;
}

// tricky pass ptr by ref
void processBranches(CFGBlock *&N, std::vector<std::string> &Clauses,
                     std::unordered_map<std::string, int> &SSATable) {
  if (N->succ_empty())
    return;
  auto *NextBlock = *std::next(&N);
  auto ID = NextBlock->getBlockID();
  auto T = N->getTerminator();
  auto *St = T.getStmt();
  if (!St)
    return;

  if (isa<ForStmt>(St) || isa<IfStmt>(St) || isa<BinaryOperator>(St)) {
    // rewrite the last the stmt in N
    if ((*N->succ_begin())->getBlockID() != ID) {
      Clauses.back() = "!(" + Clauses.back() + ")";
    }
  } else if (auto *SwitchSt = dyn_cast<SwitchStmt>(St)) {
    auto *LB = NextBlock->getLabel();
    if (!LB)
      return;
    const auto Last = Clauses.back();
    Clauses.pop_back();
    if (isa<DefaultStmt>(LB)) {
      // combine all other cases
      for (auto *FirstCase = SwitchSt->getSwitchCaseList(); FirstCase;
           FirstCase = FirstCase->getNextSwitchCase()) {
        if (auto *CaseSt = dyn_cast<CaseStmt>(FirstCase))
          if (auto Val = caseStmtVal(CaseSt))
            Clauses.push_back('(' + Last + ")!=" + Val.getValue());
      }
    } else {
      if (auto *CaseSt = dyn_cast<CaseStmt>(LB)) {
        if (auto Val = caseStmtVal(CaseSt))
          Clauses.push_back('(' + Last + ")==" + Val.getValue());
      }
    }
  }
}

class FunctionDeclVisitor : public RecursiveASTVisitor<FunctionDeclVisitor> {
  using BlockPaths = std::vector<std::vector<CFGBlock *>>;
  using BlockPath = std::vector<CFGBlock *>;

  ASTContext *Ctx;
  BlockPaths Paths;
  unsigned long Depth = MaxDepth;

  void dfsHelper(BlockPaths &PS, BlockPath &P, CFGBlock *Src) {
    if (P.size() > Depth)
      return;
    if (!P.empty()) {
      if (auto *Label = P.back()->getLabel()) {
        if (auto *L = dyn_cast<LabelStmt>(Label)) {
          if (strcmp(L->getName(), "Error") == 0) {
            PS.push_back(P);
            return;
          }
        }
      }
    }
    P.push_back(Src);
    for (auto &E : Src->succs())
      dfsHelper(PS, P, E.getReachableBlock());
    P.pop_back();
  }

public:
  explicit FunctionDeclVisitor(ASTContext *ctx) : Ctx{ctx} {}

  bool VisitFunctionDecl(FunctionDecl *Decl) {
    // only care about functions that are not in the header files
    if (!Ctx->getSourceManager().isWrittenInMainFile(Decl->getBeginLoc()))
      return true;
    if (!Ctx->getFullLoc(Decl->getBeginLoc()).isValid() || !Decl->hasBody())
      return true;

    std::vector<Formula> Fs;
    auto FuncCFG =
        CFG::buildCFG(Decl, Decl->getBody(), Ctx, CFG::BuildOptions());
    // FuncCFG->dump(LangOptions(), false);
    // FuncCFG->viewCFG(LangOptions());

    BlockPath Path;
    dfsHelper(Paths, Path, &FuncCFG->getEntry());

    for (auto &P : Paths) {
      std::vector<std::string> Clauses;
      std::unordered_map<std::string, int> SSATable;
      std::vector<unsigned int> LineNums;
      for (auto &N : P) {
        for (auto &E : *N) {
          auto *S = E.castAs<CFGStmt>().getStmt();
          if (S->getStmtClass() != Stmt::BinaryOperatorClass &&
              S->getStmtClass() != Stmt::UnaryOperatorClass &&
              S->getStmtClass() != Stmt::DeclStmtClass &&
              S->getStmtClass() != Stmt::GotoStmtClass)
            continue;
          auto FullLocation = Ctx->getFullLoc(S->getBeginLoc());
          if (FullLocation.isValid())
            LineNums.push_back(FullLocation.getSpellingLineNumber());
          processStmt(S, Clauses, SSATable);
        }
        if (N == P.back())
          continue;
        processBranches(N, Clauses, SSATable);
      }
      Fs.push_back(Formula{Clauses, SSATable, LineNums});
    }
    generateAndRunZ3Code(Fs);
    return true;
  }
};

class FunctionDeclConsumer : public ASTConsumer {
  FunctionDeclVisitor Visitor;

  //

public:
  explicit FunctionDeclConsumer(ASTContext *Ctx) : Visitor{Ctx} {}

  bool HandleTopLevelDecl(DeclGroupRef DG) override {
    for (auto D : DG)
      Visitor.TraverseDecl(D);

    return true;
  }
};

class FunctionDeclAction : public ASTFrontendAction {
public:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &Compiler,
                                                 StringRef InFile) override {
    return std::unique_ptr<clang::ASTConsumer>(
        new FunctionDeclConsumer{&Compiler.getASTContext()});
  }
};
} // namespace

int main(int argc, const char **argv) {
  CommonOptionsParser OptionsParser(argc, argv, BMCCategory);
  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());
  return Tool.run(newFrontendActionFactory<FunctionDeclAction>().get());
}

