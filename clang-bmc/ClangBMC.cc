#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/STLExtras.h"
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
};

std::string binaryOp(const Stmt *stmt,
                     std::unordered_map<std::string, int> &SSATable) {
    auto *B = cast<BinaryOperator>(stmt);
    auto *RHS = B->getRHS();
    std::string R;
    if (auto *Implicit = dyn_cast<ImplicitCastExpr>(RHS))
        RHS = Implicit->getSubExpr();
    if (auto *BOP = dyn_cast<BinaryOperator>(RHS)) {
        R = binaryOp(BOP, SSATable);
    } else if (auto *IntLit = dyn_cast<IntegerLiteral>(RHS)) {
        R = IntLit->getValue().toString(10, false);
    } else if (auto *DRE = dyn_cast<DeclRefExpr>(RHS)) {
        if (auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
            std::string Var = VD->getQualifiedNameAsString();
            R = Var + std::to_string(SSATable[Var]);
        }
    }

    auto *LHS = B->getLHS();
    std::string L;
    if (auto *Implicit = dyn_cast<ImplicitCastExpr>(LHS))
        LHS = Implicit->getSubExpr();
    if (auto *DRE = dyn_cast<DeclRefExpr>(LHS)) {
        if (auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
            std::string Var = VD->getQualifiedNameAsString();
            L = B->isAssignmentOp()
                    ? Var + std::to_string(++SSATable[Var]) + "=="
                    : Var + std::to_string(SSATable[Var]) +
                          B->getOpcodeStr().str();
        }
    }
    return L + R;
}

void declStmt(const Stmt *stmt, std::vector<std::string> &Clause,
              std::unordered_map<std::string, int> &SSATable) {
    auto *DST = cast<DeclStmt>(stmt);
    auto DS = DST->decls();
    for (const auto D : DS) {
        std::string formula;
        if (auto *VDC = dyn_cast<VarDecl>(D)) {
            std::string Var = VDC->getQualifiedNameAsString();
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
        Clause.push_back(binaryOp(stmt, SSATable));
        break;
    case Stmt::DeclStmtClass:
        declStmt(stmt, Clause, SSATable);
        break;
    case Stmt::UnaryOperatorClass:
        break;
    }
}

void generateZ3Code(std::vector<Formula> &Fs) {
    int fileNum = 0;
    for (auto &F : Fs) {
        std::error_code EC;
        raw_fd_ostream OS("Z3_code" + std::to_string(fileNum) + ".cc", EC);
        OS << "#include <z3++.h>\n"
              "#include <iostream>\n"
              "using namespace z3;\n"
              "int main() {\n"
              "    context c;\n"
              "    solver s(c);\n";

        for (auto &C : F.SSATable) {
            for (int i = 1; i <= C.second; ++i)
                OS << "    expr " << C.first << i << " = c.int_const(\""
                   << C.first << i << "\");\n";
        }

        int num = 1;
        for (auto &Clause : F.Clauses) {
            OS << "    expr conjecture" << num << " = " << Clause << ";\n";
            OS << "    s.add(conjecture" << num << ");\n";
            ++num;
        }

        OS << "    s.check();\n";
        OS << R"(    switch (s.check()) {
                             case unsat:
                                 std::cout << "this path is valid";
                                 break;
                             case sat:
                                 std::cout <<"this path is not valid";
                                 break;
                             case unknown:
                                 std::cout <<"unknown";
                                 break;
                         })";
        OS << "\n}\n";
        ++fileNum;
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

void processBranches(CFGBlock *N, std::vector<std::string> &Clauses,
                     std::unordered_map<std::string, int> &SSATable) {
    if (N->succ_empty())
        return;
    auto *NextBlock = *std::next(&N);
    const auto ID = NextBlock->getBlockID();
    auto T = N->getTerminator();
    auto *St = T.getStmt();
    if (!St)
        return;
    if (isa<IfStmt>(St)) {
        // rewrite the last the stmt in N
        if ((*N->succ_begin())->getBlockID() != ID)
            Clauses.back() = "!(" + Clauses.back() + ")";
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
                auto *CaseSt = cast<CaseStmt>(FirstCase);
                if (auto Val = caseStmtVal(CaseSt))
                    Clauses.push_back('(' + Last + ")!=" + Val.getValue());
            }
        } else {
            auto *CaseSt = dyn_cast<CaseStmt>(LB);
            if (auto Val = caseStmtVal(CaseSt))
                Clauses.push_back('(' + Last + ")==" + Val.getValue());
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
            for (auto &N : P) {
                for (auto &E : *N) {
                    auto *S = E.castAs<CFGStmt>().getStmt();
                    if (!(S->getStmtClass() == Stmt::BinaryOperatorClass) &&
                        !(S->getStmtClass() == Stmt::UnaryOperatorClass) &&
                        !(S->getStmtClass() == Stmt::DeclStmtClass))
                        continue;
                    processStmt(S, Clauses, SSATable);
                }
                processBranches(N, Clauses, SSATable);
                Fs.push_back({Clauses, SSATable});
            }
        }
        generateZ3Code(Fs);
        return true;
    }
};

class FunctionDeclConsumer : public ASTConsumer {
    FunctionDeclVisitor Visitor;

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
        return make_unique<FunctionDeclConsumer>(&Compiler.getASTContext());
    }
};
} // namespace

int main(int argc, const char **argv) {
    CommonOptionsParser OptionsParser(argc, argv, BMCCategory);
    ClangTool Tool(OptionsParser.getCompilations(),
                   OptionsParser.getSourcePathList());
    return Tool.run(newFrontendActionFactory<FunctionDeclAction>().get());
}

