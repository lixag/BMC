#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include <unordered_map>
#include <vector>

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace llvm;

static cl::OptionCategory BMCCategory("BMC options");

namespace {
class FunctionDeclVisitor : public RecursiveASTVisitor<FunctionDeclVisitor> {
  private:
    struct Formula {
        std::vector<std::string> Clauses;
        std::unordered_map<std::string, int> SSATable;
    };

    using BlockPaths = std::vector<std::vector<CFGBlock *>>;
    using BlockPath = std::vector<CFGBlock *>;

    ASTContext *Ctx;
    BlockPaths Paths;
    unsigned long Depth = 7;

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

    static std::string
    binaryOp(const Stmt *stmt, std::unordered_map<std::string, int> &SSATable) {
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
    // generating ssa form formula here
    void processStmt(std::vector<std::string> &Clause, const Stmt *stmt,
                     std::unordered_map<std::string, int> &SSATable) {
        switch (stmt->getStmtClass()) {
        case Stmt::BinaryOperatorClass: {
            Clause.push_back(binaryOp(stmt, SSATable));
            break;
        }
        case Stmt::DeclStmtClass: {
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
                            formula.append(
                                IntLit->getValue().toString(10, false));
                    } else {
                        SSATable[Var];
                    }
                }
                // only var decl
                if (!formula.empty())
                    Clause.push_back(formula);
            }
            break;
        }
        case Stmt::UnaryOperatorClass: {
            auto Loc = Ctx->getFullLoc(stmt->getBeginLoc());
            errs() << "Unary op: " << Loc.getSpellingLineNumber() << '\n';
        }
        }
    }

    static void generateZ3Code(std::vector<Formula> &Fs) {
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

    static Optional<std::string> caseStmtVal(CaseStmt *CaseSt) {
        if (!CaseSt->getLHS())
            return None;
        auto *ConstSt = cast<ConstantExpr>(CaseSt->getLHS());
        auto *CaseVal = ConstSt->getSubExpr();
        if (auto *IntLit = dyn_cast<IntegerLiteral>(CaseVal))
            return IntLit->getValue().toString(10, false);
        return None;
    }

    static void processBranch(CFGBlock *N, std::vector<std::string> &Clauses,
                              std::unordered_map<std::string, int> &SSATable) {
        if (N->succ_empty())
            return;
        auto *NextBlock = *std::next(&N);
        auto ID = NextBlock->getBlockID();
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

    bool VisitFunctionDecl(FunctionDecl *Decl) {
        if (!Ctx->getSourceManager().isWrittenInMainFile(Decl->getBeginLoc()))
            return true;
        FullSourceLoc full_location = Ctx->getFullLoc(Decl->getBeginLoc());
        std::vector<Formula> Fs;
        if (full_location.isValid()) {
            if (Decl->hasBody()) {
                auto *FuncBody = Decl->getBody();
                auto FuncCFG =
                    CFG::buildCFG(Decl, FuncBody, Ctx, CFG::BuildOptions());
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
                            if (!(S->getStmtClass() ==
                                  Stmt::BinaryOperatorClass) &&
                                !(S->getStmtClass() ==
                                  Stmt::UnaryOperatorClass) &&
                                !(S->getStmtClass() == Stmt::DeclStmtClass))
                                continue;
                            processStmt(Clauses, S, SSATable);
                        }
                        processBranch(N, Clauses, SSATable);
                        Fs.push_back({Clauses, SSATable});
                    }
                }
            }
            generateZ3Code(Fs);
        }
        return true;
    }
}; // namespace

class FunctionDeclConsumer : public clang::ASTConsumer {
    FunctionDeclVisitor Visitor;

  public:
    explicit FunctionDeclConsumer(ASTContext *Ctx) : Visitor{Ctx} {}

    bool HandleTopLevelDecl(DeclGroupRef DG) override {
        for (auto D : DG)
            Visitor.TraverseDecl(D);
        return true;
    }
};

class FunctionDeclAction : public clang::ASTFrontendAction {
  public:
    std::unique_ptr<clang::ASTConsumer>
    CreateASTConsumer(clang::CompilerInstance &Compiler,
                      llvm::StringRef InFile) override {
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

