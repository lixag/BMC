#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include <queue>
#include <unordered_map>
#include <vector>
using namespace llvm;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;

static cl::OptionCategory BMCCategory("clang-bmc options");
// static cl::opt<int> MaxDepth("depth", cl::desc("<max_depth>"), cl::Optional,
//                             cl::init(7), cl::cat(BMCCategory));

namespace {
// struct Formula {
//    std::vector<std::string> Clauses;
//    std::unordered_map<std::string, int> SSATable;
//    void print() {
//        errs() << "path: size " << Clauses.size() << ' ';
//        for (auto &Elem : Clauses)
//            errs() << Elem << ' ';
//        errs() << "\nSSATable: ";
//        for (auto &Elem : SSATable)
//            errs() << Elem.first << ' ' << Elem.second << ' ';
//        errs() << '\n';
//    }
//};
//
// void unaryOp(StringRef FuncName, const Stmt *stmt,
//             std::vector<std::string> &Clauses,
//             std::unordered_map<std::string, int> &SSATable) {
//    auto *U = cast<UnaryOperator>(stmt);
//    std::string Clause, Prefix = FuncName.str() + '_';
//    auto *E = U->getSubExpr();
//    auto *DRE = cast<DeclRefExpr>(E);
//    auto *VD = cast<VarDecl>(DRE->getDecl());
//    std::string Var = Prefix + VD->getQualifiedNameAsString();
//    auto R = std::to_string(SSATable[Var]);
//    Clause.append(Var + std::to_string(++SSATable[Var]) + "==" + Var + R);
//    if (U->isIncrementOp()) {
//        Clause.append("+1");
//    } else if (U->isDecrementOp()) {
//        Clause.append("-1");
//    }
//}
//
// void processRHSSelfIncOrDec(StringRef FuncName, const Stmt *stmt,
//                            std::vector<std::string> &Clauses,
//                            std::unordered_map<std::string, int> &SSATable,
//                            bool Pre) {
//    auto *B = cast<BinaryOperator>(stmt);
//    auto *RHS = B->getRHS();
//    std::string Clause, Prefix = FuncName.str() + '_';
//    if (auto *UOP = dyn_cast<UnaryOperator>(RHS)) {
//        if ((Pre && !UOP->isPrefix()) || (!Pre && !UOP->isPostfix()))
//            return;
//
//        auto *E = UOP->getSubExpr();
//        auto *DRE = cast<DeclRefExpr>(E);
//        auto *VD = cast<VarDecl>(DRE->getDecl());
//        std::string Var = Prefix + VD->getQualifiedNameAsString();
//        auto R = std::to_string(SSATable[Var]);
//
//        Clause.append(Var + std::to_string(++SSATable[Var]) + "==" + Var + R);
//        if (UOP->isIncrementOp())
//            Clause.append("+1");
//        else if (UOP->isDecrementOp())
//            Clause.append("-1");
//
//        Clauses.push_back(Clause);
//    }
//}
//
// std::string binaryOp(StringRef FuncName, const Stmt *stmt,
//                     std::unordered_map<std::string, int> &SSATable) {
//    auto *B = cast<BinaryOperator>(stmt);
//    auto *RHS = B->getRHS();
//    std::string R, Prefix = FuncName.str() + '_';
//    if (auto *Implicit = dyn_cast<ImplicitCastExpr>(RHS))
//        RHS = Implicit->getSubExpr();
//    if (auto *BOP = dyn_cast<BinaryOperator>(RHS)) {
//        R = binaryOp(FuncName, BOP, SSATable);
//    } else if (auto *UOP = dyn_cast<UnaryOperator>(RHS)) {
//        auto *E = UOP->getSubExpr();
//        auto *DRE = cast<DeclRefExpr>(E);
//        auto *VD = cast<VarDecl>(DRE->getDecl());
//        std::string Var = Prefix + VD->getQualifiedNameAsString();
//        R = Var + std::to_string(SSATable[Var]);
//    } else if (auto *IntLit = dyn_cast<IntegerLiteral>(RHS)) {
//        R = IntLit->getValue().toString(10, false);
//    } else if (auto *DRE = dyn_cast<DeclRefExpr>(RHS)) {
//        if (auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
//            std::string Var = Prefix + VD->getQualifiedNameAsString();
//            R = Var + std::to_string(SSATable[Var]);
//        }
//    }
//
//    auto *LHS = B->getLHS();
//    std::string L, Var;
//    if (auto *Implicit = dyn_cast<ImplicitCastExpr>(LHS))
//        LHS = Implicit->getSubExpr();
//    if (auto *BOP = dyn_cast<BinaryOperator>(LHS)) {
//        Var = binaryOp(FuncName, BOP, SSATable);
//    } else if (auto *DRE = dyn_cast<DeclRefExpr>(LHS)) {
//        if (auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
//            Var = Prefix + VD->getQualifiedNameAsString();
//    }
//    L = B->isAssignmentOp()
//        ? Var + std::to_string(++SSATable[Var]) + "=="
//        : Var + std::to_string(SSATable[Var]) + B->getOpcodeStr().str();
//    return L + R;
//}
//
// void declStmt(StringRef FuncName, const Stmt *stmt,
//              std::vector<std::string> &Clauses,
//              std::unordered_map<std::string, int> &SSATable) {
//    auto *DST = cast<DeclStmt>(stmt);
//    auto DS = DST->decls();
//    std::string Prefix = FuncName.str() + '_';
//    for (const auto D : DS) {
//        std::string Clause;
//        if (auto *VDC = dyn_cast<VarDecl>(D)) {
//            auto Var = Prefix + VDC->getQualifiedNameAsString();
//            auto *Init = VDC->getInit();
//            if (Init) {
//                Clause.append(Var + std::to_string(SSATable[Var]));
//                if (auto *IntLit = dyn_cast<IntegerLiteral>(Init))
//                    Clause.append(IntLit->getValue().toString(10, false));
//            } else {
//                SSATable[Var];
//            }
//        }
//        // only var decl
//        if (!Clause.empty())
//            Clauses.push_back(Clause);
//    }
//}
//
//// generating ssa form formula here
// void processStmt(StringRef FuncName, const Stmt *stmt,
//                 std::vector<std::string> &Clause,
//                 std::unordered_map<std::string, int> &SSATable) {
//    switch (stmt->getStmtClass()) {
//    case Stmt::BinaryOperatorClass:
//        processRHSSelfIncOrDec(FuncName, stmt, Clause, SSATable, true);
//        Clause.push_back(binaryOp(FuncName, stmt, SSATable));
//        processRHSSelfIncOrDec(FuncName, stmt, Clause, SSATable, false);
//        break;
//    case Stmt::DeclStmtClass:
//        declStmt(FuncName, stmt, Clause, SSATable);
//        break;
//    case Stmt::UnaryOperatorClass:
//        unaryOp(FuncName, stmt, Clause, SSATable);
//        break;
//    }
//}
//
// void generateAndRunZ3Code(std::vector<Formula> &Fs) {
//    int FileNum = 0;
//    for (auto &F : Fs) {
//        std::error_code EC;
//        std::string FileName = "Z3_code" + std::to_string(FileNum);
//        raw_fd_ostream OS(FileName + ".cc", EC);
//        OS << "#include <z3++.h>\n"
//              "#include <iostream>\n"
//              "using namespace z3;\n"
//              "int main() {\n"
//              "    context c;\n"
//              "    solver s(c);\n";
//
//        for (auto &C : F.SSATable) {
//            for (int i = 1; i <= C.second; ++i)
//                OS << "    expr " << C.first << i << " = c.int_const(\""
//                   << C.first << i << "\");\n";
//        }
//
//        int num = 1;
//        for (auto &Clause : F.Clauses) {
//            OS << "    expr conjecture" << num << " = " << Clause << ";\n";
//            OS << "    s.add(conjecture" << num << ");\n";
//            ++num;
//        }
//
//        OS << "    s.check();\n";
//        OS << R"(    switch (s.check()) {
//                             case unsat:
//                                 std::cout << "this path is valid";
//                                 break;
//                             case sat:
//                                 std::cout <<"this path is not valid";
//                                 break;
//                             case unknown:
//                                 std::cout <<"unknown";
//                                 break;
//                     })";
//        OS << "\n}\n";
//        ++FileNum;
//    }
//}
//
// Optional<std::string> caseStmtVal(CaseStmt *CaseSt) {
//    if (!CaseSt->getLHS())
//        return None;
//    auto *ConstSt = cast<ConstantExpr>(CaseSt->getLHS());
//    auto *CaseVal = ConstSt->getSubExpr();
//    if (auto *IntLit = dyn_cast<IntegerLiteral>(CaseVal))
//        return IntLit->getValue().toString(10, false);
//    return None;
//}
//
//// tricky pass ptr by ref
// void processBranches(CFGBlock *&N, std::vector<std::string> &Clauses,
//                     std::unordered_map<std::string, int> &SSATable) {
//    if (N->succ_empty())
//        return;
//    auto *NextBlock = *std::next(&N);
//    auto ID = NextBlock->getBlockID();
//    auto T = N->getTerminator();
//    auto *St = T.getStmt();
//    if (!St)
//        return;
//    if (isa<IfStmt>(St) && (*N->succ_begin())->getBlockID() != ID) {
//        // rewrite the last the stmt in N
//        Clauses.back() = "!(" + Clauses.back() + ")";
//    } else if (auto *SwitchSt = dyn_cast<SwitchStmt>(St)) {
//        auto *LB = NextBlock->getLabel();
//        if (!LB)
//            return;
//        const auto Last = Clauses.back();
//        Clauses.pop_back();
//        if (isa<DefaultStmt>(LB)) {
//            // combine all other cases
//            for (auto *FirstCase = SwitchSt->getSwitchCaseList(); FirstCase;
//                 FirstCase = FirstCase->getNextSwitchCase()) {
//                if (auto *CaseSt = dyn_cast<CaseStmt>(FirstCase))
//                    if (auto Val = caseStmtVal(CaseSt))
//                        Clauses.push_back('(' + Last + ")!=" +
//                        Val.getValue());
//            }
//        } else if (auto *CaseSt = dyn_cast<CaseStmt>(LB)) {
//            if (auto Val = caseStmtVal(CaseSt))
//                Clauses.push_back('(' + Last + ")==" + Val.getValue());
//        }
//    }
//}
//
// using BlockPaths = std::vector<std::vector<std::pair<StringRef, CFGBlock
// *>>>; using BlockPath = std::vector<std::pair<StringRef, CFGBlock *>>;
//
//// inlining func and identify paths that terminate with an Error label with
//// Depth steps
//
// void processInlineFunc(BlockPaths &Paths, std::vector<std::string> &Clauses,
//                       std::unordered_map<std::string, int> &SSATable) {
//    for (auto &P : Paths) {
//        for (auto &B : P) {
//            for (auto &E : *B.second) {
//                auto *S = E.castAs<CFGStmt>().getStmt();
//                processStmt(B.first, S, Clauses, SSATable);
//            }
//        }
//    }
//}
//

struct BlockNode {
  std::vector<CFGElement> Vec;
  std::vector<BlockNode*> Succ;
  std::string FuncName;
  void clear() {
    Vec.clear();
    Succ.clear();
    FuncName = "";
  }
};

std::vector<BlockNode> getMyCFG(CFG *G, StringRef FuncName, ASTContext *Ctx) {
  std::vector<BlockNode> Res;
  for (auto &B : *G) {
    BlockNode Node;
    auto Begin = B->begin(), End = B->end();
    for (; Begin != End; ++Begin) {
      auto E = *Begin;
      auto *S = E.castAs<CFGStmt>().getStmt();
      if (auto *Call = dyn_cast<CallExpr>(S)) {
        auto *Callee = Call->getDirectCallee();
        auto Tmp = getMyCFG(
            CFG::buildCFG(Callee, Callee->getBody(), Ctx, CFG::BuildOptions())
                .get(),
            Callee->getNameInfo().getAsString(), Ctx);
        Node.Succ = {Res.size()};
        Res.push_back(Node);
        Res.insert(Res.end(), Tmp.begin(), Tmp.end());
        Node.clear();
        Tmp.back().Succ = {Res.size()};
      } else {
        Node.Vec.push_back(E);
      }
      if (Begin + 1 == End) {
        for (auto &N : B->succs()) {
          auto R = N.getReachableBlock();
          Node.Succ.push_back(Res.size() + R->getBlockID());
        }
        Res.push_back(Node);
      }
    }
  }
  return Res;
}

//  Calculate CallGraph: (Input B*, CallGraph)
//  while(Q!=EMPTY)
//      B = Q.front();
//      for I in B:
//          if I is callExpr
//              path.push(callee)
//              CFG= buildCGH()
//              recurse(CFG->entry(), CallGraph)
//              path.pop()
//      Q = push succ
//  CallGraph.push(path)

// for all function decl
// find if it contains any paths that pass through an error label
// else find all path whose length is less than k
// split B at the callExpr

// for func decl who has one or more paths to error label
//      consult the call graph table to find a call chain starting with the
//      main func this is just a traverse of the call graph table combine

// suppose we have one call chain already, and paths for all the func
// combine(chain = vec[FuncName], pathsTable, Res)
// paths = pathTable[chain[0]]
// for path in paths:
//      for B in path:
//        if length > k: return;
//          if B.nextFunc == chain[1]
//              combine(chain[1:], pathTable, currPath + [path.begin(),B],
//              Res)
//
// if chain[0] == final decl
//      Res.push(currPath)

// using ElemPaths = std::vector<std::vector<std::pair<StringRef,
// BlockNode>>>; using ElemPath = std::vector<std::pair<StringRef,
// BlockNode>>;
//
// void dfsHelper(StringRef FuncName, BlockPaths &PS, BlockPath &P, CFGBlock
// *Src,
//               const unsigned long Depth, unsigned long Step) {
//    if (Step > Depth)
//        return;
//    if (!P.empty()) {
//        if (auto *Label = P.back().second->getLabel()) {
//            if (auto *L = dyn_cast<LabelStmt>(Label)) {
//                if (strcmp(L->getName(), "Error") == 0) {
//                    PS.push_back(P);
//                    return;
//                }
//            }
//        }
//
//        P.push_back({FuncName, Src});
//        for (auto &E : Src->succs())
//            dfsHelper(FuncName, PS, P, E.getReachableBlock(), Depth,
//                      Step + Src->size());
//        P.pop_back();
//    }
//}

// void funcDecl(ASTContext *Ctx, FunctionDecl *Decl) {
//    if (!Ctx->getSourceManager().isWrittenInMainFile(Decl->getBeginLoc())
//    ||
//        !Ctx->getFullLoc(Decl->getBeginLoc()).isValid() ||
//        !Decl->hasBody() || Decl->getNameInfo().getAsString() != "main")
//        return;
//    std::vector<Formula> Fs;
//    auto FuncCFG =
//        CFG::buildCFG(Decl, Decl->getBody(), Ctx, CFG::BuildOptions());
//    FuncCFG->dump(LangOptions(), false);
//    FuncCFG->viewCFG(LangOptions());
//
//    BlockPaths Paths;
//    unsigned long Depth = MaxDepth;
//    BlockPath Path;
//    dfsHelper("main", Paths, Path, &FuncCFG->getEntry(), Depth, 0);
//
//    for (auto &P : Paths) {
//        std::vector<std::string> Clauses;
//        std::unordered_map<std::string, int> SSATable;
//        std::vector<std::vector<CFGElement>> Stack;
//        for (auto &N : P) {
//            for (auto Begin = N.second->begin(), End = N.second->end();
//                 Begin != End; ++Begin) {
//                auto E = &*Begin;
//                if (auto *Call = dyn_cast<CallExpr>(E)) {
//                    std::vector<CFGElement> Curr(Begin, End);
//                    Stack.push_back(Curr);
//                    break;
//                }
//                auto *S = E->castAs<CFGStmt>().getStmt();
//                processStmt(N.first, S, Clauses, SSATable);
//            }
//
//            if (N == P.back())
//                continue;
//            processBranches(N.second, Clauses, SSATable);
//        }
//        // process stack
//        Fs.push_back(Formula{Clauses, SSATable});
//    }
//    generateAndRunZ3Code(Fs);
//}

// using CallGraph = std::vector<SmallSetVector<StringRef, 8>>;
//
// void callGraph(CFGBlock *B, CallGraph &G, ASTContext *Ctx,
//               SmallSetVector<StringRef, 8> &Path,
//               SmallSetVector<CFGBlock *, 8> &Visited) {
//
//    std::vector<CFGBlock *> Q;
//    Q.emplace_back(B);
//    while(!Q1.empty()) {
//        // traverse one func at a time
//        while (!Q.empty()) {
//            auto Block = Q.back();
//            Q.pop_back();
//            for (auto &I : *Block) {
//                auto *S = I.castAs<CFGStmt>().getStmt();
//                if (auto *Call = dyn_cast<CallExpr>(S)) {
//                    auto *Callee = Call->getDirectCallee();
//                    auto FuncName = Callee->getNameInfo().getAsString();
//                    if (Path.count(FuncName))
//                        continue;
//                    Path.insert(FuncName);
//                    for (auto &E : Path)
//                        errs() << E << '\n';
//                    Table[CurrfuncName].push_back(funName);
//                    Path.pop_back();
//                }
//            }
//
//            for (auto &E : Block->succs())
//                Q.emplace_back(E.getReachableBlock());
//        }
//
//    }
//}

class FunctionDeclVisitor : public RecursiveASTVisitor<FunctionDeclVisitor> {

  // std::vector<std::unique_ptr<CFG>> CFGS;

  // 1: check with k steps if there is error label
  // find all paths that have length of k
  // then iterating over all paths to find paths that encounters a error
  // label

  // 1->2->3->10->11->12
  //           ->4->5->8->9
  //                   ->6->7->13->14
  //                         ->15->16
  // paths

  // 2:
  // find error for individual func

  // m * n * k

  // actually kind of hard, may use mutually recursive.
  //  void pathFinder(ElemPaths Paths, StringRef FuncName, ElemPath &P,
  //                  CFGBlock *Src, const unsigned long Depth,
  //                  unsigned long Step) {
  //    auto Begin = Src->begin(), End = Src->end();
  //    auto Last = Begin;
  //    for (; Begin != End; ++Begin) {
  //      auto E = *Begin;
  //      if (auto *Call = dyn_cast<CallExpr>(&E)) {
  //        auto *Callee = Call->getDirectCallee();
  //        auto Ptr =
  //            CFG::buildCFG(Callee, Callee->getBody(), Ctx,
  //            CFG::BuildOptions());
  //        std::vector<CFGElement> Vec(Last, Begin);
  //        P.push_back({FuncName, {Vec}});
  //        auto Paths =
  //            pathFinder(Callee->getNameInfo().getAsString(), P,
  //            &Ptr->getEntry(),
  //                       Depth - P.size(), Step + (Last - Begin));
  //
  //        Last = Begin + 1;
  //      }
  //    }
  //    if (Last != End) {
  //      std::vector<CFGElement> Vec{Last, End};
  //      P.push_back({FuncName, {Vec}});
  //    }
  //
  //    for (auto &E : Src->succs())
  //      pathFinder(Paths, FuncName, P, E.getReachableBlock(), Depth,
  //                 Step + Src->size());
  //  }

  ASTContext *Ctx;

public:
  explicit FunctionDeclVisitor(ASTContext *ctx) : Ctx{ctx} {}

  bool VisitFunctionDecl(FunctionDecl *Decl) {
    if (!Ctx->getSourceManager().isWrittenInMainFile(Decl->getBeginLoc()) ||
        !Ctx->getFullLoc(Decl->getBeginLoc()).isValid() || !Decl->hasBody() ||
        Decl->getNameInfo().getAsString() != "main")
      return true;

    auto FuncCFG =
        CFG::buildCFG(Decl, Decl->getBody(), Ctx, CFG::BuildOptions());
    for (auto &B : *FuncCFG) {
      errs() << B->getBlockID() << ' ';
    }
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

