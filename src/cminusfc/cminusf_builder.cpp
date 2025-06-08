#include "cminusf_builder.hpp"
#include "Type.hpp"
#include "Value.hpp"

#define CONST_FP(num) ConstantFP::get((float)num, module.get())
#define CONST_INT(num) ConstantInt::get(num, module.get())

// types
Type *VOID_T;
Type *INT1_T;
Type *INT32_T;
Type *INT32PTR_T;
Type *FLOAT_T;
Type *FLOATPTR_T;

/*
 * use CMinusfBuilder::Scope to construct scopes
 * scope.enter: enter a new scope
 * scope.exit: exit current scope
 * scope.push: add a new binding to current scope
 * scope.find: find and return the value bound to the name
 */

Value *CminusfBuilder::visit(ASTProgram &node) {
    VOID_T = module->get_void_type();
    INT1_T = module->get_int1_type();
    INT32_T = module->get_int32_type();
    INT32PTR_T = module->get_int32_ptr_type();
    FLOAT_T = module->get_float_type();
    FLOATPTR_T = module->get_float_ptr_type();

    Value *ret_val = nullptr;
    // 对AST进行遍历
    for (auto &decl : node.declarations) {
        ret_val = decl->accept(*this);
    }
    return ret_val;
}

Value *CminusfBuilder::visit(ASTNum &node) {
    if (node.type == TYPE_INT) {
        context.ValBridge = CONST_INT(node.i_val);
    } else if (node.type == TYPE_FLOAT) {
        context.ValBridge = CONST_FP(node.f_val);
    } else {
        std::cerr << "Unsupported type in ASTNum" << std::endl;
    }
    return nullptr;
}

// 变量声明 比如：int a / float b[10]
Value *CminusfBuilder::visit(ASTVarDeclaration &node) {
    auto varTy = (node.type == TYPE_INT) ? INT32_T : FLOAT_T;
    // 如果是数组
    if (node.num != nullptr)
        varTy = ArrayType::get(varTy, node.num->i_val);
    // 如果是全局变量
    if (scope.in_global()) {
        auto initializer = ConstantZero::get(varTy, module.get());
        auto gvar = GlobalVariable::create(node.id, module.get(), varTy, false,
                                           initializer);
        scope.push(node.id, gvar);
    } else {
        auto var = builder->create_alloca(varTy);
        scope.push(node.id, var);
    }
    return nullptr;
}

Value *CminusfBuilder::visit(ASTFunDeclaration &node) {
    FunctionType *fun_type;
    Type *ret_type;
    std::vector<Type *> param_types;
    if (node.type == TYPE_INT)
        ret_type = INT32_T;
    else if (node.type == TYPE_FLOAT)
        ret_type = FLOAT_T;
    else
        ret_type = VOID_T;
    auto paramTy = INT32_T;
    for (auto &param : node.params) {
        if (param->isarray) {
            paramTy = (param->type == TYPE_INT) ? INT32PTR_T : FLOATPTR_T;
        } else {
            paramTy = (param->type == TYPE_INT) ? INT32_T : FLOAT_T;
        }
        param_types.push_back(paramTy);
    }

    fun_type = FunctionType::get(ret_type, param_types);
    auto func = Function::create(fun_type, node.id, module.get());
    scope.push(node.id, func);
    context.func = func;
    auto funBB = BasicBlock::create(module.get(), "entry", func);
    builder->set_insert_point(funBB);
    scope.enter();
    std::vector<Value *> args;
    for (auto &arg : func->get_args()) {
        args.push_back(&arg);
    }
    context.args = args;
    for (unsigned int i = 0; i < node.params.size(); ++i) {
        context.cirStep = i;
        node.params[i]->accept(*this);
    }
    node.compound_stmt->accept(*this);
    if (not builder->get_insert_block()->is_terminated()) {
        if (context.func->get_return_type()->is_void_type())
            builder->create_void_ret();
        else if (context.func->get_return_type()->is_float_type())
            builder->create_ret(CONST_FP(0.0));
        else
            builder->create_ret(CONST_INT(0));
    }
    scope.exit();
    return nullptr;
}

Value *CminusfBuilder::visit(ASTParam &node) {
    Type *paramTy;
    if (node.isarray) {
        paramTy = (node.type == TYPE_INT) ? INT32PTR_T : FLOATPTR_T;
    } else {
        paramTy = (node.type == TYPE_INT) ? INT32_T : FLOAT_T;
    }
    auto alloc = static_cast<Value *>(builder->create_alloca(paramTy));
    builder->create_store(context.args[context.cirStep], alloc);
    scope.push(node.id, alloc);
    return nullptr;
}

Value *CminusfBuilder::visit(ASTCompoundStmt &node) {

    scope.enter();
    for (auto &decl : node.local_declarations) {
        decl->accept(*this);
    }

    for (auto &stmt : node.statement_list) {
        stmt->accept(*this);
        if (builder->get_insert_block()->is_terminated())
            break;
    }
    scope.exit();
    return nullptr;
}

Value *CminusfBuilder::visit(ASTExpressionStmt &node) {
    if (node.expression != nullptr)
        node.expression->accept(*this);
    return nullptr;
}

Value *CminusfBuilder::visit(ASTSelectionStmt &node) {
    node.expression->accept(*this);
    auto expression = context.ValBridge;

    auto IFstmtBB = BasicBlock::create(module.get(), "", context.func);
    BasicBlock *ELSEstmtBB;
    auto endBB = BasicBlock::create(module.get(), "", context.func);

    auto intORfp = expression->get_type()->is_integer_type();
    auto cond_val =
        (intORfp) ? static_cast<Value *>(
                        builder->create_icmp_ne(expression, CONST_INT(0)))
                  : static_cast<Value *>(
                        builder->create_fcmp_ne(expression, CONST_FP(0.0)));

    if (!node.else_statement) {
        builder->create_cond_br(cond_val, IFstmtBB, endBB);
    } else {
        ELSEstmtBB = BasicBlock::create(module.get(), "", context.func);
        builder->create_cond_br(cond_val, IFstmtBB, ELSEstmtBB);
    }

    builder->set_insert_point(IFstmtBB);
    node.if_statement->accept(*this);
    if (not builder->get_insert_block()->is_terminated())
        builder->create_br(endBB);

    if (node.else_statement) {
        builder->set_insert_point(ELSEstmtBB);
        node.else_statement->accept(*this);
        if (not builder->get_insert_block()->is_terminated())
            builder->create_br(endBB);
    }

    builder->set_insert_point(endBB);
    return nullptr;
}

Value *CminusfBuilder::visit(ASTIterationStmt &node) {
    auto expressionBB = BasicBlock::create(module.get(), "", context.func);

    if (not builder->get_insert_block()->is_terminated())
        builder->create_br(expressionBB);

    builder->set_insert_point(expressionBB);

    node.expression->accept(*this);
    auto expression = context.ValBridge;

    auto stmtBB = BasicBlock::create(module.get(), "", context.func);
    auto endBB = BasicBlock::create(module.get(), "", context.func);

    auto intORfp = expression->get_type()->is_integer_type();
    auto cond_val =
        (intORfp) ? static_cast<Value *>(
                        builder->create_icmp_ne(expression, CONST_INT(0)))
                  : static_cast<Value *>(
                        builder->create_fcmp_ne(expression, CONST_FP(0.0)));

    builder->create_cond_br(cond_val, stmtBB, endBB);

    builder->set_insert_point(stmtBB);
    node.statement->accept(*this);
    if (not builder->get_insert_block()->is_terminated())
        builder->create_br(expressionBB);

    builder->set_insert_point(endBB);
    return nullptr;
}

Value *CminusfBuilder::visit(ASTReturnStmt &node) {
    if (node.expression == nullptr) {
        builder->create_void_ret();
    } else {
        node.expression->accept(*this);

        auto funTy = context.func->get_function_type()->get_return_type();
        auto retTy = context.ValBridge->get_type();
        if (funTy != retTy) {
            if (funTy->is_integer_type())
                context.ValBridge =
                    builder->create_fptosi(context.ValBridge, INT32_T);
            else
                context.ValBridge =
                    builder->create_sitofp(context.ValBridge, FLOAT_T);
        }

        builder->create_ret(context.ValBridge);
    }
    return nullptr;
}

Value *CminusfBuilder::visit(ASTVar &node) {
    auto var = scope.find(node.id);
    auto intTy = var->get_type()->get_pointer_element_type()->is_integer_type();
    auto floatTy = var->get_type()->get_pointer_element_type()->is_float_type();
    auto ptrTy = var->get_type()->get_pointer_element_type()->is_pointer_type();

    auto assign = (context.assign) ? !(context.assign = false) : false;

    if (node.expression == nullptr) {
        if (assign) {
            context.ValBridge = var;
        } else {
            if (intTy || floatTy || ptrTy) {
                context.ValBridge = builder->create_load(var);
            } else {
                context.ValBridge =
                    builder->create_gep(var, {CONST_INT(0), CONST_INT(0)});
            }
        }
    } else {
        node.expression->accept(*this);
        auto index = context.ValBridge;

        if (index->get_type()->is_float_type())
            index = builder->create_fptosi(index, INT32_T);

        Value *idxCond = builder->create_icmp_ge(index, CONST_INT(0));

        auto normalBB = BasicBlock::create(module.get(), "", context.func);
        auto illegalBB = BasicBlock::create(module.get(), "", context.func);
        builder->create_cond_br(idxCond, normalBB, illegalBB);

        builder->set_insert_point(illegalBB);
        auto neg_idx_except_fun = scope.find("neg_idx_except");
        builder->create_call(static_cast<Function *>(neg_idx_except_fun), {});

        auto retTy = context.func->get_return_type();
        if (retTy->is_void_type())
            builder->create_void_ret();
        else if (retTy->is_float_type())
            builder->create_ret(CONST_FP(0.0));
        else
            builder->create_ret(CONST_INT(0));

        builder->set_insert_point(normalBB);
        auto ptr = var;
        auto idxs = {index};
        if (ptrTy)
            ptr = static_cast<Value *>(builder->create_load(var));
        else if (!intTy && !floatTy)
            idxs = {CONST_INT(0), index};
        auto addr_ptr = static_cast<Value *>(builder->create_gep(ptr, idxs));
        context.ValBridge =
            (assign) ? addr_ptr : builder->create_load(addr_ptr);
    }
    return nullptr;
}

Value *CminusfBuilder::visit(ASTAssignExpression &node) {
    context.assign = true;
    node.var->accept(*this);
    auto var = context.ValBridge;
    node.expression->accept(*this);
    auto varTy = var->get_type()->get_pointer_element_type();
    auto expressionTy = context.ValBridge->get_type();
    if (varTy != expressionTy) {
        if (expressionTy == INT32_T)
            context.ValBridge =
                builder->create_sitofp(context.ValBridge, FLOAT_T);
        else
            context.ValBridge =
                builder->create_fptosi(context.ValBridge, INT32_T);
    }
    builder->create_store(context.ValBridge, var);
    return nullptr;
}

Value *CminusfBuilder::visit(ASTSimpleExpression &node) {
    if (node.additive_expression_r == nullptr) {
        node.additive_expression_l->accept(*this);
    } else {
        node.additive_expression_l->accept(*this);
        auto l_val = context.ValBridge;
        node.additive_expression_r->accept(*this);
        auto r_val = context.ValBridge;

        auto lTy = l_val->get_type()->is_integer_type();
        auto rTy = r_val->get_type()->is_integer_type();
        auto intTy = lTy && rTy;

        if (lTy != rTy) {
            if (lTy) {
                l_val = builder->create_sitofp(l_val, FLOAT_T);
            } else {
                r_val = builder->create_sitofp(r_val, FLOAT_T);
            }
        }

        Value *cmp;
        switch (node.op) {
        case OP_LE:
            if (intTy)
                cmp = builder->create_icmp_le(l_val, r_val);
            else
                cmp = builder->create_fcmp_le(l_val, r_val);
            break;
        case OP_LT:
            if (intTy)
                cmp = builder->create_icmp_lt(l_val, r_val);
            else
                cmp = builder->create_fcmp_lt(l_val, r_val);
            break;
        case OP_GT:
            if (intTy)
                cmp = builder->create_icmp_gt(l_val, r_val);
            else
                cmp = builder->create_fcmp_gt(l_val, r_val);
            break;
        case OP_GE:
            if (intTy)
                cmp = builder->create_icmp_ge(l_val, r_val);
            else
                cmp = builder->create_fcmp_ge(l_val, r_val);
            break;
        case OP_EQ:
            if (intTy)
                cmp = builder->create_icmp_eq(l_val, r_val);
            else
                cmp = builder->create_fcmp_eq(l_val, r_val);
            break;
        case OP_NEQ:
            if (intTy)
                cmp = builder->create_icmp_ne(l_val, r_val);
            else
                cmp = builder->create_fcmp_ne(l_val, r_val);
            break;
        }

        context.ValBridge = builder->create_zext(cmp, INT32_T);
    }
    return nullptr;
}

Value *CminusfBuilder::visit(ASTAdditiveExpression &node) {
    if (node.additive_expression == nullptr) {
        node.term->accept(*this);
    } else {
        node.additive_expression->accept(*this);
        auto l_val = context.ValBridge;
        node.term->accept(*this);
        auto r_val = context.ValBridge;

        auto lTy = l_val->get_type()->is_integer_type();
        auto rTy = r_val->get_type()->is_integer_type();
        auto intTy = lTy && rTy;

        if (lTy != rTy) {
            if (lTy) {
                l_val = builder->create_sitofp(l_val, FLOAT_T);
            } else {
                r_val = builder->create_sitofp(r_val, FLOAT_T);
            }
        }

        switch (node.op) {
        case OP_PLUS:
            if (intTy)
                context.ValBridge = builder->create_iadd(l_val, r_val);
            else
                context.ValBridge = builder->create_fadd(l_val, r_val);
            break;
        case OP_MINUS:
            if (intTy)
                context.ValBridge = builder->create_isub(l_val, r_val);
            else
                context.ValBridge = builder->create_fsub(l_val, r_val);
            break;
        }
    }
    return nullptr;
}

Value *CminusfBuilder::visit(ASTTerm &node) {
    if (node.term == nullptr) {
        node.factor->accept(*this);
    } else {
        node.term->accept(*this);
        auto l_val = context.ValBridge;
        node.factor->accept(*this);
        auto r_val = context.ValBridge;

        auto lTy = l_val->get_type()->is_integer_type();
        auto rTy = r_val->get_type()->is_integer_type();
        auto intTy = lTy && rTy;

        if (lTy != rTy) {
            if (lTy) {
                l_val = builder->create_sitofp(l_val, FLOAT_T);
            } else {
                r_val = builder->create_sitofp(r_val, FLOAT_T);
            }
        }

        switch (node.op) {
        case OP_MUL:
            if (intTy)
                context.ValBridge = builder->create_imul(l_val, r_val);
            else
                context.ValBridge = builder->create_fmul(l_val, r_val);
            break;
        case OP_DIV:
            if (intTy)
                context.ValBridge = builder->create_isdiv(l_val, r_val);
            else
                context.ValBridge = builder->create_fdiv(l_val, r_val);
            break;
        }
    }
    return nullptr;
}

Value *CminusfBuilder::visit(ASTCall &node) {
    auto func = static_cast<Function *>(scope.find(node.id));
    auto paramTy = func->get_function_type()->param_begin();

    std::vector<Value *> args;
    for (auto &arg : node.args) {
        arg->accept(*this);
        auto argTy = context.ValBridge->get_type();
        if (argTy != *paramTy) {
            if (argTy->is_integer_type())
                context.ValBridge =
                    builder->create_sitofp(context.ValBridge, FLOAT_T);
            else
                context.ValBridge =
                    builder->create_fptosi(context.ValBridge, INT32_T);
        }
        args.push_back(context.ValBridge);
        paramTy++;
    }

    context.ValBridge = builder->create_call(func, args);
    return nullptr;
}