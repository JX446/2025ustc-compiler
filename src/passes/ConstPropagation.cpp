#include "ConstPropagation.hpp"

#include "Instruction.hpp"
#include "logging.hpp"

ConstantInt *ConstFolder::compute(Instruction::OpID op, ConstantInt *value1, ConstantInt *value2) {
    int c_value1 = value1->get_value();
    int c_value2 = value2->get_value();

    switch (op) {
    case Instruction::add:
        return ConstantInt::get(c_value1 + c_value2, module_);
        break;
    case Instruction::sub:
        return ConstantInt::get(c_value1 - c_value2, module_);
        break;
    case Instruction::mul:
        return ConstantInt::get(c_value1 * c_value2, module_);
        break;
    case Instruction::sdiv:
        return ConstantInt::get(static_cast<int>(c_value1 / c_value2), module_);
        break;
    case Instruction::eq:
        return ConstantInt::get(c_value1 == c_value2, module_);
        break;
    case Instruction::ne:
        return ConstantInt::get(c_value1 != c_value2, module_);
        break;
    case Instruction::gt:
        return ConstantInt::get(c_value1 > c_value2, module_);
        break;
    case Instruction::ge:
        return ConstantInt::get(c_value1 >= c_value2, module_);
        break;
    case Instruction::lt:
        return ConstantInt::get(c_value1 < c_value2, module_);
        break;
    case Instruction::le:
        return ConstantInt::get(c_value1 <= c_value2, module_);
        break;
    default:
        return nullptr;
        break;
    }
}

ConstantFP *ConstFolder::compute(Instruction::OpID op, ConstantFP *value1, ConstantFP *value2) {
    float c_value1 = value1->get_value();
    float c_value2 = value2->get_value();
    switch (op) {
    case Instruction::fadd:
        return ConstantFP::get(c_value1 + c_value2, module_);
        break;
    case Instruction::fsub:
        return ConstantFP::get(c_value1 - c_value2, module_);
        break;
    case Instruction::fmul:
        return ConstantFP::get(c_value1 * c_value2, module_);
        break;
    case Instruction::fdiv:
        return ConstantFP::get(c_value1 / c_value2, module_);
        break;
    case Instruction::feq:
        return ConstantFP::get(c_value1 == c_value2, module_);
        break;
    case Instruction::fne:
        return ConstantFP::get(c_value1 != c_value2, module_);
        break;
    case Instruction::fgt:
        return ConstantFP::get(c_value1 > c_value2, module_);
        break;
    case Instruction::fge:
        return ConstantFP::get(c_value1 >= c_value2, module_);
        break;
    case Instruction::flt:
        return ConstantFP::get(c_value1 < c_value2, module_);
        break;
    case Instruction::fle:
        return ConstantFP::get(c_value1 <= c_value2, module_);
        break;
    default:
        return nullptr;
        break;
    }
}
ConstantFP *ConstFolder::compute(Instruction::OpID op, ConstantInt *value1) {
    int c_value1 = value1->get_value();

    switch (op) {
    case Instruction::sitofp:
        return ConstantFP::get((float) c_value1, module_);
        break;

    default:
        return nullptr;
        break;
    }
}

ConstantInt *ConstFolder::compute(Instruction::OpID op, ConstantFP *value1) {
    float c_value1 = value1->get_value();
    switch (op) {
    case Instruction::fptosi:
        return ConstantInt::get(static_cast<int>(c_value1), module_);
        break;

    default:
        return nullptr;
        break;
    }
}

ConstantFP *cast_constantfp(Value *value) {
    auto constant_fp_ptr = dynamic_cast<ConstantFP *>(value);
    if (constant_fp_ptr) {
        return constant_fp_ptr;
    }
    return nullptr;
}
ConstantInt *cast_constantint(Value *value) {
    auto constant_int_ptr = dynamic_cast<ConstantInt *>(value);
    if (constant_int_ptr) {
        return constant_int_ptr;
    }
    return nullptr;
}

void ConstPropagation::run() {
    for (auto &func : m_->get_functions()) {

        for (auto &bb : func.get_basic_blocks()) {
            wait_delete.clear();

            for (auto &instr : bb.get_instructions()) {
                // clear glbalvar_def map

                if (instr.is_add() || instr.is_sub() || instr.is_mul() || instr.is_div()) {
                    auto value1 = cast_constantint(instr.get_operand(0));
                    auto value2 = cast_constantint(instr.get_operand(1));
                    if (value1 && value2) {
                        auto fold_const = folder->compute(instr.get_instr_type(), value1, value2);

                        instr.replace_all_use_with(fold_const);
                        wait_delete.push_back(&instr);
                    }
                }
                // TODO: fold other type of expression
                else if (instr.is_fadd() || instr.is_fsub() || instr.is_fmul() || instr.is_fdiv()) {;
                    auto value1 = cast_constantfp(instr.get_operand(0));
                    auto value2 = cast_constantfp(instr.get_operand(1));
                    if (value1 && value2) {
                        auto fold_const = folder->compute(instr.get_instr_type(), value1, value2);

                        instr.replace_all_use_with(fold_const);
                        wait_delete.push_back(&instr);
                    }
                } else if (instr.is_si2fp()) {
                    auto value1 = cast_constantint(instr.get_operand(0));
                    if (value1) {
                        auto fold_const = folder->compute(instr.get_instr_type(), value1);

                        instr.replace_all_use_with(fold_const);
                        wait_delete.push_back(&instr);
                    }
                } else if (instr.is_fp2si()) {
                    auto value1 = cast_constantfp(instr.get_operand(0));
                    if (value1) {
                        auto fold_const = folder->compute(instr.get_instr_type(), value1);

                        instr.replace_all_use_with(fold_const);
                        wait_delete.push_back(&instr);
                    }
                } else if (instr.is_cmp()) {
                    auto value1 = cast_constantint(instr.get_operand(0));
                    auto value2 = cast_constantint(instr.get_operand(1));
                    if (value1 && value2) {
                        auto fold_const = folder->compute(instr.get_instr_type(), value1, value2);

                        instr.replace_all_use_with(fold_const);
                        wait_delete.push_back(&instr);
                    }
                } else if (instr.is_fcmp()) {
                    auto value1 = cast_constantfp(instr.get_operand(0));
                    auto value2 = cast_constantfp(instr.get_operand(1));
                    if (value1 && value2) {
                        ConstantInt *temp;
                        auto fold_const = folder->compute(instr.get_instr_type(), value1, value2);
                        if(fold_const == ConstantFP::get(0, m_)) temp = ConstantInt::get(0, m_);
                        else temp = ConstantInt::get(1, m_);
                        instr.replace_all_use_with(temp);
                        wait_delete.push_back(&instr);
                    }
                } else if (instr.is_zext()) {
                    auto value = cast_constantint(instr.get_operand(0));
                    if (value) {
                        // 检查是否是布尔值常量
                        std::string str = value->print();
                        if (str.find("true") != std::string::npos || str.find("false") != std::string::npos) {
                            // 如果是布尔值常量，保留 zext
                            continue;
                        }
                        // 如果是普通整数常量，则可以直接替换
                        instr.replace_all_use_with(value);
                        wait_delete.push_back(&instr);
                    }
                }
                else if (instr.is_phi() && instr.get_operands().size() == 4) {
                    auto value1 = cast_constantint(instr.get_operand(0));
                    auto value2 = cast_constantint(instr.get_operand(2));
                    if (value1 && value2) {
                        if (value1->get_value() == value2->get_value()) {
                            instr.replace_all_use_with(instr.get_operand(0));
                        }
                    }
                }   
            }
            globalvar_def.clear();
            for (auto instr : wait_delete) {
                bb.erase_instr(instr);
            }
        }
    }

    for (auto &func : m_->get_functions()) {
        for (auto &bb : func.get_basic_blocks()) {
            builder->set_insert_point(&bb);
            // TODO: check if conditional branch's condition is constant
            if(bb.get_terminator()->is_br() && bb.get_terminator()->get_operands().size() == 3) {
                auto cond_br = static_cast<BranchInst*>(bb.get_terminator());
                auto cond = cond_br->get_operand(0);
                auto cond_const = cast_constantint(cond);
                auto ops = cond_br->get_operands();
                if(cond_const) {
                    BasicBlock* succ_bb;
                    if(cond_const->get_value() == 1){
                        succ_bb = static_cast<BasicBlock*>(cond_br->get_operand(2));
                    }
                    else succ_bb = static_cast<BasicBlock*>(cond_br->get_operand(1));
                    for(auto &inst1 : succ_bb->get_instructions()){
                        auto inst = &inst1;
                        if(inst->is_phi()){
                            for(unsigned int i = 1; i < inst->get_num_operand(); i += 2)
                                if(inst->get_operand(i) == &bb) {
                                    inst->remove_operand(i - 1);
                                    inst->remove_operand(i - 1);
                                }
                        }
                    }
                    bb.erase_instr(cond_br);
                    if(cond_const->get_value() == 1) {
                        builder->create_br(static_cast<BasicBlock*>(ops[1]));
                    } else {
                        builder->create_br(static_cast<BasicBlock*>(ops[2]));
                    }
                    delete_bb.push_back(&bb);
                }
            }
        }
        for (auto bb : delete_bb) {
            clear_blocks_recs(bb);
        }
        delete_bb.clear();
    }
}

bool ConstPropagation::is_entry(BasicBlock *bb) {
    // TODO
    if(bb == bb->get_parent()->get_entry_block())
        return true;
    return false;
}

void ConstPropagation::clear_blocks_recs(BasicBlock *start_bb) {
    auto func = start_bb->get_parent();
    if (func == nullptr) {
        LOG(ERROR) << "basic block-" << start_bb->get_name() << " has no parent function";
    } else {
        auto prev_bb = start_bb->get_pre_basic_blocks();
        // start_bb has no previous bb and is not the entry of parent function
        if (prev_bb.size() == 0 && !is_entry(start_bb)) {
            func->remove(start_bb);
            auto succ_bb = start_bb->get_succ_basic_blocks();
            for (auto each_succ_bb : succ_bb) {
                std::vector<Instruction*> del_inst;
                for (auto &instr1 : each_succ_bb->get_instructions()) {
                    auto instr = &instr1;
                    if (instr->is_phi()) {
                        LOG(DEBUG) << "Find a PHI instruction in the sucess node of "
                                      "useless branch";
                        for (unsigned int i = 1; i < instr->get_num_operand(); i += 2) {
                            if (instr->get_operand(i) == start_bb &&
                                start_bb->get_pre_basic_blocks().size() <= 0) {
                                LOG(DEBUG) << "remove unuseful phi branch in the index of " << i - 1
                                           << " and " << i;

                                instr->remove_operand(i - 1);
                                instr->remove_operand(i - 1);
                            }
                        }
                        int operands_num_phi = instr->get_num_operand();
                        if (operands_num_phi == 2) {
                            auto value = instr->get_operand(0);
                            instr->replace_all_use_with(cast_constantint(value));
                            del_inst.push_back(instr);
                        }
                    }
                }
                for(auto instr : del_inst) each_succ_bb->erase_instr(instr);
                clear_blocks_recs(each_succ_bb);
            }
        }
    }
}