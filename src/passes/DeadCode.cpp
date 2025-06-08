#include "DeadCode.hpp"
#include "logging.hpp"
#include <vector>

// 处理流程：两趟处理，mark 标记有用变量，sweep 删除无用指令
void DeadCode::run() {
    bool changed{};
    func_info->run();
    do {
        changed = false;
        for (auto &F : m_->get_functions()) {
            auto func = &F;
            changed |= clear_basic_blocks(func);
            mark(func);
            changed |= sweep(func);
        }
    } while (changed);
    LOG_INFO << "dead code pass erased " << ins_count << " instructions";
}

bool DeadCode::clear_basic_blocks(Function *func) {
    bool changed = 0;
    std::vector<BasicBlock *> to_erase;
    for (auto &bb1 : func->get_basic_blocks()) {
        auto bb = &bb1;
        if(bb->get_pre_basic_blocks().empty() && bb != func->get_entry_block()) {
            to_erase.push_back(bb);
            changed = 1;
        }
    }
    for (auto &bb : to_erase) {
        bb->erase_from_parent();
        delete bb;
    }
    return changed;
}

// 标记阶段：递归标记所有有用的指令
void DeadCode::mark(Function *func) {
    work_list.clear();
    marked.clear();

    // 首先将所有关键指令（如有副作用的指令、控制流指令等）加入 work_list 并标记
    for (auto &bb : func->get_basic_blocks()) {
        for (auto &ins : bb.get_instructions()) {
            if (is_critical(&ins)) {
                marked[&ins] = true;
                work_list.push_back(&ins);
            }
        }
    }

    // 递归标记所有对关键指令有影响的指令
    while (work_list.empty() == false) {
        auto now = work_list.front();
        work_list.pop_front();

        mark(now);
    }
}

// 标记单条指令的所有依赖（操作数）为有用
void DeadCode::mark(Instruction *ins) {
    for (auto op : ins->get_operands()) {
        auto def = dynamic_cast<Instruction *>(op);
        if (def == nullptr)
            continue; // 不是指令定义，跳过
        if (marked[def])
            continue; // 已经标记过，跳过
        if (def->get_function() != ins->get_function())
            continue; // 不属于同一个函数，跳过
        marked[def] = true;
        work_list.push_back(def); // 加入队列，递归处理
    }
}

// 清扫阶段：删除未被标记为有用的指令
bool DeadCode::sweep(Function *func) {
    std::unordered_set<Instruction *> wait_del{};
    // 收集所有未被标记的指令
    for (auto &bb : func->get_basic_blocks()) {
        for (auto it = bb.get_instructions().begin();
             it != bb.get_instructions().end();) {
            if (marked[&*it]) {
                ++it; // 有用指令，跳过
                continue;
            } else {
                auto tmp = &*it;
                wait_del.insert(tmp); // 无用指令，加入待删除集合
                it++;
            }
        }
    }
    // 先移除所有操作数，断开依赖
    for (auto inst : wait_del)
        inst->remove_all_operands();
    // 从基本块中删除指令
    for (auto inst : wait_del)
        inst->get_parent()->get_instructions().erase(inst);
    ins_count += wait_del.size();
    return not wait_del.empty(); // 若有删除则返回 true
}

bool DeadCode::is_critical(Instruction *ins) {
    // 对纯函数的无用调用也可以在删除之列
    if (ins->is_call()) {
        auto call_inst = dynamic_cast<CallInst *>(ins);
        auto callee = dynamic_cast<Function *>(call_inst->get_operand(0));
        if (func_info->is_pure_function(callee))
            return false;
        return true;
    }
    if (ins->is_br() || ins->is_ret())
        return true;
    if (ins->is_store())
        return true;
    return false;
}

void DeadCode::sweep_globally() {
    std::vector<Function *> unused_funcs;
    std::vector<GlobalVariable *> unused_globals;
    for (auto &f_r : m_->get_functions()) {
        if (f_r.get_use_list().size() == 0 and f_r.get_name() != "main")
            unused_funcs.push_back(&f_r);
    }
    for (auto &glob_var_r : m_->get_global_variable()) {
        if (glob_var_r.get_use_list().size() == 0)
            unused_globals.push_back(&glob_var_r);
    }
    // changed |= unused_funcs.size() or unused_globals.size();
    for (auto func : unused_funcs)
        m_->get_functions().erase(func);
    for (auto glob : unused_globals)
        m_->get_global_variable().erase(glob);
}
