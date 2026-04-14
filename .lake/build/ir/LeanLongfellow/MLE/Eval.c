// Lean compiler output
// Module: LeanLongfellow.MLE.Eval
// Imports: public import Init public import LeanLongfellow.MLE.Defs public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise public import Mathlib.Algebra.BigOperators.Fin public import Mathlib.Algebra.Polynomial.Eval.Defs public import Mathlib.Data.Fin.Tuple.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fintype_piFinset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_cons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
static const lean_ctor_object lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___closed__0 = (const lean_object*)&lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___closed__0_value;
static const lean_ctor_object lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___closed__0_value)}};
static const lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___closed__1 = (const lean_object*)&lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___closed__0 = (const lean_object*)&lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_partialEvalFirst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_partialEvalFirst___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_partialEvalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0(lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = ((lean_object*)(lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___closed__1));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0___boxed(lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__0(v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__1(lean_object* v_p_13_, lean_object* v_inst_14_, lean_object* v_n_15_, lean_object* v_x_16_, lean_object* v_toMul_17_, lean_object* v_b_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc_ref(v_b_18_);
v___x_19_ = lean_apply_1(v_p_13_, v_b_18_);
v___x_20_ = lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis___redArg(v_inst_14_, v_n_15_, v_b_18_, v_x_16_);
v___x_21_ = lean_apply_2(v_toMul_17_, v___x_19_, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg(lean_object* v_inst_23_, lean_object* v_n_24_, lean_object* v_p_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_toCommRing_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_toAddCommMonoid_30_; lean_object* v___x_31_; lean_object* v_toMul_32_; lean_object* v___x_33_; lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_toCommRing_27_ = lean_ctor_get(v_inst_23_, 0);
lean_inc_ref(v_toCommRing_27_);
v___x_28_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_27_);
v___x_29_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_28_);
v_toAddCommMonoid_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc_ref(v_toAddCommMonoid_30_);
v___x_31_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_29_);
v_toMul_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_toMul_32_);
lean_dec_ref(v___x_31_);
lean_inc_n(v_n_24_, 2);
v___x_33_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_33_, 0, v_n_24_);
v___f_34_ = ((lean_object*)(lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___closed__0));
v___x_35_ = l_List_finRange(v_n_24_);
v___f_36_ = lean_alloc_closure((void*)(lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg___lam__1), 6, 5);
lean_closure_set(v___f_36_, 0, v_p_25_);
lean_closure_set(v___f_36_, 1, v_inst_23_);
lean_closure_set(v___f_36_, 2, v_n_24_);
lean_closure_set(v___f_36_, 3, v_x_26_);
lean_closure_set(v___f_36_, 4, v_toMul_32_);
v___x_37_ = lp_mathlib_Fintype_piFinset___redArg(v___x_33_, v___x_35_, v___f_34_);
v___x_38_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_30_, v___x_37_, v___f_36_);
lean_dec_ref(v_toAddCommMonoid_30_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval(lean_object* v_F_39_, lean_object* v_inst_40_, lean_object* v_n_41_, lean_object* v_p_42_, lean_object* v_x_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg(v_inst_40_, v_n_41_, v_p_42_, v_x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_partialEvalFirst___redArg___lam__0(lean_object* v_toSub_45_, lean_object* v_toOne_46_, lean_object* v_a_47_, lean_object* v_n_48_, lean_object* v_p_49_, lean_object* v_toMul_50_, lean_object* v_toAdd_51_, lean_object* v_b_52_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
lean_inc(v_a_47_);
v___x_53_ = lean_apply_2(v_toSub_45_, v_toOne_46_, v_a_47_);
v___x_54_ = 0;
v___x_55_ = lean_box(v___x_54_);
lean_inc_ref(v_b_52_);
lean_inc(v_n_48_);
v___x_56_ = lean_alloc_closure((void*)(lp_mathlib_Fin_cons___boxed), 5, 4);
lean_closure_set(v___x_56_, 0, v_n_48_);
lean_closure_set(v___x_56_, 1, lean_box(0));
lean_closure_set(v___x_56_, 2, v___x_55_);
lean_closure_set(v___x_56_, 3, v_b_52_);
lean_inc(v_p_49_);
v___x_57_ = lean_apply_1(v_p_49_, v___x_56_);
lean_inc(v_toMul_50_);
v___x_58_ = lean_apply_2(v_toMul_50_, v___x_53_, v___x_57_);
v___x_59_ = 1;
v___x_60_ = lean_box(v___x_59_);
v___x_61_ = lean_alloc_closure((void*)(lp_mathlib_Fin_cons___boxed), 5, 4);
lean_closure_set(v___x_61_, 0, v_n_48_);
lean_closure_set(v___x_61_, 1, lean_box(0));
lean_closure_set(v___x_61_, 2, v___x_60_);
lean_closure_set(v___x_61_, 3, v_b_52_);
v___x_62_ = lean_apply_1(v_p_49_, v___x_61_);
v___x_63_ = lean_apply_2(v_toMul_50_, v_a_47_, v___x_62_);
v___x_64_ = lean_apply_2(v_toAdd_51_, v___x_58_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_partialEvalFirst___redArg(lean_object* v_inst_65_, lean_object* v_n_66_, lean_object* v_p_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_toCommRing_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v_toMul_73_; lean_object* v_toAdd_74_; lean_object* v___x_75_; lean_object* v_toRing_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v_toAddMonoidWithOne_79_; lean_object* v_toSub_80_; lean_object* v_toOne_81_; lean_object* v___f_82_; 
v_toCommRing_69_ = lean_ctor_get(v_inst_65_, 0);
lean_inc_ref(v_toCommRing_69_);
v___x_70_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_69_);
v___x_71_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_70_);
v___x_72_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_71_);
v_toMul_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_toMul_73_);
v_toAdd_74_ = lean_ctor_get(v___x_72_, 1);
lean_inc(v_toAdd_74_);
lean_dec_ref(v___x_72_);
v___x_75_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_65_);
v_toRing_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_toRing_76_);
lean_dec_ref(v___x_75_);
v___x_77_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_76_);
v___x_78_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_77_);
v_toAddMonoidWithOne_79_ = lean_ctor_get(v___x_77_, 1);
lean_inc_ref(v_toAddMonoidWithOne_79_);
lean_dec_ref(v___x_77_);
v_toSub_80_ = lean_ctor_get(v___x_78_, 2);
lean_inc(v_toSub_80_);
lean_dec_ref(v___x_78_);
v_toOne_81_ = lean_ctor_get(v_toAddMonoidWithOne_79_, 2);
lean_inc(v_toOne_81_);
lean_dec_ref(v_toAddMonoidWithOne_79_);
v___f_82_ = lean_alloc_closure((void*)(lp_lean_x2dlongfellow_MultilinearPoly_partialEvalFirst___redArg___lam__0), 8, 7);
lean_closure_set(v___f_82_, 0, v_toSub_80_);
lean_closure_set(v___f_82_, 1, v_toOne_81_);
lean_closure_set(v___f_82_, 2, v_a_68_);
lean_closure_set(v___f_82_, 3, v_n_66_);
lean_closure_set(v___f_82_, 4, v_p_67_);
lean_closure_set(v___f_82_, 5, v_toMul_73_);
lean_closure_set(v___f_82_, 6, v_toAdd_74_);
return v___f_82_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_partialEvalFirst(lean_object* v_F_83_, lean_object* v_inst_84_, lean_object* v_n_85_, lean_object* v_p_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lp_lean_x2dlongfellow_MultilinearPoly_partialEvalFirst___redArg(v_inst_84_, v_n_85_, v_p_86_, v_a_87_);
return v___x_88_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_GroupWithZero_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Piecewise(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Fin(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fin_Tuple_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Eval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_GroupWithZero_Finset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Piecewise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fin_Tuple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
