// Lean compiler output
// Module: LeanLongfellow.MLE.Defs
// Imports: public import Init public import Mathlib.Data.Fintype.Pi public import Mathlib.Algebra.BigOperators.Group.Finset.Basic public import Mathlib.Algebra.Field.Defs
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
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_boolToField___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_boolToField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_boolToField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_boolToField___redArg(lean_object* v_inst_1_, lean_object* v_b_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_apply_1(v_b_2_, v_i_3_);
v___x_5_ = lean_unbox(v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v_toCommRing_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_toZero_10_; 
v_toCommRing_6_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toCommRing_6_);
lean_dec_ref(v_inst_1_);
v___x_7_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_6_);
v___x_8_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_7_);
v___x_9_ = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(v___x_8_);
v_toZero_10_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_toZero_10_);
lean_dec_ref(v___x_9_);
return v_toZero_10_;
}
else
{
lean_object* v___x_11_; lean_object* v_toRing_12_; lean_object* v___x_13_; lean_object* v_toAddMonoidWithOne_14_; lean_object* v_toOne_15_; 
v___x_11_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1_);
v_toRing_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_toRing_12_);
lean_dec_ref(v___x_11_);
v___x_13_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_12_);
v_toAddMonoidWithOne_14_ = lean_ctor_get(v___x_13_, 1);
lean_inc_ref(v_toAddMonoidWithOne_14_);
lean_dec_ref(v___x_13_);
v_toOne_15_ = lean_ctor_get(v_toAddMonoidWithOne_14_, 2);
lean_inc(v_toOne_15_);
lean_dec_ref(v_toAddMonoidWithOne_14_);
return v_toOne_15_;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_boolToField(lean_object* v_F_16_, lean_object* v_inst_17_, lean_object* v_n_18_, lean_object* v_b_19_, lean_object* v_i_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_lean_x2dlongfellow_MultilinearPoly_boolToField___redArg(v_inst_17_, v_b_19_, v_i_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_boolToField___boxed(lean_object* v_F_22_, lean_object* v_inst_23_, lean_object* v_n_24_, lean_object* v_b_25_, lean_object* v_i_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_lean_x2dlongfellow_MultilinearPoly_boolToField(v_F_22_, v_inst_23_, v_n_24_, v_b_25_, v_i_26_);
lean_dec(v_n_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis___redArg___lam__0(lean_object* v_b_28_, lean_object* v_inst_29_, lean_object* v_x_30_, lean_object* v_i_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
lean_inc(v_i_31_);
v___x_32_ = lean_apply_1(v_b_28_, v_i_31_);
v___x_33_ = lean_unbox(v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v_toRing_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v_toAddMonoidWithOne_38_; lean_object* v_toSub_39_; lean_object* v_toOne_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_34_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_29_);
v_toRing_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc_ref(v_toRing_35_);
lean_dec_ref(v___x_34_);
v___x_36_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_35_);
v___x_37_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_36_);
v_toAddMonoidWithOne_38_ = lean_ctor_get(v___x_36_, 1);
lean_inc_ref(v_toAddMonoidWithOne_38_);
lean_dec_ref(v___x_36_);
v_toSub_39_ = lean_ctor_get(v___x_37_, 2);
lean_inc(v_toSub_39_);
lean_dec_ref(v___x_37_);
v_toOne_40_ = lean_ctor_get(v_toAddMonoidWithOne_38_, 2);
lean_inc(v_toOne_40_);
lean_dec_ref(v_toAddMonoidWithOne_38_);
v___x_41_ = lean_apply_1(v_x_30_, v_i_31_);
v___x_42_ = lean_apply_2(v_toSub_39_, v_toOne_40_, v___x_41_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; 
lean_dec_ref(v_inst_29_);
v___x_43_ = lean_apply_1(v_x_30_, v_i_31_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis___redArg(lean_object* v_inst_44_, lean_object* v_n_45_, lean_object* v_b_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_toCommRing_48_; lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_toCommRing_48_ = lean_ctor_get(v_inst_44_, 0);
lean_inc_ref(v_toCommRing_48_);
v___f_49_ = lean_alloc_closure((void*)(lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis___redArg___lam__0), 4, 3);
lean_closure_set(v___f_49_, 0, v_b_46_);
lean_closure_set(v___f_49_, 1, v_inst_44_);
lean_closure_set(v___f_49_, 2, v_x_47_);
v___x_50_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_48_);
lean_dec_ref(v_toCommRing_48_);
v___x_51_ = l_List_finRange(v_n_45_);
v___x_52_ = lp_mathlib_Finset_prod___redArg(v___x_50_, v___x_51_, v___f_49_);
lean_dec_ref(v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis(lean_object* v_F_53_, lean_object* v_inst_54_, lean_object* v_n_55_, lean_object* v_b_56_, lean_object* v_x_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_lean_x2dlongfellow_MultilinearPoly_lagrangeBasis___redArg(v_inst_54_, v_n_55_, v_b_56_, v_x_57_);
return v___x_58_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Pi(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Field_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Pi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Field_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
