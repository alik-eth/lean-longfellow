// Lean compiler output
// Module: LeanLongfellow.GKR.Combining
// Imports: public import Init public import LeanLongfellow.GKR.Circuit public import LeanLongfellow.MLE.Props
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_lean_x2dlongfellow_MultilinearPoly_boolToField___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_b__lr_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lp_lean_x2dlongfellow_MultilinearPoly_boolToField___redArg(v_inst_1_, v_b__lr_2_, v_i_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__1(lean_object* v_k_5_, lean_object* v_inst_6_, lean_object* v_b__lr_7_, lean_object* v_i_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_nat_add(v_k_5_, v_i_8_);
v___x_10_ = lp_lean_x2dlongfellow_MultilinearPoly_boolToField___redArg(v_inst_6_, v_b__lr_7_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__1___boxed(lean_object* v_k_11_, lean_object* v_inst_12_, lean_object* v_b__lr_13_, lean_object* v_i_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_lean_x2dlongfellow_combiningPoly___redArg___lam__1(v_k_11_, v_inst_12_, v_b__lr_13_, v_i_14_);
lean_dec(v_i_14_);
lean_dec(v_k_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__2(lean_object* v_k_16_, lean_object* v_inst_17_, lean_object* v_b__lr_18_, lean_object* v_gStar_19_, lean_object* v_i_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = lean_nat_dec_lt(v_i_20_, v_k_16_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_gStar_19_);
v___x_22_ = lean_nat_sub(v_i_20_, v_k_16_);
lean_dec(v_i_20_);
v___x_23_ = lp_lean_x2dlongfellow_MultilinearPoly_boolToField___redArg(v_inst_17_, v_b__lr_18_, v___x_22_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
lean_dec_ref(v_b__lr_18_);
lean_dec_ref(v_inst_17_);
v___x_24_ = lean_apply_1(v_gStar_19_, v_i_20_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__2___boxed(lean_object* v_k_25_, lean_object* v_inst_26_, lean_object* v_b__lr_27_, lean_object* v_gStar_28_, lean_object* v_i_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_lean_x2dlongfellow_combiningPoly___redArg___lam__2(v_k_25_, v_inst_26_, v_b__lr_27_, v_gStar_28_, v_i_29_);
lean_dec(v_k_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg___lam__3(lean_object* v_circuit_31_, lean_object* v_inst_32_, lean_object* v_k_33_, lean_object* v_gStar_34_, lean_object* v_j_35_, lean_object* v_toMul_36_, lean_object* v_b__lr_37_){
_start:
{
lean_object* v_quads_38_; lean_object* v_wires_39_; lean_object* v_l_40_; lean_object* v_r_41_; lean_object* v_glr_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_quads_38_ = lean_ctor_get(v_circuit_31_, 0);
lean_inc(v_quads_38_);
v_wires_39_ = lean_ctor_get(v_circuit_31_, 1);
lean_inc(v_wires_39_);
lean_dec_ref(v_circuit_31_);
lean_inc_ref_n(v_b__lr_37_, 2);
lean_inc_ref_n(v_inst_32_, 5);
v_l_40_ = lean_alloc_closure((void*)(lp_lean_x2dlongfellow_combiningPoly___redArg___lam__0), 3, 2);
lean_closure_set(v_l_40_, 0, v_inst_32_);
lean_closure_set(v_l_40_, 1, v_b__lr_37_);
lean_inc_n(v_k_33_, 3);
v_r_41_ = lean_alloc_closure((void*)(lp_lean_x2dlongfellow_combiningPoly___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v_r_41_, 0, v_k_33_);
lean_closure_set(v_r_41_, 1, v_inst_32_);
lean_closure_set(v_r_41_, 2, v_b__lr_37_);
v_glr_42_ = lean_alloc_closure((void*)(lp_lean_x2dlongfellow_combiningPoly___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v_glr_42_, 0, v_k_33_);
lean_closure_set(v_glr_42_, 1, v_inst_32_);
lean_closure_set(v_glr_42_, 2, v_b__lr_37_);
lean_closure_set(v_glr_42_, 3, v_gStar_34_);
v___x_43_ = lean_unsigned_to_nat(3u);
v___x_44_ = lean_nat_mul(v___x_43_, v_k_33_);
lean_inc(v_j_35_);
v___x_45_ = lean_apply_1(v_quads_38_, v_j_35_);
v___x_46_ = lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg(v_inst_32_, v___x_44_, v___x_45_, v_glr_42_);
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_j_35_, v___x_47_);
lean_dec(v_j_35_);
v___x_49_ = lean_apply_1(v_wires_39_, v___x_48_);
lean_inc(v___x_49_);
v___x_50_ = lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg(v_inst_32_, v_k_33_, v___x_49_, v_l_40_);
lean_inc(v_toMul_36_);
v___x_51_ = lean_apply_2(v_toMul_36_, v___x_46_, v___x_50_);
v___x_52_ = lp_lean_x2dlongfellow_MultilinearPoly_eval___redArg(v_inst_32_, v_k_33_, v___x_49_, v_r_41_);
v___x_53_ = lean_apply_2(v_toMul_36_, v___x_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___redArg(lean_object* v_inst_54_, lean_object* v_k_55_, lean_object* v_circuit_56_, lean_object* v_j_57_, lean_object* v_gStar_58_){
_start:
{
lean_object* v_toCommRing_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_toMul_63_; lean_object* v___f_64_; 
v_toCommRing_59_ = lean_ctor_get(v_inst_54_, 0);
lean_inc_ref(v_toCommRing_59_);
v___x_60_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_59_);
v___x_61_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_60_);
v___x_62_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_61_);
v_toMul_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_toMul_63_);
lean_dec_ref(v___x_62_);
v___f_64_ = lean_alloc_closure((void*)(lp_lean_x2dlongfellow_combiningPoly___redArg___lam__3), 7, 6);
lean_closure_set(v___f_64_, 0, v_circuit_56_);
lean_closure_set(v___f_64_, 1, v_inst_54_);
lean_closure_set(v___f_64_, 2, v_k_55_);
lean_closure_set(v___f_64_, 3, v_gStar_58_);
lean_closure_set(v___f_64_, 4, v_j_57_);
lean_closure_set(v___f_64_, 5, v_toMul_63_);
return v___f_64_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly(lean_object* v_F_65_, lean_object* v_inst_66_, lean_object* v_k_67_, lean_object* v_depth_68_, lean_object* v_circuit_69_, lean_object* v_j_70_, lean_object* v_gStar_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lp_lean_x2dlongfellow_combiningPoly___redArg(v_inst_66_, v_k_67_, v_circuit_69_, v_j_70_, v_gStar_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_combiningPoly___boxed(lean_object* v_F_73_, lean_object* v_inst_74_, lean_object* v_k_75_, lean_object* v_depth_76_, lean_object* v_circuit_77_, lean_object* v_j_78_, lean_object* v_gStar_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_lean_x2dlongfellow_combiningPoly(v_F_73_, v_inst_74_, v_k_75_, v_depth_76_, v_circuit_77_, v_j_78_, v_gStar_79_);
lean_dec(v_depth_76_);
return v_res_80_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_GKR_Circuit(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Props(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_GKR_Combining(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_GKR_Circuit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Props(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
