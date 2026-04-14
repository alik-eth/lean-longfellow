// Lean compiler output
// Module: LeanLongfellow.Sumcheck.Protocol
// Imports: public import Init public import LeanLongfellow.MLE.Defs public import LeanLongfellow.MLE.Eval public import LeanLongfellow.MLE.Props public import Mathlib.Algebra.Polynomial.Eval.Defs
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter___redArg(lean_object* v_n_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_n_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v_one_8_; lean_object* v_n_9_; lean_object* v___x_10_; 
lean_dec(v_h__1_2_);
v_one_8_ = lean_unsigned_to_nat(1u);
v_n_9_ = lean_nat_sub(v_n_1_, v_one_8_);
v___x_10_ = lean_apply_1(v_h__2_3_, v_n_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter___redArg___boxed(lean_object* v_n_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter___redArg(v_n_11_, v_h__1_12_, v_h__2_13_);
lean_dec(v_n_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter(lean_object* v_motive_15_, lean_object* v_n_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_){
_start:
{
lean_object* v_zero_19_; uint8_t v_isZero_20_; 
v_zero_19_ = lean_unsigned_to_nat(0u);
v_isZero_20_ = lean_nat_dec_eq(v_n_16_, v_zero_19_);
if (v_isZero_20_ == 1)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_18_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__1_17_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_one_23_; lean_object* v_n_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_17_);
v_one_23_ = lean_unsigned_to_nat(1u);
v_n_24_ = lean_nat_sub(v_n_16_, v_one_23_);
v___x_25_ = lean_apply_1(v_h__2_18_, v_n_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter___boxed(lean_object* v_motive_26_, lean_object* v_n_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_lean_x2dlongfellow___private_LeanLongfellow_Sumcheck_Protocol_0__honestProver_match__1_splitter(v_motive_26_, v_n_27_, v_h__1_28_, v_h__2_29_);
lean_dec(v_n_27_);
return v_res_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Defs(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Eval(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Props(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Protocol(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Props(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Eval_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
