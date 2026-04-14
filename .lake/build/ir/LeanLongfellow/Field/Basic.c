// Lean compiler output
// Module: LeanLongfellow.Field.Basic
// Imports: public import Init public import LeanLongfellow.MLE.Defs public import LeanLongfellow.MLE.Eval public import LeanLongfellow.MLE.Props public import Mathlib.Algebra.Field.ZMod
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
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
static lean_once_cell_t lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__0;
static lean_once_cell_t lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__1;
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0(lean_object*);
static lean_once_cell_t lp_lean_x2dlongfellow_examplePoly___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_lean_x2dlongfellow_examplePoly___lam__0___closed__0;
static lean_once_cell_t lp_lean_x2dlongfellow_examplePoly___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_lean_x2dlongfellow_examplePoly___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_examplePoly___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_examplePoly___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_examplePoly;
static lean_object* _init_lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(97u);
v___x_2_ = lp_mathlib_ZMod_instField___redArg(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__0, &lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__0_once, _init_lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__0);
v___x_4_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0(lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; lean_object* v_toRing_7_; lean_object* v___x_8_; lean_object* v_toAddMonoidWithOne_9_; lean_object* v_toNatCast_10_; lean_object* v___x_11_; 
v___x_6_ = lean_obj_once(&lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__1, &lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__1_once, _init_lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__1);
v_toRing_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_toRing_7_);
v___x_8_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_7_);
v_toAddMonoidWithOne_9_ = lean_ctor_get(v___x_8_, 1);
lean_inc_ref(v_toAddMonoidWithOne_9_);
lean_dec_ref(v___x_8_);
v_toNatCast_10_ = lean_ctor_get(v_toAddMonoidWithOne_9_, 0);
lean_inc(v_toNatCast_10_);
lean_dec_ref(v_toAddMonoidWithOne_9_);
v___x_11_ = lean_apply_1(v_toNatCast_10_, v_a_5_);
return v___x_11_;
}
}
static lean_object* _init_lp_lean_x2dlongfellow_examplePoly___lam__0___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(5u);
v___x_13_ = lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0(v___x_12_);
return v___x_13_;
}
}
static lean_object* _init_lp_lean_x2dlongfellow_examplePoly___lam__0___closed__1(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(3u);
v___x_15_ = lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_examplePoly___lam__0(lean_object* v___x_16_, lean_object* v_toOne_17_, lean_object* v_b_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_nat_mod(v___x_19_, v___x_16_);
lean_inc_ref(v_b_18_);
v___x_21_ = lean_apply_1(v_b_18_, v___x_20_);
v___x_22_ = lean_unbox(v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_mod(v___x_23_, v___x_16_);
lean_dec(v___x_16_);
v___x_25_ = lean_apply_1(v_b_18_, v___x_24_);
v___x_26_ = lean_unbox(v___x_25_);
if (v___x_26_ == 0)
{
lean_inc(v_toOne_17_);
return v_toOne_17_;
}
else
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&lp_lean_x2dlongfellow_examplePoly___lam__0___closed__0, &lp_lean_x2dlongfellow_examplePoly___lam__0___closed__0_once, _init_lp_lean_x2dlongfellow_examplePoly___lam__0___closed__0);
return v___x_27_;
}
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_nat_mod(v___x_28_, v___x_16_);
v___x_30_ = lean_apply_1(v_b_18_, v___x_29_);
v___x_31_ = lean_unbox(v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; 
v___x_32_ = lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0(v___x_16_);
return v___x_32_;
}
else
{
lean_object* v___x_33_; 
lean_dec(v___x_16_);
v___x_33_ = lean_obj_once(&lp_lean_x2dlongfellow_examplePoly___lam__0___closed__1, &lp_lean_x2dlongfellow_examplePoly___lam__0___closed__1_once, _init_lp_lean_x2dlongfellow_examplePoly___lam__0___closed__1);
return v___x_33_;
}
}
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_examplePoly___lam__0___boxed(lean_object* v___x_34_, lean_object* v_toOne_35_, lean_object* v_b_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_lean_x2dlongfellow_examplePoly___lam__0(v___x_34_, v_toOne_35_, v_b_36_);
lean_dec(v_toOne_35_);
return v_res_37_;
}
}
static lean_object* _init_lp_lean_x2dlongfellow_examplePoly(void){
_start:
{
lean_object* v___x_38_; lean_object* v_toRing_39_; lean_object* v___x_40_; lean_object* v_toAddMonoidWithOne_41_; lean_object* v_toOne_42_; lean_object* v___x_43_; lean_object* v___f_44_; 
v___x_38_ = lean_obj_once(&lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__1, &lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__1_once, _init_lp_lean_x2dlongfellow_Nat_cast___at___00examplePoly_spec__0___closed__1);
v_toRing_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc_ref(v_toRing_39_);
v___x_40_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_39_);
v_toAddMonoidWithOne_41_ = lean_ctor_get(v___x_40_, 1);
lean_inc_ref(v_toAddMonoidWithOne_41_);
lean_dec_ref(v___x_40_);
v_toOne_42_ = lean_ctor_get(v_toAddMonoidWithOne_41_, 2);
lean_inc(v_toOne_42_);
lean_dec_ref(v_toAddMonoidWithOne_41_);
v___x_43_ = lean_unsigned_to_nat(2u);
v___f_44_ = lean_alloc_closure((void*)(lp_lean_x2dlongfellow_examplePoly___lam__0___boxed), 3, 2);
lean_closure_set(v___f_44_, 0, v___x_43_);
lean_closure_set(v___f_44_, 1, v_toOne_42_);
return v___f_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Defs(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Eval(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Props(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Field_ZMod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_Field_Basic(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Algebra_Field_ZMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_lean_x2dlongfellow_examplePoly = _init_lp_lean_x2dlongfellow_examplePoly();
lean_mark_persistent(lp_lean_x2dlongfellow_examplePoly);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
