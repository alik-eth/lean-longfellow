// Lean compiler output
// Module: LeanLongfellow.FiatShamir.Transform
// Imports: public import Init public import LeanLongfellow.Sumcheck.Protocol public import LeanLongfellow.Sumcheck.Completeness public import LeanLongfellow.FiatShamir.Oracle
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
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_toRounds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_toRounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_toRounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_toRounds___redArg(lean_object* v_proof_1_, lean_object* v_cs_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
lean_inc(v_i_3_);
v___x_4_ = lean_apply_1(v_proof_1_, v_i_3_);
v___x_5_ = lean_apply_1(v_cs_2_, v_i_3_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_4_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_toRounds(lean_object* v_F_7_, lean_object* v_inst_8_, lean_object* v_n_9_, lean_object* v_proof_10_, lean_object* v_cs_11_, lean_object* v_i_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_lean_x2dlongfellow_toRounds___redArg(v_proof_10_, v_cs_11_, v_i_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_lean_x2dlongfellow_toRounds___boxed(lean_object* v_F_14_, lean_object* v_inst_15_, lean_object* v_n_16_, lean_object* v_proof_17_, lean_object* v_cs_18_, lean_object* v_i_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_lean_x2dlongfellow_toRounds(v_F_14_, v_inst_15_, v_n_16_, v_proof_17_, v_cs_18_, v_i_19_);
lean_dec(v_n_16_);
lean_dec_ref(v_inst_15_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Protocol(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Completeness(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_FiatShamir_Oracle(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_FiatShamir_Transform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Protocol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Completeness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_FiatShamir_Oracle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
