// Lean compiler output
// Module: LeanLongfellow
// Imports: public import Init public import LeanLongfellow.MLE.Defs public import LeanLongfellow.MLE.Eval public import LeanLongfellow.MLE.Extension public import LeanLongfellow.MLE.Props public import LeanLongfellow.Sumcheck.Protocol public import LeanLongfellow.Sumcheck.Completeness public import LeanLongfellow.Sumcheck.Soundness public import LeanLongfellow.Field.Basic public import LeanLongfellow.FiatShamir.Oracle public import LeanLongfellow.FiatShamir.Transform public import LeanLongfellow.FiatShamir.Soundness
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Defs(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Eval(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Extension(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Props(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Protocol(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Completeness(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Soundness(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_Field_Basic(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_FiatShamir_Oracle(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_FiatShamir_Transform(uint8_t builtin);
lean_object* initialize_lean_x2dlongfellow_LeanLongfellow_FiatShamir_Soundness(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean_x2dlongfellow_LeanLongfellow(uint8_t builtin) {
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
res = initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_MLE_Props(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Protocol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Completeness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_Sumcheck_Soundness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_Field_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_FiatShamir_Oracle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_FiatShamir_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean_x2dlongfellow_LeanLongfellow_FiatShamir_Soundness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
