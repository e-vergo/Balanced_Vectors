// Lean compiler output
// Module: PsiIntegrals.Proofs.helper_lemmas
// Imports: public import Init public import PsiIntegrals.Definitions
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
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_5, x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_5, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_inc_ref(x_3);
x_9 = lean_apply_1(x_3, x_1);
x_10 = lean_apply_1(x_3, x_2);
x_11 = lean_int_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_int_sub(x_11, x_4);
lean_dec(x_11);
return x_12;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_1);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___redArg(x_3, x_4, x_5, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lp_PsiIntegrals___private_PsiIntegrals_Proofs_helper__lemmas_0__sliceComposition(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PsiIntegrals_PsiIntegrals_Definitions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PsiIntegrals_PsiIntegrals_Proofs_helper__lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PsiIntegrals_PsiIntegrals_Definitions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
