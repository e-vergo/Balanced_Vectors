// Lean compiler output
// Module: PsiIntegrals.Definitions
// Imports: public import Init public import Mathlib.Data.Fin.Basic public import Mathlib.Data.Fin.Tuple.Basic public import Mathlib.Algebra.BigOperators.Fin public import Mathlib.GroupTheory.Perm.Basic public import Mathlib.Data.Rat.Defs public import Mathlib.Tactic
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
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_imbalance(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_Multiset_sum___at___00Finset_sum___at___00imbalance_spec__0_spec__0(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0___closed__0;
lean_object* l_Int_pow(lean_object*, lean_object*);
static lean_object* lp_PsiIntegrals_Multiset_sum___at___00Finset_sum___at___00imbalance_spec__0_spec__0___closed__0;
LEAN_EXPORT uint8_t lp_PsiIntegrals_nonzeroCount___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_instCoeFunForallFinInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_instCoeFunForallFinInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_Finset_sum___at___00imbalance_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_modify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_nonzeroCount___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_Finset_sum___at___00imbalance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_nonzeroCount(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_instCoeFunForallFinInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated___redArg(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_imbalance___lam__0(lean_object*, lean_object*);
static lean_object* lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_instCoeFunForallFinInt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_instCoeFunForallFinInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_PsiIntegrals_WeakComposition_instCoeFunForallFinInt___lam__0), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_instCoeFunForallFinInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_PsiIntegrals_WeakComposition_instCoeFunForallFinInt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___closed__0;
return x_5;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_PsiIntegrals_WeakComposition_concentrated___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_concentrated___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_PsiIntegrals_WeakComposition_concentrated(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_1);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = lean_nat_dec_eq(x_4, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_apply_1(x_3, x_2);
x_9 = lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0___closed__0;
x_10 = lean_int_add(x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
x_12 = lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0___closed__0;
x_13 = lean_int_sub(x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_modify___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0), 4, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_modify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_PsiIntegrals_WeakComposition_modify___redArg(x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_WeakComposition_modify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_PsiIntegrals_WeakComposition_modify(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_lp_PsiIntegrals_Multiset_sum___at___00Finset_sum___at___00imbalance_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_add___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_Multiset_sum___at___00Finset_sum___at___00imbalance_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lp_PsiIntegrals_Multiset_sum___at___00Finset_sum___at___00imbalance_spec__0_spec__0___closed__0;
x_3 = lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___closed__0;
x_4 = l_List_foldrTR___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_Finset_sum___at___00imbalance_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_mathlib_Multiset_map___redArg(x_2, x_1);
x_4 = lp_PsiIntegrals_Multiset_sum___at___00Finset_sum___at___00imbalance_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_Finset_sum___at___00imbalance_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_PsiIntegrals_Finset_sum___at___00imbalance_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_imbalance___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Int_pow(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_imbalance(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(lp_PsiIntegrals_imbalance___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_finRange(x_1);
x_5 = lp_PsiIntegrals_Finset_sum___at___00imbalance_spec__0___redArg(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_PsiIntegrals_nonzeroCount___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___closed__0;
x_5 = lean_int_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_nonzeroCount___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_PsiIntegrals_nonzeroCount___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_PsiIntegrals_nonzeroCount(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(lp_PsiIntegrals_nonzeroCount___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_finRange(x_1);
x_5 = lp_mathlib_Multiset_filter___redArg(x_3, x_4);
x_6 = l_List_lengthTR___redArg(x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fin_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fin_Tuple_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Fin(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_GroupTheory_Perm_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Rat_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PsiIntegrals_PsiIntegrals_Definitions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fin_Tuple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_GroupTheory_Perm_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Rat_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___closed__0 = _init_lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___closed__0();
lean_mark_persistent(lp_PsiIntegrals_WeakComposition_concentrated___redArg___lam__0___closed__0);
lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0___closed__0 = _init_lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0___closed__0();
lean_mark_persistent(lp_PsiIntegrals_WeakComposition_modify___redArg___lam__0___closed__0);
lp_PsiIntegrals_Multiset_sum___at___00Finset_sum___at___00imbalance_spec__0_spec__0___closed__0 = _init_lp_PsiIntegrals_Multiset_sum___at___00Finset_sum___at___00imbalance_spec__0_spec__0___closed__0();
lean_mark_persistent(lp_PsiIntegrals_Multiset_sum___at___00Finset_sum___at___00imbalance_spec__0_spec__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
