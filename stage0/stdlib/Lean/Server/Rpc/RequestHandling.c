// Lean compiler output
// Module: Lean.Server.Rpc.RequestHandling
// Imports: Init Lean.Data.Lsp.Extra Lean.Server.Requests Lean.Server.Rpc.Basic
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
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__7;
lean_object* l_Lean_initializing(lean_object*);
lean_object* l_Lean_throwError___at_Lean_KeyedDeclsAttribute_ExtensionState_erase___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__2___boxed(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__2;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__7;
static lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
static lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___closed__2;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___closed__1;
lean_object* l_Lean_throwError___at_Lean_declareBuiltin___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__15;
static lean_object* l_Lean_Server_registerBuiltinRpcProcedure___closed__1;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__24;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__22;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__18;
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerBuiltinRpcProcedure___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348_(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__3;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__18;
static lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__1;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__19;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__5;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__1;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__15;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__5;
lean_object* l_Lean_setEnv___at_Lean_Meta_unfoldDeclsFrom___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__1;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__14;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Server_registerRpcProcedure___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__15;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__3;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__8;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__1;
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Server_registerRpcProcedure___spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__11;
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerBuiltinRpcProcedure___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_builtinRpcProcedures;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__5;
static lean_object* l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_compileDecl___at_Lean_Server_registerRpcProcedure___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Server_registerRpcProcedure___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__14;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__12;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__14;
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__2;
static lean_object* l_Lean_Server_registerBuiltinRpcProcedure___closed__2;
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__1;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__26;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__9;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Server_registerRpcProcedure___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__25;
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_101_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Server_registerBuiltinRpcProcedure___spec__5___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__12;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__10;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__13;
static lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__4(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__2;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__20;
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__10;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__6;
lean_object* l_Except_map___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Server_registerRpcProcedure___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__2;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Server_userRpcProcedures;
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__23;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_registerRpcProcedure___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile___at_Lean_Server_registerRpcProcedure___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__2;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Server_registerBuiltinRpcProcedure___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__2;
static lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__3;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___closed__2;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__17;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Server_registerLspRequestHandler___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__4;
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__1;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_handleRpcCall___lambda__2___closed__1;
static lean_object* l_Lean_Server_registerRpcProcedure___closed__4;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__1;
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
extern lean_object* l_Lean_Server_requestHandlers;
extern lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__17;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__24;
lean_object* l_Lean_Server_RequestM_bindTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__8;
uint8_t l_Array_contains___at_Lean_findField_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__1(lean_object*);
static lean_object* l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__2;
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
static lean_object* l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__1;
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___closed__1;
lean_object* l_Lean_Server_RequestM_mapTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__12;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__16;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Server_registerRpcProcedure___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__4;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__9;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerBuiltinRpcProcedure___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_handleRpcCall___closed__2;
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2___closed__1;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__9;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__8;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__7;
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__4___closed__3;
extern lean_object* l_Lean_warningAsError;
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__16;
static lean_object* l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__11;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__19;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__7;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Server_handleRpcCall___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__6(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerBuiltinRpcProcedure___closed__3;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__22;
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__2;
static lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__2;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__14;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__26;
lean_object* l_Prod_map___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__15;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__18;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure(uint64_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__11;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__5;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__11;
lean_object* l_Lean_quoteNameMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Server_registerRpcProcedure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2(lean_object*, size_t, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__12;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1(lean_object*, uint64_t);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_registerBuiltinRpcProcedure___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Server_handleRpcCall___closed__1;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__6;
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__23;
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__25;
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure___rarg(lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__6;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__1;
static lean_object* l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7___closed__1;
static lean_object* l_Lean_Server_handleRpcCall___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__1;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__13;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_Expr_instBEqExpr;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_handleRpcCall___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Server_handleRpcCall___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___closed__3;
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Server_registerRpcProcedure___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__21;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__10;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__13;
lean_object* l_Lean_Server_RequestM_asTask___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_handleRpcCall___closed__3;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__10;
lean_object* l_Lean_Environment_compileDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__2;
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__8;
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__6;
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Server_registerRpcProcedure___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(lean_object*, uint8_t);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__20;
lean_object* lean_usize_to_nat(size_t);
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__2;
static lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcCallParams____x40_Lean_Data_Lsp_Extra___hyg_1153_(lean_object*);
static lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___closed__1;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
extern lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__9;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__1___closed__16;
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Server_handleRpcCall___spec__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___closed__17;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcProcedure___lambda__4___closed__1;
static lean_object* _init_l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_instInhabitedRpcProcedure___rarg), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRpcProcedure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Lean_Server_instInhabitedRpcProcedure(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__3;
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("userRpcProcedures", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_instInhabitedName;
x_3 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__2;
x_4 = l_Lean_mkMapDeclarationExtension___rarg(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__2;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Server", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__4;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Rpc", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__6;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("RequestHandling", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__8;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__10;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__11;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__12;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("RpcProcedure", 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__13;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__15;
x_5 = l_Lean_Environment_evalConstCheck___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Server_handleRpcCall___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Server_handleRpcCall___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Server_handleRpcCall___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_handleRpcCall___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_userRpcProcedures;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_handleRpcCall___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Server_Snapshots_Snapshot_endPos(x_3);
x_5 = lean_nat_dec_le(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Server_Snapshots_Snapshot_env(x_3);
x_7 = l_Lean_instInhabitedName;
x_8 = l_Lean_Server_handleRpcCall___lambda__2___closed__1;
x_9 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_7, x_8, x_6, x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = 1;
return x_12;
}
}
}
static lean_object* _init_l_Lean_Server_handleRpcCall___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Failed to evaluate RPC constant '", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_handleRpcCall___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("': ", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Server_Snapshots_Snapshot_env(x_4);
x_8 = l_Lean_instInhabitedName;
x_9 = l_Lean_Server_handleRpcCall___lambda__2___closed__1;
lean_inc(x_7);
x_10 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_8, x_9, x_7, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_13, 2);
x_15 = l_Lean_Elab_Command_instInhabitedScope;
x_16 = l_List_head_x21___rarg(x_15, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_12);
x_18 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(x_7, x_17, x_12);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = l_Lean_Name_toString(x_12, x_20);
x_22 = l_Lean_Server_handleRpcCall___lambda__3___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_Server_handleRpcCall___lambda__3___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_19);
lean_dec(x_19);
x_27 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = 4;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_12);
x_32 = lean_ctor_get(x_18, 0);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_34 = lean_ctor_get(x_3, 2);
lean_inc(x_34);
lean_dec(x_3);
x_35 = lean_box_uint64(x_33);
x_36 = lean_apply_4(x_32, x_35, x_34, x_5, x_6);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Server_handleRpcCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_builtinRpcProcedures;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_handleRpcCall___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("No RPC method '", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_handleRpcCall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' found", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Server_handleRpcCall___closed__1;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Std_PersistentHashMap_find_x3f___at_Lean_Server_handleRpcCall___spec__1(x_6, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_10 = l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1(x_2, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_FileMap_lspPosToUtf8Pos(x_14, x_16);
lean_dec(x_14);
x_18 = 1;
lean_inc(x_8);
x_19 = l_Lean_Name_toString(x_8, x_18);
x_20 = l_Lean_Server_handleRpcCall___closed__2;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_Server_handleRpcCall___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = 2;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lambda__1___boxed), 3, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_8);
x_27 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lambda__2___boxed), 3, 2);
lean_closure_set(x_27, 0, x_17);
lean_closure_set(x_27, 1, x_8);
x_28 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall___lambda__3___boxed), 6, 3);
lean_closure_set(x_28, 0, x_8);
lean_closure_set(x_28, 1, x_25);
lean_closure_set(x_28, 2, x_1);
x_29 = l_Lean_Server_RequestM_bindWaitFindSnap___rarg(x_11, x_27, x_26, x_28, x_2, x_12);
return x_29;
}
else
{
lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_box_uint64(x_31);
x_34 = lean_apply_4(x_30, x_33, x_32, x_2, x_7);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Server_handleRpcCall___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Server_handleRpcCall___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_handleRpcCall___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Server_handleRpcCall___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleRpcCall___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_handleRpcCall___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Cannot parse request params: ", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcCallParams____x40_Lean_Data_Lsp_Extra___hyg_1153_(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_4);
lean_dec(x_4);
x_11 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Json_compress(x_1);
x_17 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_15);
lean_dec(x_15);
x_22 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__1;
x_2 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2(x_2);
x_6 = l_liftExcept___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__3(x_5, x_3, x_4);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_3(x_1, x_7, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__2;
x_13 = l_Task_Priority_default;
x_14 = lean_task_map(x_12, x_11, x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__2;
x_18 = l_Task_Priority_default;
x_19 = lean_task_map(x_17, x_15, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_requestHandlers;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__1;
x_7 = lean_st_ref_take(x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
x_12 = l_Std_PersistentHashMap_insert___at_Lean_Server_registerLspRequestHandler___spec__2(x_8, x_2, x_11);
x_13 = lean_st_ref_set(x_6, x_12, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Failed to register LSP request handler for '", 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("': already registered", 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_5 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__1;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_2);
x_10 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_8, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_6);
x_11 = lean_box(0);
x_12 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3(x_1, x_2, x_11, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_13 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__1;
x_14 = lean_string_append(x_13, x_2);
lean_dec(x_2);
x_15 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
lean_inc(x_2);
x_20 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_18, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3(x_1, x_2, x_21, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_23 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__1;
x_24 = lean_string_append(x_23, x_2);
lean_dec(x_2);
x_25 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("': only possible during initialization", 38);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_initializing(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__1;
x_10 = lean_string_append(x_9, x_1);
lean_dec(x_1);
x_11 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__1;
x_16 = lean_string_append(x_15, x_1);
lean_dec(x_1);
x_17 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4(x_2, x_1, x_22, x_21);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/rpc/call", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_handleRpcCall), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__1;
x_3 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__2;
x_4 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1(lean_object* x_1, uint64_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unbox_uint64(x_5);
x_9 = lean_uint64_dec_lt(x_2, x_8);
if (x_9 == 0)
{
uint64_t x_10; uint8_t x_11; 
lean_dec(x_4);
x_10 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_11 = lean_uint64_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_dec(x_6);
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__2___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Cannot decode params in RPC call '", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")'\n", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_2);
x_9 = lean_apply_2(x_7, x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = l_Lean_Name_toString(x_3, x_11);
x_13 = l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_Json_compress(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__3;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_10);
lean_dec(x_10);
x_22 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_3(x_1, x_7, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_st_ref_take(x_1, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__4), 2, 1);
lean_closure_set(x_12, 0, x_10);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_apply_2(x_13, x_8, x_14);
x_16 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__1;
x_17 = l_Prod_map___rarg(x_16, x_12, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_set(x_1, x_19, x_11);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Server_wrapRpcProcedure___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Outdated RPC session", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_wrapRpcProcedure___elambda__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 9;
x_2 = l_Lean_Server_wrapRpcProcedure___elambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint64_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = l_Std_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1(x_11, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = l_Lean_Server_wrapRpcProcedure___elambda__1___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__1___boxed), 3, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___boxed), 6, 3);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_8);
lean_closure_set(x_17, 2, x_1);
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__2___rarg), 4, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_9);
x_19 = l_Lean_Server_RequestM_asTask___rarg(x_18, x_9, x_10);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__3), 4, 1);
lean_closure_set(x_22, 0, x_6);
lean_inc(x_9);
x_23 = l_Lean_Server_RequestM_bindTask___rarg(x_20, x_22, x_9, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__5___boxed), 5, 2);
lean_closure_set(x_26, 0, x_15);
lean_closure_set(x_26, 1, x_5);
x_27 = l_Lean_Server_RequestM_mapTask___rarg(x_24, x_26, x_9, x_25);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___elambda__1___boxed), 10, 6);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, lean_box(0));
lean_closure_set(x_7, 3, x_4);
lean_closure_set(x_7, 4, x_5);
lean_closure_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Std_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_wrapRpcProcedure___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint64_t x_11; lean_object* x_12; 
x_11 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_12 = l_Lean_Server_wrapRpcProcedure___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerBuiltinRpcProcedure___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash___override(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2___closed__1;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerBuiltinRpcProcedure___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2___closed__1;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerBuiltinRpcProcedure___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Server_registerBuiltinRpcProcedure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Name_hash___override(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_usize_shift_right(x_2, x_5);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__7(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_registerBuiltinRpcProcedure___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__6(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Server_wrapRpcProcedure___elambda__1___boxed), 10, 6);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, lean_box(0));
lean_closure_set(x_7, 3, x_2);
lean_closure_set(x_7, 4, x_3);
lean_closure_set(x_7, 5, x_4);
x_8 = l_Lean_Server_handleRpcCall___closed__1;
x_9 = lean_st_ref_take(x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Std_PersistentHashMap_insert___at_Lean_Server_registerBuiltinRpcProcedure___spec__1(x_10, x_1, x_7);
x_13 = lean_st_ref_set(x_8, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Server_registerBuiltinRpcProcedure___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": already registered", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
x_8 = l_Lean_Server_handleRpcCall___closed__1;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_1);
x_13 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerBuiltinRpcProcedure___spec__5(x_11, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_9);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = l_Lean_Server_registerBuiltinRpcProcedure___lambda__1(x_1, x_2, x_3, x_4, x_14, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_17 = lean_string_append(x_16, x_5);
lean_dec(x_5);
x_18 = l_Lean_Server_registerBuiltinRpcProcedure___lambda__2___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
lean_inc(x_1);
x_23 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerBuiltinRpcProcedure___spec__5(x_21, x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = l_Lean_Server_registerBuiltinRpcProcedure___lambda__1(x_1, x_2, x_3, x_4, x_24, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_27 = lean_string_append(x_26, x_5);
lean_dec(x_5);
x_28 = l_Lean_Server_registerBuiltinRpcProcedure___lambda__2___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerBuiltinRpcProcedure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Failed to register builtin RPC call handler for '", 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerBuiltinRpcProcedure___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerBuiltinRpcProcedure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": only possible during initialization", 37);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = 1;
lean_inc(x_1);
x_9 = l_Lean_Name_toString(x_1, x_8);
x_10 = l_Lean_Server_registerBuiltinRpcProcedure___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_Server_registerBuiltinRpcProcedure___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_io_initializing(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_20 = lean_string_append(x_19, x_13);
lean_dec(x_13);
x_21 = l_Lean_Server_registerBuiltinRpcProcedure___closed__3;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_26 = lean_string_append(x_25, x_13);
lean_dec(x_13);
x_27 = l_Lean_Server_registerBuiltinRpcProcedure___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_box(0);
x_33 = l_Lean_Server_registerBuiltinRpcProcedure___lambda__2(x_1, x_4, x_5, x_6, x_13, x_32, x_31);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerBuiltinRpcProcedure___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_registerBuiltinRpcProcedure___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__6(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Server_registerBuiltinRpcProcedure___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerBuiltinRpcProcedure___spec__5(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerBuiltinRpcProcedure___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_registerBuiltinRpcProcedure___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Server_registerRpcProcedure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorryImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Server_registerRpcProcedure___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_KernelException_toMessageData(x_1, x_5);
x_7 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_6, x_2, x_3, x_4);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_265; uint8_t x_266; 
x_265 = 2;
x_266 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_101_(x_3, x_265);
if (x_266 == 0)
{
lean_object* x_267; 
x_267 = lean_box(0);
x_7 = x_267;
goto block_264;
}
else
{
uint8_t x_268; 
lean_inc(x_2);
x_268 = l_Lean_MessageData_hasSyntheticSorry(x_2);
if (x_268 == 0)
{
lean_object* x_269; 
x_269 = lean_box(0);
x_7 = x_269;
goto block_264;
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_2);
x_270 = lean_box(0);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_6);
return x_271;
}
}
block_264:
{
uint8_t x_8; lean_object* x_258; uint8_t x_259; uint8_t x_260; 
lean_dec(x_7);
x_258 = lean_ctor_get(x_4, 2);
x_259 = 1;
x_260 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_101_(x_3, x_259);
if (x_260 == 0)
{
x_8 = x_3;
goto block_257;
}
else
{
lean_object* x_261; uint8_t x_262; 
x_261 = l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7___closed__1;
x_262 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_258, x_261);
if (x_262 == 0)
{
x_8 = x_3;
goto block_257;
}
else
{
uint8_t x_263; 
x_263 = 2;
x_8 = x_263;
goto block_257;
}
}
block_257:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_4, 5);
x_12 = lean_ctor_get(x_4, 6);
x_13 = lean_ctor_get(x_4, 7);
x_14 = l_Lean_replaceRef(x_1, x_11);
x_15 = 0;
x_16 = l_Lean_Syntax_getPos_x3f(x_14, x_15);
x_17 = l_Lean_Syntax_getTailPos_x3f(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_18 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_FileMap_toPosition(x_10, x_21);
lean_inc(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_13);
lean_inc(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_13);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
x_26 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
lean_inc(x_9);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_8);
x_28 = lean_st_ref_take(x_5, x_20);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_29, 5);
x_33 = l_Std_PersistentArray_push___rarg(x_32, x_27);
lean_ctor_set(x_29, 5, x_33);
x_34 = lean_st_ref_set(x_5, x_29, x_30);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_29, 0);
x_42 = lean_ctor_get(x_29, 1);
x_43 = lean_ctor_get(x_29, 2);
x_44 = lean_ctor_get(x_29, 3);
x_45 = lean_ctor_get(x_29, 4);
x_46 = lean_ctor_get(x_29, 5);
x_47 = lean_ctor_get(x_29, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_29);
x_48 = l_Std_PersistentArray_push___rarg(x_46, x_27);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_44);
lean_ctor_set(x_49, 4, x_45);
lean_ctor_set(x_49, 5, x_48);
lean_ctor_set(x_49, 6, x_47);
x_50 = lean_st_ref_set(x_5, x_49, x_30);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_17);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_56 = lean_ctor_get(x_17, 0);
x_57 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Lean_FileMap_toPosition(x_10, x_60);
x_62 = l_Lean_FileMap_toPosition(x_10, x_56);
lean_dec(x_56);
lean_ctor_set(x_17, 0, x_62);
lean_inc(x_13);
lean_inc(x_12);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_12);
lean_ctor_set(x_63, 1, x_13);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
x_65 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
lean_inc(x_9);
x_66 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_66, 0, x_9);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_17);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_66, 4, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*5, x_8);
x_67 = lean_st_ref_take(x_5, x_59);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_68, 5);
x_72 = l_Std_PersistentArray_push___rarg(x_71, x_66);
lean_ctor_set(x_68, 5, x_72);
x_73 = lean_st_ref_set(x_5, x_68, x_69);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_80 = lean_ctor_get(x_68, 0);
x_81 = lean_ctor_get(x_68, 1);
x_82 = lean_ctor_get(x_68, 2);
x_83 = lean_ctor_get(x_68, 3);
x_84 = lean_ctor_get(x_68, 4);
x_85 = lean_ctor_get(x_68, 5);
x_86 = lean_ctor_get(x_68, 6);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_68);
x_87 = l_Std_PersistentArray_push___rarg(x_85, x_66);
x_88 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_82);
lean_ctor_set(x_88, 3, x_83);
lean_ctor_set(x_88, 4, x_84);
lean_ctor_set(x_88, 5, x_87);
lean_ctor_set(x_88, 6, x_86);
x_89 = lean_st_ref_set(x_5, x_88, x_69);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_94 = lean_ctor_get(x_17, 0);
lean_inc(x_94);
lean_dec(x_17);
x_95 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_FileMap_toPosition(x_10, x_98);
x_100 = l_Lean_FileMap_toPosition(x_10, x_94);
lean_dec(x_94);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_inc(x_13);
lean_inc(x_12);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_12);
lean_ctor_set(x_102, 1, x_13);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
x_104 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
lean_inc(x_9);
x_105 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_105, 0, x_9);
lean_ctor_set(x_105, 1, x_99);
lean_ctor_set(x_105, 2, x_101);
lean_ctor_set(x_105, 3, x_104);
lean_ctor_set(x_105, 4, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*5, x_8);
x_106 = lean_st_ref_take(x_5, x_97);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 4);
lean_inc(x_113);
x_114 = lean_ctor_get(x_107, 5);
lean_inc(x_114);
x_115 = lean_ctor_get(x_107, 6);
lean_inc(x_115);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 lean_ctor_release(x_107, 5);
 lean_ctor_release(x_107, 6);
 x_116 = x_107;
} else {
 lean_dec_ref(x_107);
 x_116 = lean_box(0);
}
x_117 = l_Std_PersistentArray_push___rarg(x_114, x_105);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 7, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_109);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_111);
lean_ctor_set(x_118, 3, x_112);
lean_ctor_set(x_118, 4, x_113);
lean_ctor_set(x_118, 5, x_117);
lean_ctor_set(x_118, 6, x_115);
x_119 = lean_st_ref_set(x_5, x_118, x_108);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_16);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_125 = lean_ctor_get(x_16, 0);
x_126 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lean_FileMap_toPosition(x_10, x_125);
lean_dec(x_125);
lean_inc(x_129);
lean_ctor_set(x_16, 0, x_129);
lean_inc(x_13);
lean_inc(x_12);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_12);
lean_ctor_set(x_130, 1, x_13);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_127);
x_132 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
lean_inc(x_9);
x_133 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_133, 0, x_9);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set(x_133, 2, x_16);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set(x_133, 4, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*5, x_8);
x_134 = lean_st_ref_take(x_5, x_128);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_135, 5);
x_139 = l_Std_PersistentArray_push___rarg(x_138, x_133);
lean_ctor_set(x_135, 5, x_139);
x_140 = lean_st_ref_set(x_5, x_135, x_136);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
lean_dec(x_142);
x_143 = lean_box(0);
lean_ctor_set(x_140, 0, x_143);
return x_140;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_box(0);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_147 = lean_ctor_get(x_135, 0);
x_148 = lean_ctor_get(x_135, 1);
x_149 = lean_ctor_get(x_135, 2);
x_150 = lean_ctor_get(x_135, 3);
x_151 = lean_ctor_get(x_135, 4);
x_152 = lean_ctor_get(x_135, 5);
x_153 = lean_ctor_get(x_135, 6);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_135);
x_154 = l_Std_PersistentArray_push___rarg(x_152, x_133);
x_155 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_155, 0, x_147);
lean_ctor_set(x_155, 1, x_148);
lean_ctor_set(x_155, 2, x_149);
lean_ctor_set(x_155, 3, x_150);
lean_ctor_set(x_155, 4, x_151);
lean_ctor_set(x_155, 5, x_154);
lean_ctor_set(x_155, 6, x_153);
x_156 = lean_st_ref_set(x_5, x_155, x_136);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_161 = lean_ctor_get(x_16, 0);
lean_inc(x_161);
lean_dec(x_16);
x_162 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_FileMap_toPosition(x_10, x_161);
lean_dec(x_161);
lean_inc(x_165);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
lean_inc(x_13);
lean_inc(x_12);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_12);
lean_ctor_set(x_167, 1, x_13);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_163);
x_169 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
lean_inc(x_9);
x_170 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_170, 0, x_9);
lean_ctor_set(x_170, 1, x_165);
lean_ctor_set(x_170, 2, x_166);
lean_ctor_set(x_170, 3, x_169);
lean_ctor_set(x_170, 4, x_168);
lean_ctor_set_uint8(x_170, sizeof(void*)*5, x_8);
x_171 = lean_st_ref_take(x_5, x_164);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_172, 4);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 5);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 6);
lean_inc(x_180);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 lean_ctor_release(x_172, 4);
 lean_ctor_release(x_172, 5);
 lean_ctor_release(x_172, 6);
 x_181 = x_172;
} else {
 lean_dec_ref(x_172);
 x_181 = lean_box(0);
}
x_182 = l_Std_PersistentArray_push___rarg(x_179, x_170);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 7, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_175);
lean_ctor_set(x_183, 2, x_176);
lean_ctor_set(x_183, 3, x_177);
lean_ctor_set(x_183, 4, x_178);
lean_ctor_set(x_183, 5, x_182);
lean_ctor_set(x_183, 6, x_180);
x_184 = lean_st_ref_set(x_5, x_183, x_173);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_186 = x_184;
} else {
 lean_dec_ref(x_184);
 x_186 = lean_box(0);
}
x_187 = lean_box(0);
if (lean_is_scalar(x_186)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_186;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_185);
return x_188;
}
}
else
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_16, 0);
lean_inc(x_189);
lean_dec(x_16);
x_190 = !lean_is_exclusive(x_17);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_191 = lean_ctor_get(x_17, 0);
x_192 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = l_Lean_FileMap_toPosition(x_10, x_189);
lean_dec(x_189);
x_196 = l_Lean_FileMap_toPosition(x_10, x_191);
lean_dec(x_191);
lean_ctor_set(x_17, 0, x_196);
lean_inc(x_13);
lean_inc(x_12);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_12);
lean_ctor_set(x_197, 1, x_13);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_193);
x_199 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
lean_inc(x_9);
x_200 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_200, 0, x_9);
lean_ctor_set(x_200, 1, x_195);
lean_ctor_set(x_200, 2, x_17);
lean_ctor_set(x_200, 3, x_199);
lean_ctor_set(x_200, 4, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*5, x_8);
x_201 = lean_st_ref_take(x_5, x_194);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = !lean_is_exclusive(x_202);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = lean_ctor_get(x_202, 5);
x_206 = l_Std_PersistentArray_push___rarg(x_205, x_200);
lean_ctor_set(x_202, 5, x_206);
x_207 = lean_st_ref_set(x_5, x_202, x_203);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_207, 0);
lean_dec(x_209);
x_210 = lean_box(0);
lean_ctor_set(x_207, 0, x_210);
return x_207;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
lean_dec(x_207);
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_214 = lean_ctor_get(x_202, 0);
x_215 = lean_ctor_get(x_202, 1);
x_216 = lean_ctor_get(x_202, 2);
x_217 = lean_ctor_get(x_202, 3);
x_218 = lean_ctor_get(x_202, 4);
x_219 = lean_ctor_get(x_202, 5);
x_220 = lean_ctor_get(x_202, 6);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_202);
x_221 = l_Std_PersistentArray_push___rarg(x_219, x_200);
x_222 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_222, 0, x_214);
lean_ctor_set(x_222, 1, x_215);
lean_ctor_set(x_222, 2, x_216);
lean_ctor_set(x_222, 3, x_217);
lean_ctor_set(x_222, 4, x_218);
lean_ctor_set(x_222, 5, x_221);
lean_ctor_set(x_222, 6, x_220);
x_223 = lean_st_ref_set(x_5, x_222, x_203);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_225 = x_223;
} else {
 lean_dec_ref(x_223);
 x_225 = lean_box(0);
}
x_226 = lean_box(0);
if (lean_is_scalar(x_225)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_225;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_224);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_228 = lean_ctor_get(x_17, 0);
lean_inc(x_228);
lean_dec(x_17);
x_229 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = l_Lean_FileMap_toPosition(x_10, x_189);
lean_dec(x_189);
x_233 = l_Lean_FileMap_toPosition(x_10, x_228);
lean_dec(x_228);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
lean_inc(x_13);
lean_inc(x_12);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_12);
lean_ctor_set(x_235, 1, x_13);
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_230);
x_237 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
lean_inc(x_9);
x_238 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_238, 0, x_9);
lean_ctor_set(x_238, 1, x_232);
lean_ctor_set(x_238, 2, x_234);
lean_ctor_set(x_238, 3, x_237);
lean_ctor_set(x_238, 4, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*5, x_8);
x_239 = lean_st_ref_take(x_5, x_231);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_240, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_240, 3);
lean_inc(x_245);
x_246 = lean_ctor_get(x_240, 4);
lean_inc(x_246);
x_247 = lean_ctor_get(x_240, 5);
lean_inc(x_247);
x_248 = lean_ctor_get(x_240, 6);
lean_inc(x_248);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 lean_ctor_release(x_240, 3);
 lean_ctor_release(x_240, 4);
 lean_ctor_release(x_240, 5);
 lean_ctor_release(x_240, 6);
 x_249 = x_240;
} else {
 lean_dec_ref(x_240);
 x_249 = lean_box(0);
}
x_250 = l_Std_PersistentArray_push___rarg(x_247, x_238);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 7, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_242);
lean_ctor_set(x_251, 1, x_243);
lean_ctor_set(x_251, 2, x_244);
lean_ctor_set(x_251, 3, x_245);
lean_ctor_set(x_251, 4, x_246);
lean_ctor_set(x_251, 5, x_250);
lean_ctor_set(x_251, 6, x_248);
x_252 = lean_st_ref_set(x_5, x_251, x_241);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_254 = x_252;
} else {
 lean_dec_ref(x_252);
 x_254 = lean_box(0);
}
x_255 = lean_box(0);
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_253);
return x_256;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Server_registerRpcProcedure___spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 5);
lean_inc(x_6);
x_7 = l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7(x_6, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Server_registerRpcProcedure___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7___closed__1;
x_7 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_log___at_Lean_Server_registerRpcProcedure___spec__6(x_1, x_8, x_2, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = 2;
x_11 = l_Lean_log___at_Lean_Server_registerRpcProcedure___spec__6(x_1, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_add_decl(x_9, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_throwKernelException___at_Lean_Server_registerRpcProcedure___spec__4(x_11, x_3, x_4, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_setEnv___at_Lean_Meta_unfoldDeclsFrom___spec__1(x_13, x_3, x_4, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
}
static lean_object* _init_l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration uses 'sorry'", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 5);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = 0;
lean_inc(x_1);
x_11 = l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___lambda__1(x_1, x_12, x_2, x_3, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__3;
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_logWarning___at_Lean_Server_registerRpcProcedure___spec__5(x_14, x_2, x_3, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___lambda__1(x_1, x_16, x_2, x_3, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___lambda__1(x_1, x_19, x_2, x_3, x_7);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_is_aux_recursor(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_inc(x_3);
x_5 = l_Lean_isRecCore(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_8 = l_Array_contains___at_Lean_findField_x3f___spec__1(x_7, x_3);
lean_dec(x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
else
{
uint8_t x_11; 
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_isCasesOnRecursor(x_1, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_12 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_13 = l_Array_contains___at_Lean_findField_x3f___spec__1(x_12, x_3);
lean_dec(x_3);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_inc(x_3);
x_16 = l_Lean_isRecCore(x_1, x_3);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = 0;
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_19 = l_Array_contains___at_Lean_findField_x3f___spec__1(x_18, x_3);
lean_dec(x_3);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = 0;
return x_22;
}
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("code generator does not support recursor '", 42);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' yet, consider using 'match ... with' and/or structural recursion", 66);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_1);
x_33 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_33, 0, x_1);
x_34 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_33, x_32);
if (lean_obj_tag(x_34) == 0)
{
x_10 = x_6;
goto block_30;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_41, x_4, x_5, x_6);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_dec(x_35);
x_10 = x_6;
goto block_30;
}
}
block_30:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_12, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
x_2 = x_14;
x_3 = x_9;
x_6 = x_10;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_22, x_4, x_5, x_10);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_16);
x_28 = lean_box(0);
x_2 = x_28;
x_3 = x_9;
x_6 = x_10;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
x_2 = x_13;
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_21, x_4, x_5, x_6);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_15);
x_27 = lean_box(0);
x_2 = x_27;
x_3 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_box(0);
lean_inc(x_1);
x_24 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__12(x_1, x_23, x_22, x_4, x_5, x_6);
x_10 = x_24;
goto block_18;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_31, x_4, x_5, x_6);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
x_10 = x_32;
goto block_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_10 = x_36;
goto block_18;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_25);
x_37 = lean_ctor_get(x_8, 2);
lean_inc(x_37);
lean_dec(x_8);
x_38 = lean_box(0);
lean_inc(x_1);
x_39 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__12(x_1, x_38, x_37, x_4, x_5, x_6);
x_10 = x_39;
goto block_18;
}
}
block_18:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_2 = x_11;
x_3 = x_9;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Server_registerRpcProcedure___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_10, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_20, x_4, x_5, x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_44; lean_object* x_45; 
lean_dec(x_3);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_44 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_44, 0, x_1);
x_45 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_44, x_27);
if (lean_obj_tag(x_45) == 0)
{
x_28 = x_6;
goto block_43;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 4)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_26);
lean_dec(x_1);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_52, x_4, x_5, x_6);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_dec(x_46);
x_28 = x_6;
goto block_43;
}
}
block_43:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_29, 0, x_1);
x_30 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_29, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_39, x_4, x_5, x_28);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_28);
return x_42;
}
}
}
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_78; lean_object* x_79; 
lean_dec(x_3);
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
lean_dec(x_2);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 2);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_1);
x_78 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_78, 0, x_1);
x_79 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_78, x_61);
if (lean_obj_tag(x_79) == 0)
{
x_62 = x_6;
goto block_77;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 4)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_60);
lean_dec(x_1);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_86, x_4, x_5, x_6);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_dec(x_80);
x_62 = x_6;
goto block_77;
}
}
block_77:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_63, 0, x_1);
x_64 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_63, x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
if (lean_obj_tag(x_67) == 4)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_73, x_4, x_5, x_62);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_62);
return x_76;
}
}
}
}
case 3:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_112; lean_object* x_113; 
lean_dec(x_3);
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
lean_dec(x_2);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 2);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_1);
x_112 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_112, 0, x_1);
x_113 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_112, x_95);
if (lean_obj_tag(x_113) == 0)
{
x_96 = x_6;
goto block_111;
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 4)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_94);
lean_dec(x_1);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_120, x_4, x_5, x_6);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_121);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_dec(x_114);
x_96 = x_6;
goto block_111;
}
}
block_111:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed), 2, 1);
lean_closure_set(x_97, 0, x_1);
x_98 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_97, x_94);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
lean_dec(x_98);
if (lean_obj_tag(x_101) == 4)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2;
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_107, x_4, x_5, x_96);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_101);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_96);
return x_110;
}
}
}
}
case 4:
{
lean_object* x_126; 
lean_dec(x_1);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_3);
lean_ctor_set(x_126, 1, x_6);
return x_126;
}
case 5:
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_2, 0);
lean_inc(x_127);
lean_dec(x_2);
x_128 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11(x_1, x_3, x_127, x_4, x_5, x_6);
return x_128;
}
default: 
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_2, 2);
lean_inc(x_129);
lean_dec(x_2);
x_130 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__13(x_1, x_3, x_129, x_4, x_5, x_6);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Server_registerRpcProcedure___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = l_Lean_Declaration_foldExprM___at_Lean_Server_registerRpcProcedure___spec__10(x_8, x_1, x_9, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___at_Lean_Server_registerRpcProcedure___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_Environment_compileDecl(x_8, x_9, x_1);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 11)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l___private_Lean_MonadEnv_0__Lean_checkUnsupported___at_Lean_Server_registerRpcProcedure___spec__9(x_1, x_2, x_3, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_throwError___at_Lean_declareBuiltin___spec__1(x_16, x_2, x_3, x_14);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = l_Lean_throwKernelException___at_Lean_Server_registerRpcProcedure___spec__4(x_11, x_2, x_3, x_7);
lean_dec(x_3);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = l_Lean_setEnv___at_Lean_Meta_unfoldDeclsFrom___spec__1(x_23, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___at_Lean_Server_registerRpcProcedure___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_compileDecl___at_Lean_Server_registerRpcProcedure___spec__8(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__1;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__3;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__5;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wrapRpcProcedure", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__8;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__1;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__12;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__5;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("quotedName", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__5;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__23;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_8);
x_11 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_8, 10);
lean_inc(x_14);
x_15 = lean_st_ref_get(x_9, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_environment_main_module(x_18);
x_20 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__11;
x_21 = l_Lean_addMacroScope(x_19, x_20, x_14);
x_22 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__13;
lean_inc(x_1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
x_24 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__14;
lean_inc(x_1);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__10;
lean_inc(x_12);
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_26);
lean_inc(x_2);
x_29 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_1, x_2);
x_30 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__19;
lean_inc(x_12);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__20;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__18;
lean_inc(x_12);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_33);
lean_inc(x_2);
x_36 = lean_mk_syntax_ident(x_2);
x_37 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__22;
x_38 = lean_array_push(x_37, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_39 = l_Lean_quoteNameMk(x_2);
x_40 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__21;
x_41 = lean_array_push(x_40, x_39);
lean_inc(x_35);
x_42 = lean_array_push(x_41, x_35);
x_43 = lean_array_push(x_42, x_35);
x_44 = lean_array_push(x_43, x_36);
x_45 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__16;
lean_inc(x_12);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_44);
x_47 = lean_array_push(x_38, x_46);
x_48 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__7;
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_3);
x_51 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_Elab_Term_elabTerm(x_49, x_50, x_51, x_51, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_53, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_29);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_61 = lean_ctor_get(x_29, 0);
x_62 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__25;
x_63 = l_String_intercalate(x_62, x_61);
x_64 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__26;
x_65 = lean_string_append(x_64, x_63);
lean_dec(x_63);
x_66 = lean_box(2);
x_67 = l_Lean_Syntax_mkNameLit(x_65, x_66);
x_68 = lean_array_push(x_32, x_67);
x_69 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__24;
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_68);
x_71 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__21;
x_72 = lean_array_push(x_71, x_70);
lean_inc(x_35);
x_73 = lean_array_push(x_72, x_35);
x_74 = lean_array_push(x_73, x_35);
x_75 = lean_array_push(x_74, x_36);
x_76 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__16;
lean_inc(x_12);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_75);
x_78 = lean_array_push(x_38, x_77);
x_79 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__7;
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_12);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_78);
lean_ctor_set(x_29, 0, x_3);
x_81 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_82 = l_Lean_Elab_Term_elabTerm(x_80, x_29, x_81, x_81, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_83, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_82);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
x_90 = lean_ctor_get(x_29, 0);
lean_inc(x_90);
lean_dec(x_29);
x_91 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__25;
x_92 = l_String_intercalate(x_91, x_90);
x_93 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__26;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = lean_box(2);
x_96 = l_Lean_Syntax_mkNameLit(x_94, x_95);
x_97 = lean_array_push(x_32, x_96);
x_98 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__24;
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_97);
x_100 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__21;
x_101 = lean_array_push(x_100, x_99);
lean_inc(x_35);
x_102 = lean_array_push(x_101, x_35);
x_103 = lean_array_push(x_102, x_35);
x_104 = lean_array_push(x_103, x_36);
x_105 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__16;
lean_inc(x_12);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_12);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_104);
x_107 = lean_array_push(x_38, x_106);
x_108 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__7;
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_107);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_3);
x_111 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_112 = l_Lean_Elab_Term_elabTerm(x_109, x_110, x_111, x_111, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_114);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_118 = x_112;
} else {
 lean_dec_ref(x_112);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_registerRpcProcedure___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_rpc_wrapped", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__15;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__5;
x_3 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__4;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = 1;
x_5 = 0;
x_6 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__6;
x_7 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__7;
x_8 = lean_alloc_ctor(0, 8, 8);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*8, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 1, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 2, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 3, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 4, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 5, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 6, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 7, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__10() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_3);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_3);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_3);
lean_ctor_set_uint8(x_5, 12, x_3);
lean_ctor_set_uint8(x_5, 13, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__11;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__10;
x_3 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__12;
x_4 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__13;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__15;
x_3 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__16;
x_4 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__3;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__18;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__20;
x_3 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__21;
x_4 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__24;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__17;
x_3 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__25;
x_4 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__6;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__2;
x_7 = l_Lean_Name_append(x_1, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__3;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcProcedure___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Server_registerRpcProcedure___spec__1), 8, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_st_ref_get(x_4, x_5);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__26;
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__8;
x_19 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__9;
x_20 = l_Lean_Server_registerRpcProcedure___lambda__3___closed__14;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_21 = l_Lean_Elab_Term_TermElabM_run___rarg(x_11, x_18, x_19, x_20, x_16, x_3, x_4, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_4, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_16, x_26);
lean_dec(x_16);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_7);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_8);
lean_ctor_set(x_29, 2, x_9);
lean_inc(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_8);
x_31 = lean_box(0);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Lean_addAndCompile___at_Lean_Server_registerRpcProcedure___spec__2(x_34, x_3, x_4, x_28);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_4, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Server_handleRpcCall___lambda__2___closed__1;
x_42 = l_Lean_MapDeclarationExtension_insert___rarg(x_41, x_40, x_1, x_7);
x_43 = l_Lean_setEnv___at_Lean_Meta_unfoldDeclsFrom___spec__1(x_42, x_3, x_4, x_39);
lean_dec(x_4);
lean_dec(x_3);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 0);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_35);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
return x_21;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_21, 0);
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_21);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Failed to register RPC call handler for '{method}'", 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1;
x_2 = l_Lean_Server_registerRpcProcedure___lambda__4___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__4___closed__2;
x_2 = l_Lean_Server_registerBuiltinRpcProcedure___lambda__2___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__4___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__4___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_3);
x_7 = l_Lean_instInhabitedName;
x_8 = l_Lean_Server_handleRpcCall___lambda__2___closed__1;
lean_inc(x_1);
x_9 = l_Lean_MapDeclarationExtension_contains___rarg(x_7, x_8, x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Server_registerRpcProcedure___lambda__3(x_1, x_10, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_12 = l_Lean_Server_registerRpcProcedure___lambda__4___closed__5;
x_13 = l_Lean_throwError___at_Lean_KeyedDeclsAttribute_ExtensionState_erase___spec__1(x_12, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": already registered (builtin)", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__4___closed__2;
x_2 = l_Lean_Server_registerRpcProcedure___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerRpcProcedure___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerRpcProcedure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerRpcProcedure___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_3, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Server_handleRpcCall___closed__1;
x_12 = lean_st_ref_get(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerBuiltinRpcProcedure___spec__5(x_13, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Server_registerRpcProcedure___lambda__4(x_1, x_8, x_16, x_2, x_3, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_1);
x_18 = l_Lean_Server_registerRpcProcedure___closed__4;
x_19 = l_Lean_throwError___at_Lean_KeyedDeclsAttribute_ExtensionState_erase___spec__1(x_18, x_2, x_3, x_14);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Server_registerRpcProcedure___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwKernelException___at_Lean_Server_registerRpcProcedure___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Server_registerRpcProcedure___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_log___at_Lean_Server_registerRpcProcedure___spec__6(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__13(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Server_registerRpcProcedure___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Declaration_foldExprM___at_Lean_Server_registerRpcProcedure___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_registerRpcProcedure___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerRpcProcedure___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerRpcProcedure___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_registerRpcProcedure(x_1, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attribute cannot be erased", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__2;
x_6 = l_Lean_throwError___at_Lean_AttributeImpl_erase___default___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_registerRpcProcedure___lambda__1___closed__12;
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__2;
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__4;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__5;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__6;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__7;
x_2 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__8;
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__10;
x_2 = lean_unsigned_to_nat(1348u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("serverRpcMethod", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Marks a function as a Lean server RPC method.\n    Shorthand for `registerRpcProcedure`.\n    The function must have type `α → RequestM (RequestTask β)` with\n    `[RpcEncodable α]` and `[RpcEncodable β]`.", 208);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__11;
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__13;
x_3 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__14;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__15;
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__16;
x_3 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__17;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__18;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Requests(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Rpc_RequestHandling(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Requests(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1 = _init_l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__1);
l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__2 = _init_l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_instInhabitedRpcProcedure___rarg___closed__2);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__1 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__1();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__2);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__3 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__3();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32____closed__3);
if (builtin) {res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_32_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_builtinRpcProcedures = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_builtinRpcProcedures);
lean_dec_ref(res);
}l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__1 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__1();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__2 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__2();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74____closed__2);
if (builtin) {res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_74_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_userRpcProcedures = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_userRpcProcedures);
lean_dec_ref(res);
}l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__2 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__2();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__2);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__3 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__3();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__3);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__4 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__4();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__4);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__5 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__5();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__5);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__6 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__6();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__6);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__7 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__7();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__7);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__8 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__8();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__8);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__9 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__9();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__9);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__10 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__10();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__10);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__11 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__11();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__11);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__12 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__12();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__12);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__13 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__13();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__13);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__14 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__14();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__14);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__15 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__15();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__15);
l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__1 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__1();
l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__2 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Server_handleRpcCall___spec__2___closed__2();
l_Lean_Server_handleRpcCall___lambda__2___closed__1 = _init_l_Lean_Server_handleRpcCall___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_handleRpcCall___lambda__2___closed__1);
l_Lean_Server_handleRpcCall___lambda__3___closed__1 = _init_l_Lean_Server_handleRpcCall___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_handleRpcCall___lambda__3___closed__1);
l_Lean_Server_handleRpcCall___lambda__3___closed__2 = _init_l_Lean_Server_handleRpcCall___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Server_handleRpcCall___lambda__3___closed__2);
l_Lean_Server_handleRpcCall___closed__1 = _init_l_Lean_Server_handleRpcCall___closed__1();
lean_mark_persistent(l_Lean_Server_handleRpcCall___closed__1);
l_Lean_Server_handleRpcCall___closed__2 = _init_l_Lean_Server_handleRpcCall___closed__2();
lean_mark_persistent(l_Lean_Server_handleRpcCall___closed__2);
l_Lean_Server_handleRpcCall___closed__3 = _init_l_Lean_Server_handleRpcCall___closed__3();
lean_mark_persistent(l_Lean_Server_handleRpcCall___closed__3);
l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__1 = _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__1();
lean_mark_persistent(l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__1);
l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__2 = _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__2();
lean_mark_persistent(l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__2___closed__2);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__1);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__2 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__2___closed__2);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__1);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__2 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__3___closed__2);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__1);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__2 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___lambda__4___closed__2);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____spec__1___closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__1 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__1();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__2 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__2();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350____closed__2);
res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_350_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__1 = _init_l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__1);
l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__2 = _init_l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__2);
l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__3 = _init_l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Server_wrapRpcProcedure___elambda__1___lambda__2___closed__3);
l_Lean_Server_wrapRpcProcedure___elambda__1___closed__1 = _init_l_Lean_Server_wrapRpcProcedure___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_wrapRpcProcedure___elambda__1___closed__1);
l_Lean_Server_wrapRpcProcedure___elambda__1___closed__2 = _init_l_Lean_Server_wrapRpcProcedure___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_wrapRpcProcedure___elambda__1___closed__2);
l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Server_registerBuiltinRpcProcedure___spec__2___closed__1);
l_Lean_Server_registerBuiltinRpcProcedure___lambda__2___closed__1 = _init_l_Lean_Server_registerBuiltinRpcProcedure___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_registerBuiltinRpcProcedure___lambda__2___closed__1);
l_Lean_Server_registerBuiltinRpcProcedure___closed__1 = _init_l_Lean_Server_registerBuiltinRpcProcedure___closed__1();
lean_mark_persistent(l_Lean_Server_registerBuiltinRpcProcedure___closed__1);
l_Lean_Server_registerBuiltinRpcProcedure___closed__2 = _init_l_Lean_Server_registerBuiltinRpcProcedure___closed__2();
lean_mark_persistent(l_Lean_Server_registerBuiltinRpcProcedure___closed__2);
l_Lean_Server_registerBuiltinRpcProcedure___closed__3 = _init_l_Lean_Server_registerBuiltinRpcProcedure___closed__3();
lean_mark_persistent(l_Lean_Server_registerBuiltinRpcProcedure___closed__3);
l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7___closed__1 = _init_l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_Server_registerRpcProcedure___spec__7___closed__1);
l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__1 = _init_l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__1();
lean_mark_persistent(l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__1);
l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__2 = _init_l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__2();
lean_mark_persistent(l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__2);
l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__3 = _init_l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__3();
lean_mark_persistent(l_Lean_addDecl___at_Lean_Server_registerRpcProcedure___spec__3___closed__3);
l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__1 = _init_l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__1();
lean_mark_persistent(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__1);
l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2 = _init_l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2();
lean_mark_persistent(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__2);
l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__3 = _init_l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__3();
lean_mark_persistent(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__3);
l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4 = _init_l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4();
lean_mark_persistent(l_List_foldlM___at_Lean_Server_registerRpcProcedure___spec__11___closed__4);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__1 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__1);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__2 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__2);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__3 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__3);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__4 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__4);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__5 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__5);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__6 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__6);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__7 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__7);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__8 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__8);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__9 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__9);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__10 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__10);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__11 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__11);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__12 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__12);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__13 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__13);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__14 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__14);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__15 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__15);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__16 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__16);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__17 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__17);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__18 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__18);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__19 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__19);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__20 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__20);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__21 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__21();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__21);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__22 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__22();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__22);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__23 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__23();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__23);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__24 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__24();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__24);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__25 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__25();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__25);
l_Lean_Server_registerRpcProcedure___lambda__1___closed__26 = _init_l_Lean_Server_registerRpcProcedure___lambda__1___closed__26();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__1___closed__26);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__1 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__1);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__2 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__2);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__3 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__3);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__4 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__4);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__5 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__5);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__6 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__6);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__7 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__7);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__8 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__8);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__9 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__9);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__10 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__10);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__11 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__11);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__12 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__12();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__12);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__13 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__13();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__13);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__14 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__14();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__14);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__15 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__15();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__15);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__16 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__16();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__16);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__17 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__17();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__17);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__18 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__18();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__18);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__19 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__19();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__19);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__20 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__20();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__20);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__21 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__21();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__21);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__22 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__22();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__22);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__23 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__23();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__23);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__24 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__24();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__24);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__25 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__25();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__25);
l_Lean_Server_registerRpcProcedure___lambda__3___closed__26 = _init_l_Lean_Server_registerRpcProcedure___lambda__3___closed__26();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__3___closed__26);
l_Lean_Server_registerRpcProcedure___lambda__4___closed__1 = _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__4___closed__1);
l_Lean_Server_registerRpcProcedure___lambda__4___closed__2 = _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__4___closed__2);
l_Lean_Server_registerRpcProcedure___lambda__4___closed__3 = _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__4___closed__3);
l_Lean_Server_registerRpcProcedure___lambda__4___closed__4 = _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__4___closed__4);
l_Lean_Server_registerRpcProcedure___lambda__4___closed__5 = _init_l_Lean_Server_registerRpcProcedure___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___lambda__4___closed__5);
l_Lean_Server_registerRpcProcedure___closed__1 = _init_l_Lean_Server_registerRpcProcedure___closed__1();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___closed__1);
l_Lean_Server_registerRpcProcedure___closed__2 = _init_l_Lean_Server_registerRpcProcedure___closed__2();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___closed__2);
l_Lean_Server_registerRpcProcedure___closed__3 = _init_l_Lean_Server_registerRpcProcedure___closed__3();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___closed__3);
l_Lean_Server_registerRpcProcedure___closed__4 = _init_l_Lean_Server_registerRpcProcedure___closed__4();
lean_mark_persistent(l_Lean_Server_registerRpcProcedure___closed__4);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__1 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__2 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____lambda__2___closed__2);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__1 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__1();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__2 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__2();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__2);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__3 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__3();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__3);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__4 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__4();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__4);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__5 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__5();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__5);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__6 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__6();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__6);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__7 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__7();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__7);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__8 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__8();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__8);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__9 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__9();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__9);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__10 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__10();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__10);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__11 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__11();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__11);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__12 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__12();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__12);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__13 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__13();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__13);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__14 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__14();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__14);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__15 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__15();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__15);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__16 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__16();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__16);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__17 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__17();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__17);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__18 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__18();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348____closed__18);
res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_1348_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
