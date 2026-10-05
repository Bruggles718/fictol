#include <llvm-c/Core.h>
#include <caml/mlvalues.h>

extern void *from_val(value v);   /* defined in the LLVM OCaml bindings' C library */

CAMLprim value fictol_llvm_set_musttail(value call_inst) {
  LLVMSetTailCallKind((LLVMValueRef)from_val(call_inst), LLVMTailCallKindMustTail);
  return Val_unit;
}