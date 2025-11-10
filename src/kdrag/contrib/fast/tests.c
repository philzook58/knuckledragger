#include "fast.h"
#include "z3.h"
#include <assert.h>
int main() {
  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = Z3_mk_context_rc(cfg);
  Z3_sort sort = Z3_mk_bool_sort(ctx);
  Z3_symbol sym = Z3_mk_string_symbol(ctx, "x");

  {
    Z3_ast t = Z3_mk_const(ctx, sym, sort);
    Z3_inc_ref(ctx, t);

    {
      Z3_ast_vector vec = KDRAG_get_consts(ctx, t);
      unsigned size = Z3_ast_vector_size(ctx, vec);
      assert(size == 1 && "there should be one constant");
      for (unsigned i = 0; i < size; i++) {
        Z3_ast ast = Z3_ast_vector_get(ctx, vec, i);
        Z3_dec_ref(ctx, ast);
      }
      Z3_ast_vector_dec_ref(ctx, vec);
    }

    {
      Z3_ast args[] = {t, t};
      Z3_ast myand = Z3_mk_and(ctx, 2, args);
      // Z3_inc_ref(ctx, myand);
      Z3_ast_vector vec = KDRAG_get_consts(ctx, myand);
      unsigned size = Z3_ast_vector_size(ctx, vec);
      assert(size == 2 && "there should be two constants");
      for (unsigned i = 0; i < size; i++) {
        Z3_ast ast = Z3_ast_vector_get(ctx, vec, i);
        assert(ast == t && "the constant should be t");
        Z3_dec_ref(ctx, ast);
      }
      Z3_dec_ref(ctx, myand);
      Z3_ast_vector_dec_ref(ctx, vec);
    }

    Z3_dec_ref(ctx, t);
  }
  Z3_del_context(ctx);
  Z3_del_config(cfg);

  return 0;
}