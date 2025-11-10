#include "z3.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int myadd(int a, int b) { return a + b; }

const char *hello = "hello from fast.c";
const char *z3_version() {
  puts(Z3_get_full_version());
  char *test = (char *)malloc(sizeof(char) * 10);
  if (!test)
    return NULL;
  test[0] = 'h';
  test[1] = 'e';
  test[2] = 'l';
  test[3] = 'l';
  test[4] = 'o';
  test[5] = '\0';
  strncpy(test, Z3_get_full_version(), 9);
  return test; //
               // return "hello"; // Z3_get_full_version();//hello;
}

Z3_ast my_mk_true(Z3_context ctx) { return Z3_mk_true(ctx); }

Z3_ast my_mk_and(Z3_context ctx, Z3_ast a, Z3_ast b) {
  Z3_ast args[2] = {a, b};
  return Z3_mk_and(ctx, 2, args);
}

// https://stackoverflow.com/questions/27200320/maintenance-of-reference-counting-in-z3
// https://github.com/Z3Prover/z3/blob/master/examples/c/test_capi.c
Z3_ast_vector KDRAG_get_consts(Z3_context ctx, Z3_ast t) {
  Z3_ast_vector res = Z3_mk_ast_vector(ctx);
  Z3_ast_vector_inc_ref(ctx, res);
  Z3_ast_vector todo = Z3_mk_ast_vector(ctx);
  Z3_ast_vector_inc_ref(ctx, todo);
  // todo: seen set
  // Z3_ast_map seen = Z3_mk_ast_map(ctx);
  // Z3_ast_map_inc_ref(ctx, seen);

  Z3_ast_vector_push(ctx, todo, t);
  Z3_inc_ref(ctx, t);
  unsigned visited = 0;
  while (visited < Z3_ast_vector_size(ctx, todo)) {
    Z3_ast current = Z3_ast_vector_get(ctx, todo, visited);
    if (Z3_is_app(ctx, current)) {
      Z3_app app = Z3_to_app(ctx, current);
      unsigned num_args = Z3_get_app_num_args(ctx, app);
      if (num_args == 0) {  // possible constant
        bool found = false; // already in res?
        for (unsigned i = 0; i < Z3_ast_vector_size(ctx, res); i++) {
          Z3_ast existing = Z3_ast_vector_get(ctx, res, i);
          if (existing == current) {
            found = true;
            break;
          }
        }
        if (!found) {
          Z3_inc_ref(ctx, current);
          Z3_ast_vector_push(ctx, res, current);
        }
      } else { // push args to todo
        for (unsigned j = 0; j < num_args; j++) {
          Z3_ast arg = Z3_get_app_arg(ctx, app, j);
          Z3_inc_ref(ctx, arg);
          Z3_ast_vector_push(ctx, todo, arg);
        }
      }
    }
    Z3_dec_ref(ctx, current);
    visited++;
  }
  Z3_ast_vector_dec_ref(ctx, todo);
  return res;
}