#include <z3.h>
#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>


int main(int argc, char *argv[]) {
    int opt;
    int verbose = 0;
    char *filename = NULL;

    while ((opt = getopt(argc, argv, "v")) != -1) {
        switch (opt) {
            case 'v':
                verbose = 1;
                break;
            default:
                fprintf(stderr, "Usage: %s [-v] <filename>\n", argv[0]);
                exit(EXIT_FAILURE);
        }
    }

    if (optind < argc) {
        filename = argv[optind];
    } else {
        fprintf(stderr, "Usage: %s [-v] <filename>\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    if (verbose) {
        printf("Verbose mode enabled.\n");
        printf("Processing file: %s\n", filename);
    }
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_error_code error_code = Z3_get_error_code(ctx);
    if(error_code != Z3_OK) {
        fprintf(stderr, "Error creating Z3 context: %s\n", Z3_get_error_msg(ctx, error_code));
        exit(EXIT_FAILURE);
    }
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort dom[] = {int_sort, bool_sort};
    Z3_func_decl prove0 = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "prove0"), 2, dom, bool_sort);
    Z3_ast_vector asserts = Z3_parse_smtlib2_file(ctx, filename, 0, NULL, NULL, 0, NULL, NULL);
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, asserts); i++) {
        Z3_ast ast = Z3_ast_vector_get(ctx, asserts, i);
        Z3_inc_ref(ctx, ast);
        if (verbose) {
            printf("Processing assertion %u: %s\n", i, Z3_ast_to_string(ctx, ast));
        }
        Z3_app app = Z3_to_app(ctx, ast);
        Z3_func_decl decl = Z3_get_app_decl(ctx, app);
        if (Z3_is_eq_func_decl(ctx, decl, prove0)) {
            if (verbose) {
                printf("Prove0 assertion found: %s\n", Z3_ast_to_string(ctx, ast));
            }
            Z3_solver solver = Z3_mk_solver(ctx);
            Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, Z3_get_app_arg(ctx, app, 1)));
            Z3_lbool res = Z3_solver_check(ctx, solver);
            if (res == Z3_L_TRUE) {
                if (verbose) {
                    printf("The assertion is satisfiable.\n");
                }
                Z3_model model = Z3_solver_get_model(ctx, solver);
                if (verbose) {
                    printf("Model:\n%s\n", Z3_model_to_string(ctx, model));
                }
                exit(EXIT_FAILURE);
            } else if (res == Z3_L_UNDEF) {
                    printf("The result is unknown.\n");
                    exit(EXIT_FAILURE);
            }
        } else {
            if (verbose) {
                printf("Unknown assertion type: %s\n", Z3_ast_to_string(ctx, ast));
            }
        }


        

    }


    return 0;

}