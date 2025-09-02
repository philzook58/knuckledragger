use std::ffi::CString;
use z3;
use z3::ast::Ast;
use z3_sys;

pub fn deserialize(sexp0: &str) -> Option<z3::ast::Dynamic> {
    let ctx = z3::Context::thread_local();
    let raw_ctx = ctx.get_z3_context();
    let sexp = CString::new(sexp0).ok()?;
    let z3_vec = unsafe {
        z3_sys::Z3_parse_smtlib2_string(
            raw_ctx,
            sexp.as_ptr(),
            0,
            std::ptr::null(),
            std::ptr::null(),
            0,
            std::ptr::null(),
            std::ptr::null(),
        )
    };
    let len = unsafe { z3_sys::Z3_ast_vector_size(raw_ctx, z3_vec) };
    if len != 1 {
        return None;
    }
    let z3_ast = unsafe { z3_sys::Z3_ast_vector_get(raw_ctx, z3_vec, 0) };
    let ast = unsafe { z3::ast::Dynamic::wrap(&ctx, z3_ast) };
    let ast = ast.nth_child(0)?;
    // Do I need to delete z3_vec?
    Some(ast)
}

pub fn serialize(ast: &z3::ast::Dynamic) -> String {
    let f = z3::FuncDecl::new("F", &[&ast.get_sort()], &z3::Sort::bool());
    let s = z3::Solver::new();
    s.assert(f.apply(&[ast]).as_bool().unwrap());
    s.to_smt2()
}

fn decl_eq(d1: &z3::FuncDecl, d2: &z3::FuncDecl) -> bool {
    d1.kind() == d2.kind() && d1.name() == d2.name() && d1.arity() == d2.arity()
}

/*
Many precompilations to pmatch are possible.
We could precompile all the rules into one bit matcher
Or other things.
*/
pub fn pmatch(
    vs: &[&z3::ast::Dynamic],
    pattern: &z3::ast::Dynamic,
    term: &z3::ast::Dynamic,
    subst: &mut Vec<Option<z3::ast::Dynamic>>,
) -> bool {
    subst.resize(vs.len(), None);
    let mut todo = vec![(pattern.clone(), term.clone())];
    while let Some((p, t)) = todo.pop() {
        //if p.eq(&t) {
        //    Well, strictly speaking wrong.
        //    continue;
        //}
        if let Some(i) = vs.iter().position(|v| v.eq(&&p)) {
            if let Some(old) = &subst[i] {
                if !old.eq(&t) {
                    // Conflict
                    subst.clear();
                    return false;
                }
            } else {
                subst[i] = Some(t);
            }
        } else if p.is_app() && t.is_app() {
            let pc = p.num_children();
            if pc != t.num_children() || !decl_eq(&p.decl(), &t.decl()) {
                // Mismatch
                subst.clear();
                return false;
            }
            for i in 0..pc {
                let pc = p.nth_child(i).unwrap();
                let tc = t.nth_child(i).unwrap();
                todo.push((pc, tc));
            }
        } else {
            return false;
        }
    }
    return true;
}

pub fn rewrite1(
    vs: &[&z3::ast::Dynamic],
    lhs: &z3::ast::Dynamic,
    rhs: &z3::ast::Dynamic,
    term: &z3::ast::Dynamic,
) -> Option<z3::ast::Dynamic> {
    let mut subst = Vec::with_capacity(vs.len());
    if !pmatch(vs, lhs, term, &mut subst) {
        return None;
    }
    let subst: Vec<z3::ast::Dynamic> = subst.into_iter().collect::<Option<_>>()?;
    let pairs: Vec<(&z3::ast::Dynamic, &z3::ast::Dynamic)> =
        vs.iter().copied().zip(subst.iter()).collect();
    Some(rhs.substitute(&pairs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::ast::Ast;
    #[test]
    fn test_pmatch() {
        let x: z3::ast::Dynamic = z3::ast::Int::new_const("x").into();
        let y = z3::ast::Int::new_const("y").into();
        let mut subst = vec![];
        assert!(pmatch(&[&x], &x, &y, &mut subst));
        assert!(subst.len() == 1);
        let p1: z3::ast::Dynamic = subst[0].clone().unwrap();
        assert!(p1.eq(&y));
        subst.clear();
        assert!(!pmatch(&[], &x, &y, &mut subst));
        let f = z3::FuncDecl::new("f", &[&x.get_sort()], &x.get_sort());
        subst.clear();
        assert!(pmatch(
            &[&x],
            &f.apply(&[&x]).into(),
            &f.apply(&[&y]).into(),
            &mut subst
        ));
        assert!(subst.len() == 1);
        assert!(subst[0].clone().unwrap().eq(&y));
    }

    #[test]
    fn test_rewrite() {
        let x: z3::ast::Dynamic = z3::ast::Int::new_const("x").into();
        let y = z3::ast::Int::new_const("y").into();
        let z = z3::ast::Int::new_const("z").into();
        let f = z3::FuncDecl::new("f", &[&x.get_sort()], &x.get_sort());
        assert!(rewrite1(&[&x], &x, &y, &z).unwrap().eq(&y));
        assert!(rewrite1(&[&x], &x, &x, &z).unwrap().eq(&z));
        assert!(
            rewrite1(&[&x], &f.apply(&[&x]).into(), &x, &f.apply(&[&z]).into())
                .unwrap()
                .eq(&z)
        );
        assert!(rewrite1(&[&x], &f.apply(&[&y]).into(), &z, &f.apply(&[&z]).into()).is_none());
    }
}
