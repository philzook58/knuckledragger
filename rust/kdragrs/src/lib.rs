use pyo3::prelude::*;

#[pyfunction]
fn full_version() -> String {
    z3::full_version().to_string()
}

fn z3_from_py(z3_expr: Bound<PyAny>) -> PyResult<z3::ast::Dynamic> {
    let s: String = z3_expr.call_method0("serialize")?.extract()?;
    kdrag::deserialize(&s).ok_or_else(|| {
        pyo3::exceptions::PyValueError::new_err("Failed to deserialize the given string")
    })
}

fn z3_to_py<'py>(py: Python<'py>, ast: &z3::ast::Dynamic) -> PyResult<Bound<'py, PyAny>> {
    let z3_mod = PyModule::import(py, "z3")?;
    z3_mod.call_method1("deserialize", (kdrag::serialize(ast),))
}
// Alternative: translate between contexts. Fishy between z3 versions.
// https://github.com/toolCHAINZ/jingle/blob/main/jingle/src/python/z3/ast.rs
#[pyfunction]
fn my_id<'py>(py: Python<'py>, z3_expr: Bound<'py, PyAny>) -> PyResult<Bound<'py, PyAny>> {
    let ast = z3_from_py(z3_expr)?;
    z3_to_py(py, &ast)
}

/// A Python module implemented in Rust.
#[pymodule]
fn kdragrs(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(full_version, m)?)?;
    m.add_function(wrap_pyfunction!(my_id, m)?)?;
    Ok(())
}
