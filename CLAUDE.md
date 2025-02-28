# Knuckledragger Development Guide

## Commands
- **Test**: `pytest -k <test_name>` or `python -m pytest tests/test_<module>.py::test_<function>`
- **All Tests**: `python test.sh` or `pytest -m "not slow"`
- **Lint**: `ruff check kdrag/`
- **Type Check**: `pyright kdrag/`

## Code Style
- **Imports**: Group standard library, third-party, and local imports
- **Types**: Use type annotations for function parameters and return values
- **Formatting**: Follow PEP 8 guidelines; ruff handles formatting
- **Docstrings**: Include for public functions and classes
- **Function Names**: snake_case for functions, CamelCase for classes
- **Error Handling**: Use exceptions for failure conditions with clear messages
- **Test Names**: Prefix with `test_` and descriptively name the behavior

## Ruff Configuration
- Excludes test directories
- Ignores E741 (ambiguous variable names)
- Special ignores for specific files (see pyproject.toml)