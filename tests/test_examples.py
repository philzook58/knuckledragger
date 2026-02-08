import pytest

import subprocess
import tempfile


@pytest.mark.slow
def test_examples():
    import examples.soft_found.lf.indprop
    import examples.soft_found.lf.imp as imp
    #import examples.kt as ks
    imp.AExp