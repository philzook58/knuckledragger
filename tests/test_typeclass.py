
import pytest
import kdrag.property as prop

class Foo1(prop.TypeClass):
    def check(self, key):
        assert self.x == 1

class Foo2(prop.TypeClass):
    def check(self, key):
        assert self.x == 2




def test_typeclass():
    Foo1.register("mykey", x=1)
    Foo2.register("mykey", x=2)
    Foo1("mykey")
    Foo2("mykey")
    with pytest.raises(Exception) as _:
        Foo1.register("mykey2", x=2)
    with pytest.raises(Exception) as _:
        Foo1.register("mykey", x=1)

