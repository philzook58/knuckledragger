from dataclasses import dataclass


@dataclass(frozen=True)
class Sort:
    name: str


BoolSort = Sort("bool")
RealSort = Sort("real")
