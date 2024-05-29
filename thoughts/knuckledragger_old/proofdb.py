
from dataclasses import dataclass



class ProofDB():
    def __init__(self):
        self.__proofdb = []
    def assume(self, formula, reason):
        self.__proofdb.append((formula, reason))
        return Theorem(len(self.__proofdb), self)
    def __getitem__(self, key):
        return self.__proofdb[key]
    def __len__(self):
        return len(self.__proofdb)
    
@dataclass(frozen=True)
class Theorem():
    formula_id: int
    proofdb: ProofDB
    def formula(self):
        return self.proofdb[self.formula_id][0]
    def repr(self):
        return f"Proof({self.formula()})"