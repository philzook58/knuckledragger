from knuckledrag2 import *

global_var_env = {}

class MetaVar(Term):

    def __init__(self, name, env = global_var_env):
        self.name = name
        self.env = env
        if name not in self.env:
            self.level = -1
            self.env[name] = 0
        else:
            self.level = global_var_env[name]
            self.env[name] = self.level + 1

    def __str__(self):
        if self.level == -1:
            return self.name
        else:
            return self.name + str(self.level)

    def __eq__(self, other):
        if not isinstance(other, MetaVar):
            return False
        return (self.name == other.name) and (self.level == other.level)
    def __hash__(self):
        return hash((self.name, self.level))

# A little clunky
def open_vars_aux(term, metas):
    if isinstance(term, Var):
        if term.name in metas:
            return metas[term.name]
        else:
            return term
    if isinstance(term, FunApp):
        #We force the list right away
        args = list(map(lambda t: open_vars_aux(t, metas), term.args))
        return FunApp(term.name, args)
    if isinstance(term, BindApp):
        metas_pruned = metas.copy()
        bound_names = map(lambda v: v.name, term.vars)
        for v in metas_pruned:
            if v in bound_names:
                del(metas_pruned[v])
        return BindApp(term.vars, open_vars_aux(term.body, metas_pruned))
    if isinstance(term, MetaVar):
        return term
    else:
        raise ValueError("open_vars_aux: unkown instance")

#Uses global_var_env for now
def open_bound(term):
    if isinstance(term, BindApp):
        metas = {}
        for v in term.vars:
            mv = MetaVar(v.name)
            metas[v.name] = mv
        return open_vars_aux(term.body, metas)
    raise ValueError('open_bound: value is not a binder!')

#Substitutions are little more than a wrapper around a dictionary,
# and a method that performs the substitution `this.apply(term)`.
class Subst():

    def __init__(self, assgn):
        self.assgn = assgn

    def __getitem__(self, key):
        return self.assgn[key]

    def __setitem__(self, key, newval):
        self.assgn[key] = newval

    def __contains__(self, key):
        return key in self.assgn

    # tedious; python doesn't like dicts with wonky keys
    def __str__(self):
        s = (", ".join("{}: {}".format(k, v) for k, v in self.assgn.items()))
        return "{{ {} }}".format(s)

    def apply(self, term):
        # this would be better/easier with a visitor
        if isinstance(term, MetaVar):
            return self.applyMetaVar(term)
        if isinstance(term, Var):
            return self.applyVar(term)
        if isinstance(term, FunApp):
            return self.applyFunApp(term)
        if isinstance(term, BindApp):
            return self.applyBindApp(term)
        ## We could return term here, but it's a bit "offensive"
        raise ValueError("Subst.apply: Unkown term constructor")

    def applyMetaVar(self, term):
        if term in assgn:
            return self[term]
        else:
            # for now, we allow metavariables to go unresolved
            return term

    def applyVar(self, term):
        return term

    def applyFunApp(self, term):
        return FunApp(term.name, map(lambda t:self.apply(t), term.args))

    def applyBindApp(self, term):
        #things are easy here, because we handled shadowing in `open_bound`
        return BindApp(term.vars, self.apply(term.body))

def EmptySubst():
    return Subst({})

#takes a single pattern (with "fresh" metavars) and a term and returns
#the mgu, or None if none exists.
class Matcher():

    def __init__(self, pattern, term, subst):
        self.pattern = pattern
        self.term = term
        self.subst = subst

    def apply(self):
        if not self.subst:
            return
        if isinstance(self.pattern, MetaVar):
            #the interesting bit
            if self.pattern in self.subst:
                self.pattern = self.subst[self.pattern]
                self.apply()
                return
            else:
                #this is a call to `Subst.__setitem__`
                self.subst[self.pattern] = self.term
                return
        if isinstance(self.pattern, Var) and isinstance(self.term, Var):
            if self.pattern.name != self.term.name:
                self.subst = None
                return
        if isinstance(self.pattern, FunApp) and isinstance(self.term, FunApp):
            if self.pattern.name != self.term.name:
                self.subst = None
                return
            for i in range(len(self.pattern.args)):
                self.pattern = self.pattern.args[i]
                self.term = self.term.args[i]
                self.apply()
                return

        if isinstance(self.pattern, BindApp) and isinstance(self.term, BindApp):
            for v in self.pattern.vars:
                if v not in self.term.vars:
                    self.subst = None
                    return
                self.pattern = self.pattern.body
                self.term = self.term.body
                self.apply()
                return
        else:
            self.subst = None
            return

def match(pattern, term):
    matcher = Matcher(pattern, term, EmptySubst())
    matcher.apply()
    return matcher.subst

if __name__ == "__main__":
    x = Var('x')
    A = lambda t:Atom('A', [t])
    B = lambda t:Atom('A', [t])
    three = Var('3')
    matcher = ForAll([x], A(x))
    matchee = A(three)
    print(match(open_bound(matcher), matchee))
