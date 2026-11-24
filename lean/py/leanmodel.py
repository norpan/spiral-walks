# Reads the definitions in ../Falafel/Model.lean (and the table in ../Falafel/Stamp.lean) and turns them
# into Python functions, so that the exact Lean text can be tested here.  Only the small expression language used in that file is
# understood: if/then/else, + - * / %, comparisons, parentheses, integer literals, function calls.
import re, os
SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "Falafel", "Model.lean")
TOK = re.compile(r"\s*(≥|≤|:=|[-+*/%()=<>]|[A-Za-z_][A-Za-z_0-9]*|\d+)")
def tokens(s):
    out = []; i = 0; s = s.rstrip()
    while i < len(s):
        m = TOK.match(s, i)
        if not m: raise SyntaxError("cannot read: " + s[i:i+30])
        out.append(m.group(1)); i = m.end()
    return out
class P:
    def __init__(self, toks, names): self.t = toks; self.i = 0; self.names = names
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def take(self, x=None):
        tok = self.peek()
        if x is not None and tok != x: raise SyntaxError("expected %s, got %s at %d" % (x, tok, self.i))
        self.i += 1; return tok
    def expr(self):                       # if-then-else, or a comparison
        if self.peek() == "if":
            self.take("if"); c = self.expr(); self.take("then"); a = self.expr(); self.take("else"); b = self.expr()
            return "(%s if %s else %s)" % (a, c, b)
        a = self.arith()
        ops = {"≥": ">=", "≤": "<=", "=": "==", "<": "<", ">": ">"}
        if self.peek() in ops:
            op = ops[self.take()]; b = self.arith(); return "(%s %s %s)" % (a, op, b)
        return a
    def arith(self):
        a = self.term()
        while self.peek() in ("+", "-"):
            op = self.take(); b = self.term(); a = "(%s %s %s)" % (a, op, b)
        return a
    def term(self):
        a = self.unary()
        while self.peek() in ("*", "/", "%"):
            op = self.take(); b = self.unary(); a = "(%s %s %s)" % (a, "//" if op == "/" else op, b)
        return a
    def unary(self):
        if self.peek() == "-": self.take(); return "(-%s)" % self.unary()
        return self.app()
    def atom(self):
        tok = self.take()
        if tok == "(": e = self.expr(); self.take(")"); return e
        if re.fullmatch(r"\d+", tok) or re.fullmatch(r"[A-Za-z_]\w*", tok): return tok
        raise SyntaxError("unexpected " + str(tok))
    def app(self):                        # function application by juxtaposition
        tok = self.peek()
        if tok in self.names:
            self.take(); args = []
            while self.peek() is not None and (self.peek() == "(" or re.fullmatch(r"\w+", self.peek())) \
                    and self.peek() not in ("then", "else", "if"):
                args.append(self.atom())
            return "%s(%s)" % (tok, ", ".join(args))
        return self.atom()
def load():
    text = open(SRC, encoding="utf-8").read()
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = "\n".join(l.split("--")[0] for l in text.splitlines())
    defs = re.findall(r"^def (\w+) ((?:\(.*?\) )+): ℤ :=(.*?)(?=^def |^end |\Z)", text, flags=re.S | re.M)
    names = {d[0] for d in defs}; env = {}
    for name, binders, body in defs:
        args = re.findall(r"\(([^:]*):", binders); args = " ".join(args).split()
        p = P(tokens(body), names); e = p.expr()
        if p.peek() is not None: raise SyntaxError("trailing tokens in " + name)
        exec("def %s(%s): return %s" % (name, ", ".join(args), e), env)
    return {n: env[n] for n in names}
L = load()
globals().update(L)

def load_prefix():
    """The list `prefixList` of ../Falafel/Stamp.lean."""
    text = open(os.path.join(os.path.dirname(SRC), "Stamp.lean"), encoding="utf-8").read()
    body = re.search(r"def prefixList : List \(ℤ × ℤ\) :=\s*\[(.*?)\]", text, flags=re.S).group(1)
    return [(int(a), int(b)) for a, b in re.findall(r"\((-?\d+),\s*(-?\d+)\)", body)]
PREFIX = load_prefix()
