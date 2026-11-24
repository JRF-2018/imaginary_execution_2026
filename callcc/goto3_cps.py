# -*- coding: utf-8 -*-
"""JRF《Haskell の callCC で goto を作る》example_goto_3.hs の Cont モナドを
Python の継続渡しにそのまま写したもの。"stop" を送ったときに何が起きるかを調べる。"""
import sys
sys.setrecursionlimit(100000)

def ret(x):      return lambda k: k(x)
def bind(m, f):  return lambda k: m(lambda a: f(a)(k))
def callCC(f):   return lambda k: f(lambda a: (lambda _k: k(a)))(k)

TRACE = []
class Loop(Exception): pass

def looper(inp, out):
    return callCC(lambda goto: ret(("LoopStart", inp, out, goto)))

def mk_service(goto):
    return lambda x, y, r: bind(goto(("Method1", x, y, r, goto)), lambda uv: ret(uv[0]))

def server_case(z):
    tag = z[0]; TRACE.append("S:" + tag)
    if len(TRACE) > 60: raise Loop()
    if tag == "LoopEnd":
        _, inp, out, goto = z
        return ret((out + " slend " if not inp else out + inp[0] + " slastnext ", mk_service(goto)))
    if tag == "LoopStart":
        _, inp, out, goto = z
        if not inp: return goto(("LoopEnd", [], out + " slse ", goto))
        return goto(("LoopStart", inp[1:], out + " slsn " + inp[0], goto))
    if tag == "Method1":
        _, inp, out, r_, goto = z
        if not inp: return goto(("LoopEnd", [], out + " sm1e ", goto))
        c, rest = inp[0], inp[1:]
        if c == "stop":
            # ここから return に向かうこともできる。しかし、そこからどこへ行くのだろう？
            return goto(("LoopEnd", rest, out + " sm11e " + c, goto))
        return bind(r_(out + " sm1n " + c), lambda y: goto(("Dummy",)))
    raise RuntimeError("server: non-exhaustive pattern " + tag)

server = bind(looper([], ""), server_case)

def client_case(z):
    tag = z[0]; TRACE.append("C:" + tag)
    if tag == "LoopEnd":
        _, inp, out, goto = z
        return ret((out + " clend " if not inp else out + inp[0] + " clastnext ", mk_service(goto)))
    if tag == "LoopStart":
        _, inp, out, goto = z
        return bind(server, lambda so: goto(("LoopMain", inp, so[0] + out, goto)))
    if tag == "LoopMain":
        _, inp, out, goto = z
        if not inp: return goto(("LoopEnd", [], out + " clme ", goto))
        c, rest = inp[0], inp[1:]
        def got_server(so, c=c, rest=rest, out=out, goto=goto):
            TRACE.append("C:got server, sending " + c)
            return so[1]([c], out + " clmn " + c,
                         lambda y: bind(goto(("Receive1", rest, y, goto)), lambda uv: ret(uv[0])))
        return bind(bind(server, got_server), lambda y: goto(("Dummy",)))
    if tag == "Receive1":
        _, inp, out, goto = z
        if not inp: return goto(("LoopEnd", [], out + " cr1e ", goto))
        return goto(("LoopMain", inp[1:], out + " cr1n " + inp[0], goto))
    raise RuntimeError("client: non-exhaustive pattern " + tag)

def runclient(inp): return bind(looper(inp, ""), client_case)

for inp in (["a", "b", "c", "d", "e"], ["a", "b", "stop", "d", "e"]):
    TRACE.clear()
    try:
        bind(runclient(inp), lambda uv: ret(uv[0]))(print)
    except Loop:
        print("(終わらない)")
    print("  入力", inp, "\n  経路:", " ".join(TRACE[:40]), "...\n" if len(TRACE) > 40 else "\n")
