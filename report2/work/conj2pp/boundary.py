# 境界の場合(CS の数 = 状態の数、満ちたプロセスが絡む組)を厳密な判定で調べる
import sys, itertools, random, time
sys.path.insert(0, '.'); sys.path.insert(0, 'conj2pp')
from killchar import dist_kill
from nonfull import full
nS = int(sys.argv[1]); N = int(sys.argv[2])
rng = random.Random(21); F = [f for f in itertools.product(range(nS), repeat=nS) if f != tuple(range(nS))]
t0 = time.time(); fulls = []; tries = 0
while len(fulls) < 400 and tries < 3_000_000:
    tries += 1
    X = tuple(rng.choice(F) for _ in range(nS))
    if full(X, nS): fulls.append(X)
print(f"長さ {nS} の満ちたプロセス: {len(fulls)}/{tries} の割合で見つかった", flush=True)
bad = 0; tot = 0
for _ in range(N):
    X = rng.choice(fulls); Y = list(X)
    r = rng.random()
    if r < 0.6: Y[rng.randrange(nS)] = rng.choice(F)
    elif r < 0.8: Y = list(rng.choice(fulls))
    else: Y = [rng.choice(F) for _ in range(nS)]
    Y = tuple(Y)
    if Y == X: continue
    tot += 1
    if dist_kill(X, Y, nS) is None:
        bad += 1; print("区別できない:", X, Y, flush=True)
print(f"|S|={nS}: 満ちた長さ {nS} のプロセスとの組 {tot} 組中、区別できない {bad} ({time.time()-t0:.0f}s)")
