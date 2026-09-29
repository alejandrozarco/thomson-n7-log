# Independent check: Hessian of Riesz s-energy (s=0 -> log) at the pentagonal bipyramid,
# restricted to the tangent space, modulo rotations. Uses mpmath finite differences.
import mpmath as mp, itertools
mp.mp.dps = 40
def pbp():
    X=[mp.matrix([0,0,1]),mp.matrix([0,0,-1])]
    X+= [mp.matrix([mp.cos(2*mp.pi*k/5),mp.sin(2*mp.pi*k/5),0]) for k in range(5)]
    return X
def energy(X,s):
    E=0
    for i,j in itertools.combinations(range(7),2):
        d=mp.norm(X[i]-X[j])
        E+= -mp.log(d) if s==0 else d**(-s)
    return E
def normalize(v): return v/mp.norm(v)
# pucker mode: ring points move in z with pattern cos(2*2pi k/5); poles fixed
def pucker(a):
    X=pbp()
    for k in range(5):
        v=X[2+k].copy(); v[2]+= a*mp.cos(2*2*mp.pi*k/5); X[2+k]=normalize(v)
    return X
for s in [0, 0.5, 1, 1.5, 2, 2.5]:
    h=mp.mpf('1e-8'); E0=energy(pbp(),s)
    d2=(energy(pucker(h),s)-2*E0+energy(pucker(-h),s))/h**2
    print(f"s={s}: d2E along k=2 pucker = {mp.nstr(d2,12)}")
