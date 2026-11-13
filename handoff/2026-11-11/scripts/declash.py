import re,subprocess,os,sys
os.chdir('/Users/samsara/code/era-protocol-specs')
env=dict(os.environ,PATH=os.path.expanduser('~/.elan/bin')+':'+os.environ['PATH'])
def mod2file(m): return m.replace('.','/')+'.lean'
def importers(target):
    # all .lean files that (transitively) import target module
    files=subprocess.run(['git','ls-files','EraSpec/*.lean','EraSpec/**/*.lean'],capture_output=True,text=True).stdout.split()
    imp={f:set(re.findall(r'^import (\S+)',open(f).read(),re.M)) for f in set(files)}
    res={mod2file(target)}; ch=True
    while ch:
        ch=False
        for f,ims in imp.items():
            if f not in res and any(mod2file(i) in res for i in ims): res.add(f); ch=True
    return res
prev=None
for it in range(60):
    out=subprocess.run(['lake','build','EraSpec'],capture_output=True,text=True,env=env).stdout
    m=re.search(r"import (\S+) failed, environment already contains '([^']+)' from (\S+)",out)
    if not m:
        print('no more clashes; tail:'); print('\n'.join([l for l in out.splitlines() if 'error' in l][:10])); break
    mod2,name,mod1=m.groups()
    if (mod2,name)==prev: print('STUCK',name,mod1,mod2); break
    prev=(mod2,name); short=name.split('.')[-1]
    topic=mod2.split('.')[-1]; new=f"{short}_{topic}"
    fs=sorted(importers(mod2)-{'EraSpec.lean'})
    n=0
    for f in fs:
        s=open(f).read(); s2=re.sub(r'(?<![\w\'.])'+re.escape(short)+r'(?![\w\'])',new,s); s2=re.sub(r'(?<=\bProperties\.)'+re.escape(short)+r'(?![\w\'])',new,s2)
        if s2!=s: open(f,'w').write(s2); n+=1
    print(f"[{it}] {name}: {mod1} vs {mod2} -> {new} in {n} files")
