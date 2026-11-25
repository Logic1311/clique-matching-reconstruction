"""Independent exhaustive check using NetworkX graph isomorphism (c=3,4,5)."""
import networkx as nx
from itertools import combinations

def F(p,q,k):
    G=nx.Graph(); G.add_nodes_from(range(p+q))
    G.add_edges_from(combinations(range(p),2)); G.add_edges_from(combinations(range(p,p+q),2))
    G.add_edges_from((i,p+i) for i in range(k)); return G

def iso(G,H):
    return G.number_of_edges()==H.number_of_edges() and nx.is_isomorphic(G,H)
for c in range(3,6):
    for b in range(2,c):
        s=c-b; G=F(c,c,b); A=F(c,c-1,b-1); B=F(c,c-1,b)
        profiles=set(); n=2*c
        for base in [A,B]:
            for mask in range(1<<(n-1)):
                H=base.copy(); H.add_node(n-1); H.add_edges_from((n-1,i) for i in range(n-1) if mask>>i&1)
                if iso(H,G): continue
                a=d=0
                for v in H:
                    card=H.subgraph(set(H)-{v}); a+=iso(card,A); d+=iso(card,B)
                profiles.add((min(a,2*b),min(d,2*s)))
        if c>=4:
            for a in range(2*b+1):
                for d in range(2*s+1):
                    predicted=(a<=2*(s+1) and d==0) or (a==0 and d<=2*(b+1)) or (a<=b and d<=s+1)
                    assert predicted == any(x>=a and y>=d for x,y in profiles)
        unique=[a+d for a in range(2*b+1) for d in range(2*s+1) if not any(x>=a and y>=d for x,y in profiles)]
        ally=min(unique); adv=1+max(x+y for x,y in profiles)
        assert ally==(min(b+2,max(4,b)+1) if s==1 else min(b+2,s+3)) and adv==c+2
        print(c,b,ally,adv,len(profiles),flush=True)
