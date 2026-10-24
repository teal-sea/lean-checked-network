"""Emit the factored residual program used by every leaf."""
def render(template):
 s=template.replace('namespace RouteA','namespace RouteNC\nopen RouteA').replace('end RouteA','end RouteNC')
 a=s.index(' let ml :=');z=s.index('\ndef contrib',a)
 return s[:a]+''' let nq := Int.mul nn Q
 let pos := Int.sub aa nq
 let neg := Int.neg nq
 let ml := Int.mul (if l ≤ 0 then neg else pos) l
 let mu := Int.mul (if u ≤ 0 then neg else pos) u
 if l ≤ 0 ∧ 0 ≤ u then min 0 (min ml mu) else min ml mu) a n
'''+s[z:]
