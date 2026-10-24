import pathlib,json,re
R=pathlib.Path.cwd();leaves=json.loads((R/'leaves.json').read_text())
s='import CoverageData\n'+''.join(f'import N{i}.AcceptNC\n' for i in leaves)+'\nopen RouteA SharedWeights\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
props=[];proofs=[]
for i in leaves:
 a=(R/f'N{i}/AcceptNC.lean').read_text();prop=a.split(f'theorem node{i}NC : ',1)[1].split(' :=',1)[0]
 prop=re.sub(r'\b([vc][0-5])\b',lambda m:f'Leaf{i}.{m[0]}',prop)
 props.append('('+prop+')');proofs.append(f'Proof{i}.node{i}NC')
 s+=f'theorem boxMatches{i} : Leaf{i}.boxl.zip Leaf{i}.boxu = (nodes[{i}]!).box := by decide +kernel\n'
s+='theorem allLeavesNC : '+' ∧ '.join(props)+' :=\n ⟨'+', '.join(proofs)+'⟩\n#print axioms allLeavesNC\n'
s+='theorem terminalIds : (nodes.toList.zipIdx.filterMap (fun (n,i) => match n.kind with | .leaf => some i | _ => none)) = '+str(leaves)+' := by decide +kernel\n#print axioms terminalIds\n#print axioms coverage_checked\n'
(R/'AllLeaves.lean').write_text(s)
