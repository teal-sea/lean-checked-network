import copy
from fractions import Fraction as F
import pytest
from exact_check import Arithmetic,replay,tree_check,run

def fixture():
 return {'complete':True,'manifest':{'decimal_box':[['-1'],['1']]},'root':[[-1],[1]],'layers':[{'w':[[1]],'b':[0]},{'w':[[1]],'b':[2]}],'c':[[1]],'rhs':[0],'nodes':[{'box':[[-1],[1]],'terminal':True,'objective':0,'alphas':[[0.5]]}]}
@pytest.mark.parametrize('p',[None,30,50,80])
def test_sound_relu(p):
 c=fixture();r=run(c,p);assert r['passed']==1;assert F(r['min_margin'])==F(3,2)
@pytest.mark.parametrize('p',[None,30,50,80])
def test_negative_relu(p):
 c=fixture();c['layers'][1]['w']=[[-1]];c['layers'][1]['b']=[2]
 assert replay(c,c['nodes'][0],Arithmetic(p))==1

def test_gap():
 c=fixture();c['nodes']=[{'box':[[-1],[1]],'dim':0,'cut':0,'children':[1,2]},{'box':[[-1],[0]],'terminal':True,'objective':0,'alphas':[[0.5]]},{'box':[[0.25],[1]],'terminal':True,'objective':0,'alphas':[[0.5]]}]
 with pytest.raises(ValueError,match='gap'):tree_check(c)
def test_incomplete():
 c=fixture();c['complete']=False
 with pytest.raises(ValueError,match='incomplete'):tree_check(c)
def test_invalid_alpha():
 c=fixture();c['nodes'][0]['alphas']=[[1.1]]
 with pytest.raises(ValueError,match='alpha'):run(c)
def test_rounding_enclosure():
 a=Arithmetic(30)
 for x in [F(-7,3),F(1,7),F(12,17)]:
  for y in [F(3,11),F(-3,7)]:
   assert a.op('mul',x,y)<=x*y<=a.op('mul',x,y,True)
   assert a.op('div',x,y)<=x/y<=a.op('div',x,y,True)
def test_mutated_weight_rejects():
 c=fixture();c['layers'][1]['w']=[[-4]]
 assert run(c)['failed']==1 # actual value at x=1 is -2
