import ZecaMantle
import SatinThinMemory
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Lattice Regis.Head.Brecht Regis.Circuit Stationary


open CF
open CF.Py.Rate.LocalLimit.Preparation.Yoke CF.QuadClock
namespace Gin
def v (c i:Axis):ℤ:= if i=c ∨ i=3 then 1 else 0
def M (c i j:Axis):ℤ:= -(if j=i then 1 else 0) + 2*v c i*v c j
def E (c i j k l:Axis):ℤ:=(if k=j then M c i l else 0)-(if l=j then M c i k else 0)
def X (c:Axis)(p q:PlaqAxes) :=
 E c p.val.1 p.val.2 q.val.1 q.val.2 -
 E c p.val.2 p.val.1 q.val.1 q.val.2
def z (p:PlaqAxes):ℤ:=if p=rimA∨p=rimD then 1 else if p=rimB∨p=rimC then -1 else 0

def codex (c:Axis):ℤ:=∑p: PlaqAxes,∑q:PlaqAxes, z p * z q * X c p q^2

lemma codex_2 : codex 2 = -16:=by decide
lemma codex_0 : codex 0 = 8:=by decide

def V (c:Axis)(t:ℝ):Gaia:=WithLp.toLp 2 fun i=>t*v c i
def amber (t:ℂ):ℂ:=2*Maxwell.normal*(2*t^2)⁻¹^2
def plug (t:ℂ)(c i:Axis):ℂ:= t * v c i
lemma flare (p q:Axis){t:ℂ}(h:t≠0)(c:Axis):
 bill p q (plug t c) (2*t^2)=M c p q * amber t:=by
 unfold bill plug M amber
 rw [basis_eq]
 by_cases a:q=p
 · rw [if_pos a,if_pos a]
   push_cast
   field_simp; ring
 rw [if_neg a,if_neg a]
 push_cast
 field_simp; ring
lemma zest (p q r s:Axis){t:ℂ}(h:t≠0)(c:Axis):
 curlIn p q r s (plug t c) (2*t^2)= E c p q r s * amber t:=by
 unfold curlIn E
 simp [flare _ _ h, sub_mul,ite_mul]
lemma amber_x (p q:PlaqAxes){t:ℂ}(h:t≠0)(c:Axis):
 stamp p q (plug t c) (2*t^2) = X c p q * amber t:=by
 simp [stamp,X,zest _ _ _ _ h, sub_mul]
lemma amber_z (p:PlaqAxes): (witnessZ p:ℂ)=z p/2:=by 
 unfold witnessZ z starWeight
 split_ifs<;>simp
#check duoPower
#check wholeV
#print axioms amber_x

def pri (t:ℝ):ℂ:= ((Fintype.card SU.group.ColorIndex:ℂ)/2) * amber (t:ℂ)^2
lemma price (c:Axis) {t:ℝ}(h:0<t):
 satire witnessZ SU.group (plug (t:ℂ) c) (2*(t:ℂ)^2)=(codex c:ℂ)*pri t:=by
 have g:(t:ℂ)≠0:=by exact_mod_cast h.ne'
 unfold satire wholeV duoPower codex
 simp_rw [Int.cast_sum,Finset.sum_mul,Int.cast_mul, Int.cast_pow,
   amber_z,amber_x _ _ g]
 apply Finset.sum_congr rfl
 intro p _
 apply Finset.sum_congr rfl
 intro q _
 unfold pri
 ring
#print axioms price
