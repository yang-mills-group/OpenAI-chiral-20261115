import YM.CF.Haro.Silk
import YM.CF.Prism.Col
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(G:Ratio c f)(h: Odd G.count.val)
open Branch Laic
variable {t:ℝ}(p:0<t)(Y: cro G t)(W: Meter TailB G t)
open Skye Precision
open Jet Scree
variable (X:Hub f){P:RG.BudgetPoint}{v u:ℝ}(F:InkD f)(hp:PressB P X F u v)(U:Pane f)
-- sing.R Φ. syntax.Aff.Weight $ord.Wick.TRUE.
abbrev CharM (a b:Prism.Rock f): Pane f→ Op Slot:= fun x=> Prism.mileT a b true false (F x)
variable (A B: Support (More f))(r s:Prism.Rock f)(i j:Prism.Rock c)(Z:Rill.Arch G t)
abbrev lyric (p:0<t) (W: Meter TailB G t)(F:InkD f)(A B:Support (More f))(r s:Prism.Rock f)(i j:Prism.Rock c)(U:Pane f)(Z:Rill.Arch G t):Op Slot:= star (fyL G true W (bring p Z) A r i)*CharM F r s U * fyL G false W (bring p Z) B s j
include hp
lemma char_g (g:Seat f→SU.E): CharM F r s (Lattice.gauge g U)= putX g r * CharM F r s U * star (putX g s):= Prism.forge hp r s true false g U -- tune
abbrev verQ(Z:Rill.Arch G t):Prop:=Z.val=1
variable (C Q:Toll (Iota G))(a:Suite (badge _) (pinH G t true) (pinH G t false) A C (W (true,true) A))(b:Suite (badge _) (pinH G t true) (pinH G t false) B Q (W (true,false) B))
include p a b
lemma lyric_g (g:Seat f→SU.E): let v:= Peaks.scaleG G g; lyric G p W F A B r s i j (gauge g U) (herb G g Z) = putX v i * lyric G p W F A B r s i j U Z * star (putX v j):=by
 intro v; let R:=bring p Z; let T:=bring p (herb G g Z)
 have he(X Y:Op Slot)(t:SU.E)(W:Op Slot)(h:X*mater t=W*Y): X=W*Y*star (mater t):=by rw [←h,mul_assoc,show mater t *star (mater t)=1 from (matter t).property.2, mul_one] -- tune
 let I:=putX g r; let S:=putX g s; let D:=putX v i; let V:=putX v j
 let X:= fyL G true W R A r i; let L:=fyL G false W R B s j
 unfold lyric; rw [char_g _ F hp,show fyL G true W _ A r i= I*X*star D from he _ _ (v _) I (marchG G p W g Z true C _ a r i), show fyL G false W _ B s j= S*L*star V from he _ _ (v _) S (marchG G p W g Z false Q _ b s j)]; change star (I*X*_) * (I*_*star S) * (S*L*star V)=D* (star X*_*L)*star V
 have ht:star I * I=1:=(matter _).property.1; have hQ :star S*S=1:=(matter _).property.1; simp only [star_mul,star_star]; generalize CharM F r s U=K; -- noncomm_simp
 simp only [mul_assoc]; rw [←mul_assoc (star S),hQ, one_mul]; rw [←mul_assoc (star I),ht,one_mul]
omit p a b hp
def taxi (V:Pane c)(a b:Prism.Rock c)(F:Op Slot):Op Slot:= F * mater (travel V (node a.1) (shiftH (node a.1) (node b.1)))
lemma care(V:Pane c)(p:Op Slot)(t:∀ i:SU.E,Commute p (mater i))(g:Seat c→SU.E): taxi (gauge g V) i j p = putX g i*taxi V i j p*star (putX g j):=by
 unfold taxi; rw [travel_gauge,stopH]; unfold putX mater; simp only [map_mul,map_inv]; -- tune
 let x:=mater (g (node i.1)); let y:=mater (g (node j.1)); change p*(x*_*star y)=x*(p*_)*star y; rw [←mul_assoc,←mul_assoc p,(t _).eq, mul_assoc x] -- tune
include p hp a b
lemma taxing (x:SU.E)(hz:verQ G Z): Commute (lyric G p W F A B r s i j 1 Z) (mater x):=by
 let F': Seat f→SU.E:= fun _=>x; let H:= lyric G p W F A B r s i j 1 Z; have hh:= lyric_g G p W X F hp 1 A B r s i j Z C Q a b F'; let Y:Pane f:=1
 have hp0: Lattice.gauge F' Y=Y:=funext fun i=> by simp [Lattice.gauge,F',Y] -- tune
 have he: herb G F' Z=Z:=by
    apply Subtype.ext; change (Peaks.july G F' Z.val.1,gauge _ Z.val.2) = Z.val; rw [hz]; unfold july; change ((gauge F' Y,gauge (Peaks.scaleG G F') (1:Pane c)), gauge F' Y)=(1:Nom c f × Pane f); rw [hp0, show gauge (Peaks.scaleG G F') (1:Pane c)=1 from funext fun i=>by simp [Lattice.gauge,Peaks.scaleG,F']]; rfl
 change lyric G p W F A B r s i j (gauge F' Y) (herb G F' Z)= mater x * H * star (mater x) at hh; rw [he,hp0] at hh; change H = _ at hh; change H * _= _*H
 calc
    H * _=(mater x*H*star (mater x))*mater x:= congr_arg (·*mater x) hh
    _ = _:=by rw [mul_assoc,show star (mater x)*_=1 from (matter x).property.1,mul_one]
end YM.CF.Haro
