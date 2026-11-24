import YM.CF.Haro.Cubit
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
-- stationary lifts.Cost.C all orb wraps explicit
variable {n:Side}
abbrev rentH(F:Op (Single n)):= (love n).symm F
abbrev matPH(F:Op (Single n))(x y:Site n):= Scroll.tap (rentH F) x y
abbrev upper(v:Signed)(x:Cover):= if detX v then -x else x -- for lift under adjoint
abbrev AxisB(F:Op (Single n)):Prop:=∀ (A:Shape)(b:Bool)(U:UNI SpinIdx),JetS A.s b (detX A.s) U→ sings b (prepU A U (xtra b) n) F=Thera.jazz (detX A.s) F
variable(F:Op (Single n))(hp:AxisB F)
lemma mate_v(P T:Op (Single n))(x:Site n)(A:Shape)(b:Bool)(U:UNI SpinIdx)(h:sings b (prepU A U (xtra b) n) P=T)(y:Cover)(V: Pal)(g:matPH P (A.mills n x) (A.mills n x+wrap n (A.s.act y))=Rush.wind (A.mills n x) (A.s.act y) • V):matPH T x (x+wrap n y)=Rush.wind x y • sings b (twoU U b) V:=by
 unfold matPH rentH; rw [←h]; obtain ⟨Y,rfl⟩:= (love n).surjective P; change matPH ((love n) Y) _ _= _ at g; change tap ((love n).symm (sings b (prepU A U (xtra b) n) ((love n) Y))) _ _= _; rw [wingX,StarAlgEquiv.symm_apply_apply,tap_sg]
 have he: Scroll.tap Y (A.mills n x) (A.mills n x+wrap n (A.s.act y))= Rush.wind (A.mills n x) (A.s.act y) • V:=by -- tune
    unfold matPH rentH at g; rwa [StarAlgEquiv.symm_apply_apply] at g
 change _* windX b (tap _ (A.mills n x) (A.mills n _))*star _= _; rw [A.tow,he]; exact lane_x ..
def tapH(x:Cover): Pal:= Rush.wind (0:Site n) x • matPH F 0 (wrap n x)
lemma wind_t (x: Site n)(y:Cover)(T: Pal): Rush.wind x y • Rush.wind x y • T=T:=by rw [smul_smul,show Rush.wind x y*Rush.wind x y=1 from fee_one _, one_smul] -- implicit
include hp
lemma taff(x:Site n)(y:Cover): matPH F x (x+wrap n y)= Rush.wind x y • tapH F y:=by
 let U:=lagX (-natural x); have he: U.mills n x=0:=by unfold U; rw [lag_i,map_neg,nat_true]; abel
 have hs: detX U.s=false:=det_i
 have H:=hp U false 1 (hs.symm ▸ calmSX); apply Eq.trans (b:=Rush.wind x y • sings false (twoU 1 false) (tapH F y)) (mate_v F F x U false 1 (show _ from ?_) y _ ?_) ?_
 · rw [hs] at H; exact H
 · rw [he,show U.s.act y=y from (by simp [U,lagX]),zero_add]; exact (wind_t 0 _ _).symm
 · change _ • twist _ _ =_; rw [show twoU 1 false=1 from Subtype.ext (Matrix.one_kronecker_one (α:=ℂ)), Fock.one_des]; rfl
lemma taste_g (s:Signed)(b:Bool)(U:UNI SpinIdx)(g:JetS s b (detX s) U)(x: Cover): sings b (twoU U b) (tapH F (s.act x))=if detX s then -star (tapH F (-x)) else tapH F x:=by
 let a:= incX s; let i:Site n:=0; let j:= wrap n x; have he:=mate_v F _ i a b U (hp a b U g) x _ (taff F hp _ _)
 rw [show i+wrap n x=j from zero_add _] at he; have ht:s=a.s:=rfl; cases hv:detX s; swap
 · rw [← ht,hv] at he; change matPH (-star F) i j=_ • sings b (twoU U b) (tapH F (s.act x)) at he
   have hp': matPH (-star F) i j= -(star (matPH F j i)):=by unfold matPH rentH; rw [map_neg,map_star]; rfl
   rw [hp',show matPH F j i= Rush.wind j (-x) • tapH F (-x) from ?_,star_smul, show star (Rush.wind j (-x))=Rush.wind i x from ?_] at he -- tune
   · change _= -star _; rw [←wind_t i x (sings _ _ _),←he, ←smul_neg]; exact wind_t ..
   · rw [show star (Rush.wind j (-x))=Rush.wind j (-x) from fee_real _]; have h:= invert_wx i x; rw [show i+wrap n x=j from zero_add _] at h; exact h.symm
   · have hx:= taff F hp j (-x); rw [map_neg,show j+ -wrap n x=i from add_neg_cancel _] at hx; exact hx
 rw [←ht,hv] at he; change matPH F i j= Rush.wind _ _ • sings b (twoU U b) (tapH F (s.act x)) at he; change _= tapH F x; rw [←wind_t i x (sings _ _ _),←he]; rfl
end YM.CF.Haro
