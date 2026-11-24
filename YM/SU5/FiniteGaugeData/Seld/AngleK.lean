import YM.SU5.FiniteGaugeData.Seld.Limb
import YM.SU5.FiniteGaugeData.Seld.Raft
set_option linter.unusedSimpArgs false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
open Function Filter Metric Complex Set MeasureTheory Lattice Mist Celeritas Land OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ContDiff
variable {K:Axis→Hilbert}(W:∀ a:Axis, OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) {H:Hilbert} {a:Axis}
namespace Breve
variable (a b:Axis)(L A B R:Shrine K) (m n:ℕ) (o y x z:E4)(t:ℝ)
local notation "S" u:max=> sites_r o (jeer a y u) x z
local notation "Θ"=> choice4 L A B R
local notation "I" i:max o:max t:max=> orbit_on W i o t
abbrev porder : List FHorizon:= [0,1,2,3]
abbrev rorder : List FHorizon:= [0,2,1,3]
structure Line2 : Prop where
 zeroA : A.t a=0
 zeroB : B.t a=0
 same_a : o a=y a
 behind : x a+ (L.t a:ℝ)= o a-2
 front : z a- (R.t a:ℝ)= o a+2
variable (p:Line2 a L A B R o y x z)
local notation "J"=> Ω a
local notation "Y"=> W a
local notation "ι"=> parabola (W a)
local notation "η"=> Par (W a)
local notation "d"=> OS.Semigroup.duration
abbrev week(m n:ℕ): FHorizon→ℕ:=![0,m,n,0]
include p
lemma turf(h:0<t)(u:t<2): porder.Pairwise (Seers (Θ) (S t) a)∧ rorder.Pairwise (Seers (Θ) (S (-t)) a):=by
 simp [porder,rorder,Seers,endX,startX,choice4,sites_r,p.zeroA,p.zeroB,top_a, ←p.same_a]; rcases p with ⟨wa,wb,e,w,c⟩; repeat' (first|apply And.intro|linarith)
local notation "Γ" x:max=> coast W a (week m n) (Θ) x
local notation "Ab"=> I a o A
local notation "Bb"=> I a y B
local notation "Lv"=> soup W Ω a L true x
local notation "Rv"=> soup W Ω a R false z
omit p in
lemma walkz : actO W (Θ) (S t) a 2= I a y B:=by
 change opt (Y) (jeer a y t) (B.f a)=opt _ y _; unfold jeer; rw [←opt_add]; unfold opt; rw [leg_veil,one_mul,←neg_smul,leg_veil,mul_one]
omit p in
private lemma Real2 {t:ℝ}(v:0≤t): OS.Semigroup.duration t.toNNReal=(t:ℂ):= by unfold OS.Semigroup.duration; rw [Real.coe_toNNReal t v]
variable (v:0<t)(p':t<2)
include v p'
lemma act_p : chalk W Ω a (week m n) (Θ) (S t) porder= backwards (Y) (Lv) (Rv) (Ab) (Bb) m n (t:ℂ):=by
 let S' : FHorizon→E4:= S t; let Z:= Γ S'; let U:=actO W (Θ) (S t) a
 have he: Z 0 1= η m 2:=by unfold Z coast; simp [week,S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,p.behind,Par] -- spelling
 have hh: Z 1 2=ι (m+n) (t:ℂ):=by unfold Z coast; simp [week,S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,top_a,←p.same_a, Real2 v.le]
 have hv: Z 2 3=ι n (2-(t:ℂ)):=by
    unfold Z coast; simp [week,S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,p.front,top_a,←p.same_a]; rw [Real2 (sub_pos.mpr p').le]; push_cast; rfl
 let A':=U 0; let Hh:Lv= A'.adjoint J:= rfl
 unfold backwards; rw [Hh, ContinuousLinearMap.adjoint_inner_left]; change inner ℂ _ (U 0 (Z 0 1 (U 1 (Z 1 2 (U 2 (Z 2 3 (U 3 J)))))))=_; rw [he,hh,hv,show U 2=Bb from walkz ..]; rfl
lemma act_r : chalk W Ω a (week m n) (Θ) (S (-t)) rorder= forwards (Y) (Lv) (Rv) (Ab) (Bb) m n (t:ℂ):=by
 let S' : FHorizon→E4:= S (-t); let Z:= Γ S'; let U:=actO W (Θ) (S (-t)) a
 have he: Z 1 3= η m 2:=by unfold Z coast; simp [week,S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,p.front,Par]
 have hh: Z 2 1=ι (m+n) (t:ℂ):=by unfold Z coast; simp [week,S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,top_a,←p.same_a, Real2 v.le]; rw [add_comm m]
 have hv: Z 0 2=ι n (2-(t:ℂ)):=by
    unfold Z coast; simp [week,S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,p.behind,top_a,←p.same_a]; rw [show -t+2=2-t from by ring, Real2 (sub_pos.mpr p').le]; push_cast; rfl
 let A':=U 0; let Hh:Lv= A'.adjoint J:= rfl
 unfold forwards; rw [Hh, ContinuousLinearMap.adjoint_inner_left]; change inner ℂ _ (U 0 (Z 0 2 (U 2 (Z 2 1 (U 1 (Z 1 3 (U 3 J)))))))=_; rw [he,hh,hv,show U 2=Bb from walkz ..]; rfl
#print axioms act_p
#print axioms act_r
end Breve
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
