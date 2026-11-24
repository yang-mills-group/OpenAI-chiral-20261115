import YM.SU5.FiniteGaugeData.Celeritas.Emblem
import YM.SU5.FiniteGaugeData.Celeritas.Lacem
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace InnerProductSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
set_option quotPrecheck false
namespace Land
open Mist
variable {K:Axis→Hilbert}(W:∀ a:Axis, OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) (U:Set (Shrine K)) (a b:Axis)
abbrev FHorizon:= Fin 4
variable (V L A B R:Shrine K)
-- coordinate gap along a x Ω etc
variable (o y x z:E4) (t:ℝ)
local notation "F" x:max=> (x: Shrine K)
def jeer (u:ℝ) := y+u • basis a
def sites_r (o y x z:E4): FHorizon → E4 := ![x,o,y,z]
-- o origin of A moved? use o general instead of 0. a-coord same as y initially. x left, z right
local notation "S" u:max=> sites_r o (jeer a y u) x z
abbrev choice4 : FHorizon→Shrine K := ![L,A,B,R] -- Section V not used
abbrev orbit_on (V:Shrine K):= opt (W a) o (V.f a)
local notation "I" i:max o:max t:max=> orbit_on W i o t -- arg order test
local notation "Θ"=> choice4 L A B R
local notation "ε"=>t • basis a
-- assumptions lengths, positions, and b$t capacity.
structure Line : Prop where
 zeroA : A.t a=0
 zeroB : B.t a=0
 same_a : o a=y a -- time
 behind : x a+ (L.t a:ℝ)= o a-1
 front : z a- (R.t a:ℝ)= o a+1
variable (p:Line a L A B R o y x z)
local notation "ι" t:max=> (W a).E t
local notation "J"=> (Ω a)
-- reduce. Need order includes nodup.M
@[simp] lemma top_a (t:ℝ):jeer a y t a= y a+t:=by simp [jeer]
include p
lemma dawn_p(t:ℝ)(h:0<t)(u:t<1): List.Pairwise (Seers (Θ) (S t) a) [0,1,2,3]:=by
 simp only [List.pairwise_cons]; -- stack small
 simp [Seers,endX,startX,choice4,sites_r,p.zeroA,p.zeroB,top_a, ←p.same_a]; rcases p with ⟨wa,wb,e,w,c⟩; repeat' (first|apply And.intro|linarith)
lemma dawn_r (t:ℝ)(h:0<t)(u:t<1): List.Pairwise (Seers (Θ) (S (-t)) a) [0,2,1,3]:=by
 simp [Seers,endX,startX,choice4,sites_r,p.zeroA,p.zeroB,top_a, ←p.same_a]; rcases p with ⟨wa,wb,e,w,c⟩; repeat' (first|apply And.intro|linarith)
private lemma orbit_a(v:Shrine K)(t:ℝ):orbit_on W a (jeer a y t) v=orbit_on W a y v:=by unfold orbit_on; unfold jeer; rw [←opt_add]; unfold opt; rw [leg_veil,one_mul,←neg_smul,leg_veil,mul_one]
lemma dawnH(t:ℝ): chorus W Ω (Θ) (S t) [0,1,2,3] a = heat_A (W a) (I a o A) (I a y B) (star (I a x L) J) ((I a z R) J) (↑t) := by
 unfold heat_A; rw [show 1-(t:ℂ)=↑(1-t) from (by push_cast; rfl), veil_real,veil_real]; -- tune ofreal
 unfold chorus; rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left];
 -- simplify Hi computing NN.LENGTH. h validated all t clipping; E1 OK. Mark's width.L α. `Hi inner sign center`.
 let S': FHorizon → E4:= S t; have Hx:Leap W (Θ) S' a 0 1=ι 1:=by unfold Leap; congr 1; simp [S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,p.behind] -- z norm sum
 have Hy:Leap W (Θ) S' a 1 2=ι t.toNNReal:=by unfold Leap; congr 1; simp [S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,top_a,←p.same_a]
 have Hz:Leap W (Θ) S' a 2 3=ι ((1-t).toNNReal):=by unfold Leap; congr 1; simp [S',Hi,startX,endX,choice4,sites_r,p.front,p.zeroB,top_a,←p.same_a]; -- need algebra
 let U':=actO W (Θ) (S t); have H2: U' a 2=I a y B:=orbit_a W a L A B R _ _ _ _ p B t -- tune arg
 change inner ℂ J ((U' a 0) (Leap W (Θ) S' a 0 1 (U' a 1 (Leap W (Θ) S' a 1 2 (U' a 2 (Leap W (Θ) S' a 2 3 (U' a 3 J))))))) = _; rw [Hx,Hy,Hz,H2]; rfl
#print axioms dawnH
lemma duskB(t:ℝ): chorus W Ω (Θ) (S (-t)) [0,2,1,3] a = heat_B (W a) (I a o A) (I a y B) (star (I a x L) J) ((I a z R) J) (↑t) := by
 unfold heat_B; rw [show 1-(t:ℂ)=↑(1-t) from (by push_cast; rfl), veil_real,veil_real]; -- tune ofreal
 unfold chorus; rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left];
 -- simplify Hi computing NN.LENGTH. h validated all t clipping; E1 OK. Mark's width.L α. `Hi inner sign center`.
 let S': FHorizon → E4 := S (-t); have Hx:Leap W (Θ) S' a 0 2=ι ((1-t).toNNReal):=by unfold Leap; congr 1; simp [S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,p.behind,←p.same_a]; rw [show -t+1=1-t from by ring] -- z norm sum
 have Hy:Leap W (Θ) S' a 2 1=ι t.toNNReal:=by unfold Leap; congr 1; simp [S',Hi,startX,endX,choice4,sites_r,p.zeroA,p.zeroB,top_a,←p.same_a]
 have Hz:Leap W (Θ) S' a 1 3=ι 1:=by unfold Leap; congr 1; simp [S',Hi,startX,endX,choice4,sites_r,p.front,p.zeroA]; -- need algebra
 let U':=actO W (Θ) (S (-t)); have H2: U' a 2=I a y B:=orbit_a W a L A B R _ _ _ _ p B (-t) -- tune arg
 change inner ℂ J ((U' a 0) (Leap W (Θ) S' a 0 2 (U' a 2 (Leap W (Θ) S' a 2 1 (U' a 1 (Leap W (Θ) S' a 1 3 (U' a 3 J))))))) = _; rw [Hx,Hy,Hz,H2]; rfl
structure WaveK(t:ℝ) : Prop where
 halo : L.t b+x b < o b-A.t b -- behind, no motion x
 soil : t ≤ y b-(B.t b)-(o b+A.t b)
 wake : t ≤ z b-(R.t b)-(y b+B.t b)
variable (s:ℝ)(g:0< s)(q: WaveK b L A B R o y x z s) (hw:b≠a)
omit p
lemma jeer_other (v:a≠ b): jeer a y t b=y b:=by simp [jeer,basis,v,v.symm]
include g q hw
lemma stare (t:ℝ) : List.Pairwise (Seers (Θ) (S t) b) [0,1,2,3]:=by
 simp [Seers,startX,endX,sites_r,choice4,jeer_other a b y t hw.symm]; obtain ⟨v,f,m⟩:=q; repeat' (first| apply And.intro | linarith [(B.t b).coe_nonneg,(A.t b).coe_nonneg])
omit g q
abbrev fieldQ (hw:b≠a) : Cross b:= Utah.Vac (a:=b) 1 a hw.symm
lemma field_v : ‖fieldQ a b hw‖=1:=by change ‖(1:ℝ) • basis a‖=1; simp
lemma leg_rook(t:ℝ): leg (W b) (t • basis a)=(W b).U (t • fieldQ a b hw):= by rw [←leg_sp]; apply congrArg; simp [fieldQ, Utah.Vac]
lemma orbit_b(t:ℝ):orbit_on W b (jeer a y t) B=(W b).U (t • fieldQ a b hw)*(orbit_on W b y B)*(W b).U (-t • fieldQ a b hw):=by rw [←leg_rook,←leg_rook]; change _= _; unfold orbit_on jeer; rw [add_comm,←opt_add]; unfold opt; rw [neg_smul] -- tune
-- *b utterance* from standing still be paid by Bowl
variable (k:ℝ)
abbrev Shade (i j:FHorizon) := Hi (Θ) (sites_r o y x z) b i j
local notation "J'" i:max j:max=> (W b).E (Shade b L A B R o y x z i j)
local notation "b'"=> (W b)
omit hw
def TranQ : (K b)→L[ℂ] ℂ:= (innerSL ℂ (Ω b)).comp ((I b x L)*(J' 0 1)*(I b o A))
-- shape record.F.Actor.Leak issue zero plank.I.
include hw
lemma bPaid(t:ℝ): chorus W Ω (Θ) (S t) [0,1,2,3] b=sideB (W b) (I b y B) (TranQ W Ω b L A B R o y x z) ((I b z R) (Ω b)) (Shade b L A B R o y x z 1 2) (Shade b L A B R o y x z 2 3) (fieldQ a b hw) t:=by
 let X(i j):= J' i j; let H0(i j):=Leap W (Θ) (S t) b i j; let hx(i j):=Shade b L A B R o y x z i j; have he : H0=X:=by
    funext i j; apply congrArg (W b).E; apply congrArg Real.toNNReal; unfold startX endX; have hp(i:FHorizon):((S t) i) b= (sites_r o y x z i) b:=by fin_cases i <;> first|rfl|exact jeer_other a b y t hw.symm
    simp_rw [hp]
 let U' :=actO W (Θ) (S t); have H2:U' b 2= (W b).U (t • fieldQ a b hw)*(orbit_on W b y B)*(W b).U (-t • fieldQ a b hw):= orbit_b ..
 change inner ℂ (Ω b) (U' b 0 (H0 0 1 (U' b 1 (H0 1 2 (U' b 2 (H0 2 3 (U' b 3 (Ω b)))))))) =_; rw [he,H2]; rfl
-- cross coherence criterion.
abbrev Cleaning (a b:Axis)(U:Set (Shrine K)) := ∀ (x: FHorizon→E4)(T₁ T₂:List FHorizon), T₁.Nodup→T₁.Perm T₂→∀ f:FHorizon→ Shrine K,(∀ i,f i∈ U)→ T₁.Pairwise (Seers f x a)→ T₂.Pairwise (Seers f x b)→ chorus W Ω f x T₁ a= chorus W Ω f x T₂ b
abbrev orbit_E (V:Shrine K)(t:ℝ):=(W a).edge t*I a o V*(W a).edge (-t) -- notation.I multiplication.
local notation "Y0" => (W a)
local notation "Jp"=> ((ι 1) (star (I a x L) J))
local notation "Q'"=> ((ι 1) ((I a z R) J))
-- instantiate.K.Store.Phys.Type.
variable (u':|t| < s) (V':Cleaning W Ω a b U) (v':Cinema (W b)) (w:∀ i,(choice4 L A B R) i∈U)
include p q g u' V' v' w
lemma boulder : inner ℂ (Jp) (((I a o A) * (orbit_E W a y B t)) (Q'))=inner ℂ (Jp) (((orbit_E W a y B t)*(I a o A)) (Q')) :=by
 let s₀:= Shade b L A B R o y x z; let W':= TranQ W Ω b L A B R o y x z; let Rp:List FHorizon:=[0,1,2,3]; let Rh:List FHorizon:=[0,2,1,3]
 have hT(j k:FHorizon)(p:s ≤ startX (Θ) (sites_r o y x z) b k- endX (Θ) (sites_r o y x z) b j): s ≤ (s₀ j k:ℝ) := p.trans (Real.le_coe_toNNReal _)
 refine torrent (W a) (W b) s (I a o A) (I a y B) (star (I a x L) J) ((I a z R) J) (I b y B) W' ((I b z R) (Ω b)) (s₀ 1 2) (s₀ 2 3) (fieldQ a b hw) v' (field_v ..).le (hT 1 2 q.soil) (hT 2 3 q.wake) g ?_ ?_ t u'
 · intro u e v; exact (bPaid W Ω a b L A B R o y x z hw u).symm.trans ((V' (S u) Rp Rp (by decide) (.refl _) _ w (dawn_p a L A B R o y x z p u e v) (stare a b L A B R o y x z s g q hw u)).symm.trans (dawnH W Ω a L A B R o y x z p u))
 intro u e v; exact (bPaid W Ω a b L A B R o y x z hw (-u)).symm.trans ((V' (S (-u)) Rh Rp (by decide) (List.Perm.cons 0 (List.Perm.swap ..)) _ w (dawn_r a L A B R o y x z p u e v) (stare a b L A B R o y x z s g q hw (-u))).symm.trans (duskB W Ω a L A B R o y x z p u))
#print axioms boulder
end Land
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
