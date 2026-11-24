import YM.SU5.Reconstruction.Hygrometry.Landing
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Mir Reflect Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open PriceCliff
variable {α : Type*}
namespace Windward
variable (P:Ramp)
local notation "a"=> P.a
local notation "b"=> P.b
def share :ℝ:=(Real.sqrt 2)⁻¹
local notation "γ"=>share
private lemma price_pos: 0<share:=by unfold share; positivity
lemma doubleCost: share *share=1/2:=by
 unfold share; rw [show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (Real.sqrt 2 * Real.sqrt 2)⁻¹ from (mul_inv_rev ..).symm, Real.mul_self_sqrt (by norm_num), one_div]
noncomputable def survey (P:Ramp)(x:Gaia): Gaia:= WithLp.toLp 2 (fun i=>if i=P.a then γ*(x P.a+x P.b) else if i=P.b then γ*(-x P.a+x P.b) else x i)
lemma head (x:Gaia): survey P x a= γ*(x a+x b):=by simp [survey]
lemma taste (x:Gaia): survey P x b=γ*(-x a+x b):=by simp [survey,P.cross]
lemma no_change (x:Gaia){i:Axis}(u:i≠P.a)(v:i≠P.b):survey P x i=x i:=by simp [survey,u,v]
lemma face (x:Gaia)(p:face_tilt P x): face_axis a (survey P x):=by unfold face_axis; rw [head]; exact mul_pos price_pos p
lemma transit (x y:Gaia): survey P (x-y)=survey P x-survey P y:=by
 apply PiLp.ext; intro i; by_cases u:i=P.a; · subst i; simp [survey,mul_add]; ring --
 by_cases v:i=P.b; · subst i; simp [survey,P.cross,mul_add]; ring
 simp [survey,u,v]
lemma chronod (x:Gaia): land_axis a (survey P x)=survey P (land_tilt P x):=by
 apply PiLp.ext; intro i; by_cases u:i=P.a
 · subst i; change (if a=a then -(survey P x a) else _)=survey P (land_tilt P x) a; rw [if_pos rfl, head,head] -- noop
   change _= γ*(P.s.act x.ofLp P.a+ P.s.act x.ofLp P.b); rw [P.move_a,P.move_b]; ring
 change (if i=a then -(survey P x i) else survey P x i)=survey P (land_tilt P x) i; rw [if_neg u]
 by_cases v:i=P.b
 · subst i; rw [taste,taste]; change _ = γ*(-(P.s.act x.ofLp P.a)+ P.s.act x.ofLp P.b); rw [P.move_a,P.move_b]; ring
 rw [no_change P x u v,no_change P _ u v]; exact (P.move_h x.ofLp u v).symm
-- decompose sums. consistent orientation AB order
lemma tot {X:Type*}[AddCommMonoid X](f:Axis→ X): ∑ i,f i=f a + f b + ∑ i∈ ((Finset.univ.erase a).erase b),f i:=by
 have he:= add_sum_erase _ f (show b∈ (Finset.univ.erase a) from Finset.mem_erase.mpr ⟨P.cross, mem_univ _⟩)
 rw [← add_sum_erase _ f (Finset.mem_univ P.a), ← he, add_assoc]
lemma meters (x:Gaia): ‖survey P x‖=‖x‖:=by
 apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : (2:ℕ)≠0)).mp
 rw [← Stationary.geode_sum, ← Stationary.geode_sum]; rw [tot P (fun i=> _), tot P (fun i=> (x i)^2), head, taste, sum_congr rfl (show ∀ i∈ ((Finset.univ.erase a).erase b), (survey P x i)^2=x i^2 from fun i t=> by rw [no_change P x (mem_erase.mp (mem_erase.mp t).2).1 (mem_erase.mp t).1])]; congr 1; rw [mul_pow,mul_pow, sq γ,doubleCost]; ring
local notation "A"=> gammaOp a
local notation "B"=> gammaOp b
local notation "G"=> Op SpinIdx
private abbrev joinSpin (P:Ramp) := gammaOp P.a*gammaOp P.b
def radiusS (P:Ramp):Op SpinIdx:=(1+γ:ℝ) • (1:Op SpinIdx) + γ • joinSpin P -- 1+ gamma_n
private lemma ab : gammaOp b*gammaOp a= -joinSpin P:= gammaSwap b a P.cross
private lemma skewJ : star (joinSpin P)= -joinSpin P:=by unfold joinSpin; rw [star_mul,(gammaAdj b).star_eq,(gammaAdj a).star_eq, ab]
local notation "J"=> joinSpin P
private lemma aj:A*J=B:=by rw [joinSpin,←mul_assoc,gammaOne,one_mul]
private lemma ja:J*A= -B:=by rw [joinSpin, mul_assoc,ab,mul_neg,aj]
private lemma jb:J*B=A:=by rw [joinSpin,mul_assoc,gammaOne,mul_one]
private lemma bj:B*J= -A:=by rw [joinSpin,←mul_assoc,ab,neg_mul,jb]
private lemma jj:J*J= -1:=by nth_rw 2 [joinSpin]; rw [←mul_assoc,ja,neg_mul,gammaOne]
def pinCost:ℝ:=Real.sqrt ((2+2*share)⁻¹)
private lemma accountS: pinCost* (pinCost*(2+2*share))=1:=by unfold pinCost; have h:0<share:=price_pos; rw [←mul_assoc,Real.mul_self_sqrt (by positivity),inv_mul_cancel₀ (by positivity)]
private lemma rotorU : (γ*γ+(1+γ)*(1+γ))=2+2*γ:=by nlinarith [doubleCost]
lemma radialW: radiusS P*star (radiusS P)= (2+2*share) • (1:G):=by
 rw [radiusS,star_add,star_smul, star_smul,star_one, skewJ]; simp only [star_trivial, add_mul,mul_add,Matrix.smul_mul, Matrix.mul_smul,one_mul, mul_neg, mul_one,jj, smul_neg, ← rotorU]
 module
noncomputable def vestib(P:Ramp): UNI SpinIdx:= ⟨pinCost • radiusS P, Matrix.mem_unitaryGroup_iff.mpr (by change (_ • radiusS P)*star _=1; rw [star_smul,star_trivial,Matrix.smul_mul,Matrix.mul_smul, radialW,smul_smul,smul_smul,mul_assoc,accountS];exact one_smul ..)⟩
private lemma aj_ratio: γ^2+(γ*(1+γ))=1+γ:=by rw [sq,doubleCost]; nlinarith [doubleCost]
lemma radius_a: radiusS P * A = (γ • A - γ • B)*radiusS P :=by
 rw [radiusS, add_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul,ja, sub_mul,mul_add,mul_add]; simp only [Matrix.smul_mul,Matrix.mul_smul,aj,bj,mul_one,smul_neg,smul_smul]; rw [doubleCost];
 have he:γ*(1+γ)=γ+1/2:=by rw [mul_add,mul_one,doubleCost]
 simp only [mul_comm (1+γ) γ,he]; module
lemma radius_b: radiusS P * B= (γ • A + γ • B)* radiusS P:=by
 simp only [radiusS, add_mul,mul_add,Matrix.smul_mul, Matrix.mul_smul,jb,bj,aj,one_mul,mul_one,smul_neg,smul_smul]; rw [doubleCost]; have he:γ*(1+γ)=γ+1/2:=by rw [mul_add,mul_one,doubleCost]
 module
lemma twist_a : twist (vestib P) A=γ • A-γ • B:=by
 apply twist_comm; change (pinCost • _)*_=_*(pinCost • _); rw [Matrix.smul_mul,Matrix.mul_smul,radius_a]
lemma twist_b : twist (vestib P) B=γ • A+γ • B:=by
 apply twist_comm; change (pinCost • _)*_=_*(pinCost • _); rw [Matrix.smul_mul,Matrix.mul_smul,radius_b]
lemma twin{T:G}(u:A*T= -(T*A))(v:B*T= -(T*B)): twist (vestib P) T=T:=by
 apply twist_comm; change (pinCost • radiusS P)*_=_*(pinCost • _); rw [Matrix.smul_mul,Matrix.mul_smul,radiusS]; unfold joinSpin; simp only [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul]; rw [mul_one,one_mul,mul_assoc,v,mul_neg, ←mul_assoc,u,neg_mul,neg_neg,mul_assoc]
lemma twist_tall : twist (vestib P) grading=grading:=twin P (by rw [gradingSwap,neg_neg]) (by rw [gradingSwap,neg_neg])
lemma twist_basis {x:Axis}(u:x≠P.a)(v:x≠P.b): twist (vestib P) (gammaOp x)=gammaOp x:=twin P (gammaSwap a x u.symm) (gammaSwap b x v.symm)
lemma earns_pin : twist (vestib P) P.imageP=pin a:=by
 change twist (vestib P) (γ • _)=_; rw [map_smul]; simp only [map_add,pin,map_mul,twist_a,twist_tall,twist_b, sub_mul, add_mul,Matrix.smul_mul]
 simp only [smul_add, smul_sub γ, smul_smul,doubleCost]; module
lemma earnsA : twist (vestib P) Aop= Aop:= by rw [Adef,twist_scalar,map_add,map_one,twist_tall]
local notation "Gκ"=> vestib P
lemma twist_pen (x:Gaia) : pencil (survey P x) = twist (vestib P) (pencil x) := by
 unfold pencil gleamV minA; rw [map_smul, map_mul,map_sub,map_one,earnsA,meters,map_sum]; simp_rw [twist_scalar]; congr 2 -- tune
 rw [tot P (fun i=> ((survey P x i):ℂ) • _), tot P (fun i=>(x i:ℂ) • _), head,taste,twist_a,twist_b, sum_congr rfl (show ∀ i∈ ((Finset.univ.erase a).erase b), (survey P x i:ℂ) • gammaOp i=(x i:ℂ) • twist (vestib P) (gammaOp i) from fun i h=> by have hv:=(mem_erase.mp (mem_erase.mp h).2).1; have ht:=(mem_erase.mp h).1; rw [no_change P x hv ht, twist_basis P hv ht])]
 simp only [BZ.ofReal_action]; module
noncomputable def equip (P:Ramp)(x:Personality): Personality where
 down:=x.down
 voice:=acts (vestib P).val x.voice
 color:=x.color
 signed:= by
    unfold remains; nth_rw 1 [← earnsA P]; rw [←Fock.swivel,show acts Aop x.voice=_ from x.signed]; split <;> simp_all
lemma cross_turn (x:Personality): (applaud a).role (equip P x)=equip P ((whisper P).role x):=by
 have he:= earns_pin P
 have hh: acts (pin a) (acts (Gκ).val x.voice)=acts (Gκ).val (acts P.imageP x.voice):=by rw [←he,Fock.swivel] -- tune
 unfold ActMark.role equip impel; congr 1
lemma toward_next (x:Gaia)(s t:Personality): toward (survey P x) (equip P s) (equip P t)=toward x s t:=by
 unfold toward equip; dsimp only; rw [twist_pen, ← Fock.swivel,act_unit_inner]
lemma glow (x y:Gaia)(s t:Personality): poster (survey P x) (survey P y) (equip P s) (equip P t)=poster x y s t:=by change (if s.down=t.down then _ else if s.down then toward _ _ _ else -toward (survey P y-survey P x) (equip P t) (equip P s))=_; rw [←transit P x,←transit P y,toward_next,toward_next]; rfl
lemma ticket(x:α→Gaia)(t:α→Personality)(Z:List α): quantum (survey P ∘ x) (equip P ∘ t) Z=quantum x t Z:=by unfold quantum; simp only [comp_apply,glow]
end Windward
end YM.CF.Hygrometry
