import YM.SU5.FiniteGaugeData.Signal.GasJet
import YM.CF.Buffered.Duels
/-! Geometric compatibility PACKING MANY simultaneous insertions
 projected annihilators (both types) at once --- scales H^-1 in relative height, paying the
 exponential-in-full-volume ratio bill by high operator density tests at each fixed
 supported tile. This lemma lets us propagate that interpretation within existing RP
 orientation-even cone. Does NOT assert RP WITH non-Euclidean/odd extras. -/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal.Furnace
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Scree Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ContDiff ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
open Phase Spire
variable {n:Type*}[LinearOrder n][Fintype n]
variable {P P' X X':Op n}(h:IsStarProjection P)(q:TagG P X){H R c:ℝ}(p:0<H)
local notation "F" => transformed P X H
variable {S S' T: Finset n}{x y : FC n}
local notation "R↓"=> lineOp (cutM T)
namespace Spike
def lit (P X: Op n) (H c:ℝ) (x:FC n) := ‖transformed P X H x‖ ≤ c ∧ ∃ (a:ℂ)(v:Ket n)(b:Bool),x=a • creed b v
-- for input constructions
include h q p
lemma inferior {v:Ket n} [Nonempty n] (t:‖acts (upstairs P H*(1-X)) v‖ ≤ c): lit P X H c (create v):=by
 have he:= press_C h p q v -- include? later
 refine ⟨he ▸ ?_,1,v,false,by simp [Fock.creed]⟩; exact (Flare.cost_pe false _).trans t
lemma ignite (U:UNI n) (l:lit P X H c x)(h₁: twist U P=1-P')(h₂: X'= -(twist U (star X)))(hp':IsStarProjection P')(hq':TagG P' X'): lit P' X' H c (theta U x):=by
 obtain ⟨hc,a,v,_|_,rfl⟩:= l; all_goals
    have hC(U V:Op n)(u:ℝ)(t:ℂ)(x:FC n): transformed U V u (t • x)=t • transformed U V u x:=by simp [transformed,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
    rw [theta_smul]; let y:=acts U.val v
    have hi(k l:ℝ): twist U (burn P k l)=burn P' l k:=by rw [twisting,h₁]; unfold burn; rw [sub_sub_cancel,add_comm]
 · change lit _ _ _ _ (star a • theta U (create v))
   rw [theta_upV]; refine ⟨?_,(star a) * (-Complex.I),y,true,?_⟩; swap; · rw [smul_smul]; rfl
   have he : twist U (upstairs P H*(1-X))= downstairs P' H*(1+star X'):=by simp only [map_mul,map_sub,map_one, hi,h₂,star_neg,←map_star,star_star,←sub_eq_add_neg] -- map_smul?
   rw [hC,hC,press_D hp' p hq',←he, ←Fock.swivel]
   change ‖F (a • create v)‖ ≤ c at hc; rw [hC,press_C h p q] at hc; refine hc.trans' (le_of_eq ?_)
   rw [←theta_upV]; rw [←theta_smul,theta,twist_norm]; rw [norm_cc] -- names tune theta missed −i in inside alignment
 change lit _ _ _ _ (star a • theta U (remove v)); rw [theta_downV]; refine ⟨?_,(star a)*Complex.I,y,false,?_⟩; swap; · rw [smul_smul]; rfl
 have he : twist U (downstairs P H*(1+star X))= upstairs P' H*(1-X'):=by simp only [map_mul,map_add,map_one, hi,h₂, sub_neg_eq_add]
 rw [hC,hC,press_C hp' p hq',←he, ←Fock.swivel]; change ‖F (a • remove v)‖ ≤ c at hc; rw [hC,press_D h p q] at hc; refine hc.trans' (le_of_eq ?_); rw [←theta_downV,←theta_smul,theta,twist_norm,norm_cc]
end Spike

namespace Vine
-- parity existential. F is EVEN on registration.
def riveted (P X:Op n)(H c:ℝ)(S T:Finset n)(d:ℕ)(x:FC n):Prop:=∃ (L:List (FC n))(Z:FC n), L.length=d ∧ (∃ b:Bool,Sector S b Z) ∧ (∀ i∈L,Sector S true i ∧ Spike.lit P X H c i)∧‖Z‖≤1 ∧ (lineOp (cutM T)) * x = lineOp (cutM T)*(Z* L.prod)
lemma grow {d:ℕ}(l:riveted P X H c S T d x)(e:S⊆S'):riveted P X H c S' T d x:=by
 obtain ⟨L,Z,z,⟨b,x⟩,u,y,v⟩:=l
 exact ⟨L,Z,z,⟨b, Buffered.Cin.widen e x⟩, fun i v=>⟨Buffered.Cin.widen e (u i v).1,(u i v).2⟩,y,v⟩
lemma parityOf (L: List (FC n))(p:∀ i∈L, Sector S true i): ∃ b,Sector S b L.prod:=by
 induction L with
 | nil=> exact ⟨false,Sector.one⟩
 | cons i L ih=> obtain ⟨b,d⟩:= ih (fun i v=>p i (List.mem_cons_of_mem _ v)); exact ⟨_,(p _ List.mem_cons_self).mul d⟩
lemma addOn {d d':ℕ}(p:riveted P X H c S T d x)(q:riveted P X H c S' T d' y)(w:Disjoint S S')(f:Sector S false x)(g:Sector S' false y): riveted P X H c (S∪S') T (d+d') (x*y):=by
 obtain ⟨L,Z,z,⟨b,pZ⟩,u,y0,v⟩:= p
 obtain ⟨M,Z',z',⟨k,pZ'⟩,u',y1,v'⟩:= q
 obtain ⟨i,wL⟩:= parityOf L (fun i h=> (u i h).1); obtain ⟨j,wM⟩:= parityOf M (fun i h=> (u' i h).1)
 let t:= Sector.grainB j b; let y':= t • (Z'*Z); refine ⟨M++L,y',by simp [z,z',add_comm], ⟨_,((Buffered.Cin.widen subset_union_right pZ').mul (Buffered.Cin.widen subset_union_left pZ)).scale _⟩,?_,?_,?_⟩ -- use wL parity
 · intro i a; rcases List.mem_append.mp a with a|a
   · exact ⟨Buffered.Cin.widen subset_union_right (u' i a).1,(u' i a).2⟩
   exact ⟨Buffered.Cin.widen subset_union_left (u i a).1,(u i a).2⟩
 · rw [norm_smul,show ‖t‖=1 by unfold t Sector.grainB; split <;> simp,one_mul]; exact (norm_mul_le ..).trans ((mul_le_mul y1 y0 (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
 rw [←mul_assoc,v]; have he: (Z*L.prod)*y=y*(Z*L.prod):=by simpa only [Sector.grainB,Bool.and_false, Bool.false_eq_true,ite_false,one_smul] using Sector.apart (pZ.mul wL) g w
 rw [mul_assoc,he,←mul_assoc,v',mul_assoc]; have hk : M.prod*Z=t • (Z * M.prod):= Sector.apart wM pZ w.symm
 rw [List.prod_append]; apply congrArg; calc Z' * M.prod * (Z * L.prod)= Z'*(M.prod*Z)*L.prod:=by noncomm_ring
                                             _ = _:= by rw [hk]; unfold y'; simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, mul_assoc]

lemma lantern (U:UNI n)(p: twist U (cutM Tᶜ) = cutM T) : theta U (lineOp (cutM T))=lineOp (cutM T):=by
 rw [cutLine]; have he : (star (cutM {T}))=(cutM {T}) := (cutM_idp ..).isSelfAdjoint
 have hc : cc (cutM {T})=cutM {T} := by unfold cc; rw [he]; simp [cutM]
 rw [theta,hc,screenM,Fock.twin,leaves,←cutLine,← line_twist, invFilm,Fock.twin,p,rankPhase, cutLine]
include h p q
lemma reflectSegments {d:ℕ} (l:riveted P X H c S T d x)(U:UNI n)(hX:twist U (cutM Tᶜ)=cutM T)(hy:twist U (cutM S)=cutM S')(h₁: twist U P=1-P')(h₂:X'= -(twist U (star X)))(v:IsStarProjection P')(t:TagG P' X'): riveted P' X' H c S' T d (theta U x):=by
 obtain ⟨L,Z,d,⟨b,hZ⟩,pZ,hg,w⟩:= l
 refine ⟨L.map (theta U),theta U Z,by simp [d],⟨b,theta_carries U hZ hy⟩,fun i hc=>?_, (le_of_eq ?_).trans hg,?_⟩
 · obtain ⟨a,e,rfl⟩:= List.mem_map.mp hc
   exact ⟨theta_carries U (pZ _ e).1 hy, Spike.ignite h q p U (pZ _ e).2 h₁ h₂ v t⟩
 · rw [theta,twist_norm,norm_cc]
 have hk (L:List (FC n)): (L.map (theta U)).prod=theta U L.prod:=by induction L with| nil=> simp [theta_one]| cons i L h=> simp [theta_mul,h]
 rw [hk,←theta_mul,← lantern U hX,←theta_mul,←theta_mul,w]

variable [Nonempty n]
lemma burn_ten {d:ℕ}(g:riveted P X H c S T d x){v z:Wave n}(l:Sea P v)(w:Sea (cutM T) z)(b:1≤H)(e:H≤R)(f f':ribbon n)(u:0≤c):
    ‖inner ℂ z (acts x (acts (tank P (exp f*f') * exp (dg X)) v))‖ ≤ ‖exp (dg X)‖ * Real.exp (tier R f.val) * tier R f'.val * c^d:=by
 obtain ⟨L,Z,r,_,hq,hy,ht⟩:= g
 let p':= tank P (exp f*f')*exp (dg X); let A:= acts p' v; have he(y:Wave n):inner ℂ z y=inner ℂ z (acts (lineOp (cutM T)) y):=by
    nth_rw 1 [←w.1]; rw [←act_inner,(line_proj (cutM_idp _)).isSelfAdjoint]
 rw [he,←act_mul,ht,act_mul,←he] -- name z wrong
 rw [act_mul,←act_mul L.prod]; apply (norm_inner_le_norm ..).trans; rw [w.2,one_mul]
 apply (Graph.spentS n Z _).trans; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) hy)
 simpa [r] using spotlight h p q l b e f f' id L (fun i v=> (hq i v).2.1) u -- args simplify mul_assoc
end Vine
end YM.CF.Signal.Furnace
#print axioms YM.CF.Signal.Furnace.Vine.burn_ten
#print axioms YM.CF.Signal.Furnace.Vine.addOn
#print axioms YM.CF.Signal.Furnace.Vine.reflectSegments
