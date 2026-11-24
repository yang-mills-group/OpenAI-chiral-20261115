import Merino.Coin.Blush
import SatinThinWarp

set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Coin
open Function Finset Lattice Cube RG Scree Skye Fock
open scoped Topology Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Py Roots QuadClock Oise Mew Neon Waxy
open Vow TreasuryFog Dial Paige Vault
open scoped YM.CF.Mew
open NormedSpace Spire Stax Tulip
attribute [local instance] opCStarAlgebra
open Py Rate LocalLimit Preparation Yoke
open Next SectorNext.Remainder Graph
open Buffered Afterglow Vale Pressure Pressure.Worth Journey Scales
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable {I:Type}[Fintype I][LinearOrder I] {n:Side}
open MeasureTheory Papyrus Papyrus.Franc
open scoped InnerProductSpace

lemma cupboard {h d b v:ℝ}(R:GramM n)(H:MarketR R h d)(t:0≤h){U:RegBudget n}{F:ForceBudget n}
    (u:Pavilion (cream R.p) h v b U F):
    Graph.MarketR (pertain R (R.F+U) R.slip (R.K+F)) h (d+2*(b+v*sites n)):=by
 obtain ⟨x,A,y,Z,rfl,rfl,hx,hy,hA,hZ⟩:=u.pay
 obtain ⟨i,j,k,e,f,g,r⟩:=H
 have p:FixedE R.p h (b + v*sites n) (x+A):=by
     obtain ⟨c,q,w⟩:=(fixed_uniteE hx (fixedFromE hA t)).pay
     exact ⟨c,fun i=>lessE.mpr (q i),w⟩
 have vp:FixedF R.p h (b + v*sites n) (y+Z):=by
     obtain ⟨c,q,w⟩:=(fixed_uniteF hy (fixedFromF hZ t)).pay
     exact ⟨c,fun i=>lessF.mpr (q i),w⟩
 exact ⟨_,_,_,fixed_uniteE e p,f,fixed_uniteF g vp,by linarith only [r]⟩
section
variable {N B:Side}(X:GramM (mid N B))(p:I→Site (mid N B)){E:Key I→RegBudget (mid N B)}{F:Key I→ForceBudget (mid N B)}
    {K:Teller SU.group}{L:Precision.ChartRatio SU.group}
    {R:Patch}(V:Grace K R L){d:ℝ}(P_:Grasp V.U B d)(Lo:Scree.Loom (mid N B))

open Rive 
lemma chleap (a:Notice p E F)
 (x:Orbit (mid N B))(U:Key I→Key I)(u:Differentiable ℂ U): River ((serum P_ X Lo E F x) ∘ U):=by
 let A':Key I→RegBudget (mid N B):= fun z=>X.F+E (U z); let F':Key I→ForceBudget (mid N B):=fun z=>X.K+ F (U z); let T':= fun _:Key I=>X.slip; let ℓ: I→Unit:=fun _=>()
 have hp {C: Type}[NormedAddCommGroup C][NormedSpace ℂ C][CompleteSpace C]{f:Key I→C}(p: River f): Law_C ℓ 0 [] f f:= ⟨p,p,fun i u=>by rw [List.sublist_nil.mp u]; rfl⟩
 refine (pulse_H V ℓ 0 [] (by simp [ψS]) X Lo A' A' T' T' F' F' (fun _=>X.v) (fun _=>X.v) x (fun i h=>hp ?_) (fun i x=>hp ?_) (fun i x=>hp ?_) (hp (zeroR _))).1
 · exact dub_V (zeroR (X.F _ _)) (river_all (fun z=>E (U z) i h) ((a.varE _ _).comp u)) -- needs explic
 · exact zeroR _
 exact dub_V (zeroR (X.K _ _)) (river_all (fun z=>F (U z) i x) ((a.varF _ _).comp u))
end


variable (s i k:ℕ)
abbrev fuelled (b:ℝ)
 (E:Key I→RegBudget (side Y i s))(F:Key I→ForceBudget (side Y i s)) :Prop:=
   PanoramaBill (cream (RootBook Y i k s).p) P.h (2*b⁻¹) (slotFee P s) 2 E F
-- Based on SatinThinCourt.actual_late_wager, SatinThinWarp.warped
lemma gamb
    (b v:ℝ) (p:s≤Y.uv k)(c:MarketCost v Y s i k)(E:Key I→RegBudget (side Y i s))(F:Key I→ForceBudget (side Y i s))(u:fuelled Y s i k b E F): let G:=RootBook Y i k s; let f:= (Y.voyage i).CapeT s; let n:=side Y i s;
 let q:=slotFee P s; let C₀:=3*dleaf P.R.L (hat P.R.L P.x s)*sites n
 ∀ x:Key I,(∀ j, ‖x j‖≤2*b⁻¹) →∀ (w:Orbit (side Y i s))(g:Seat (side Y i s)→SU.E), ‖beamZ _ (serum P.U G f E F w x)‖ ≤ Real.exp (G.v.re + (C₀+2*(2*Fintype.card I+q*sites n))+ Cascade.angleFin G.J.M n P.K.j+ v*metroStress P.K.j G f w g) * Graph.past G w.1:= by
 intro G f n q C₀ x hx w g
 let z:= C₀+2*(2*Fintype.card I+q*sites n)
 let R:= pertain G (G.F+E x) G.slip (G.K+F x)
 have ht:MarketR R P.h z:=cupboard G (existingMarket Y s i k p) (zero_le_one.trans P.height) (u x hx)
 have hp := c.buys z (G.F+E x) G.slip (G.K+F x) ht w g
 let S':= Scree.denZ R P.U f w
 let W:= z+ Cascade.angleFin G.J.M n P.K.j+ v*metroStress P.K.j G f w g
 let N:ℝ:= Graph.past G w.1
 change ‖beamZ n (Complex.exp (-G.v) • S')‖ ≤ N * Real.exp W at hp; change ‖beamZ n S'‖ ≤ _
 have hh: Real.exp (-G.v.re) * ‖beamZ n S'‖ ≤ N * Real.exp W := by simpa only [Scree.beamZ,inner_smul_right,norm_mul,Complex.norm_exp,Complex.neg_re] using hp
 have hz:= mul_le_mul_of_nonneg_left hh (Real.exp_pos G.v.re).le; rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] at hz; refine hz.trans_eq ?_; rw [show G.v.re+z+_+_=G.v.re+W from (by unfold W; ring), Real.exp_add G.v.re W]; change _ = _ * N; ring


variable {c b:ℝ}(R:ShelterCost c Y s i k)(hb:0<b)
open Rive Pannier
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "Ω"=> side Y i s
local notation "G0"=> RootBook Y i k s
local notation "K0"=> (Y.voyage i).CapeT s
include R hb

lemma warps (wb:b≤1)(E:Key I→RegBudget (side Y i s))(F:Key I→ForceBudget (side Y i s))(p:fuelled Y s i k b E F) (o:I→Site (side Y i s))(q:Notice o E F)(l:List I)(u:Orbit (side Y i s)):
 ‖beamZ (side Y i s) (tipI (serum P.U G0 K0 E F u) l)‖ ≤ b^l.length*(Real.exp (glowRise Y 1 s i k (Fintype.card I))*shadeY Y s i k 0 (gateC (hat L P.x s)) u):=by
 let G:=G0; let N:=side Y i s; let F':=serum P.U G K0 E F u; let g:= atFrame Y s i u
 let f:= innerSL ℂ (mateK N) ∘ F'; let w:=glowRise Y 1 s i k (Fintype.card I); let X:=hat L P.x s; let V:=gateC X; let Y':= flakes (shieldC X) u.1
 have hx: River F' := chleap G o P.V P.U K0 q u id differentiable_id
 let K:=sites N; let a:=Cascade.angleFin G.J.M N D; let h:=meterC X; let d:=G.path.inChannels G.funds G.p G.beta u.1
 let U:=slotFee P s; obtain ⟨_,p1,v1,v2,v3⟩:=R.load.health
 change ‖beamZ _ (tipI F' l)‖≤_; rw [show beamZ _ _=tipI f l from (sim_H hx (innerSL ℂ (mateK N)) l roots).symm]
 apply vigor_bound hb wb l; · intro c; exact (sc_V (chleap G o P.V P.U K0 q u _ (differentiable_id.const_smul c)) (innerSL ℂ (mateK N)): River (f ∘ lensShift _ c)) -- tune implicit named
 intro x hM
 apply (gamb Y s i k b c R.load.paid R.pose E F p x hM u g).trans; change Real.exp _ *Graph.past G u.1 ≤ Real.exp w* Real.exp (-d+ 0* _+V*Y'); rw [zero_mul,add_zero,←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
 let f':ℝ:= Fintype.card I; let W:=metroStress D G K0 u g; let L':= dleaf L X
 have hu: c*W ≤ h*K + V*Y' := R.effort u; change G.v.re+(3*L'*K+2*(2*f'+U*K))+a+c*W+(-d)≤ (4*1*f'+6*h*K+a+G.v.re)+ _
 have hz:U≤h:=v2; have hp:L'≤h:=p1; have hK:0≤K:=zero_le_one.trans (sites_pos _); nlinarith only [hu,mul_le_mul_of_nonneg_right hz hK,mul_le_mul_of_nonneg_right hp hK]

/-- f generalizing steamRent -/
abbrev aroma (P:Preparation)(b:ℝ)(s:ℕ)(n:Side)(t j:ℕ):ℝ:=
 b^j * Real.exp (4 * (1:ℝ)*t+14*meterC (hat P.R.L P.x s)*sites n)

lemma invoice (wb:b≤1)(E:Key I→RegBudget (side Y i s))(F:Key I→ForceBudget (side Y i s))(p:fuelled Y s i k b E F)(o:I→Site (side Y i s))(q:Notice o E F)(l:List I)
    (t:Integrable (fun x=> beamZ (side Y i s) (tipI (serum P.U G0 K0 E F x) l)) (city _)):
    ‖(∫ x:Orbit (side Y i s), beamZ (side Y i s) (tipI (serum P.U G0 K0 E F x) l)∂city _)/coined Y i k s‖ ≤ aroma P b s Ω (Fintype.card I) l.length:=by
 let G:= G0; let N:=side Y i s; let K:= sites N; let h:= meterC (hat L P.x s); let g:=glowRise Y 1 s i k (Fintype.card I); let B':= b ^ l.length; let d:= Papal.gBaseR Y s i k; let C':ℝ:= d+7*h*K; let Ψ:= Cascade.angleFin G.J.M N D; let ε':= G.v.re; let v:= Scales.merit P.R.L (hat L P.x s); let F':=(fun x=> beamZ (side Y i s) (tipI (serum P.U G0 K0 E F x) l)); let D':=shadeY Y s i k 0 (gateC (hat L P.x s)); let Q:=‖coined Y i k s‖
 have hD:=R.load.vast; simp only [VLine,compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at hD; change Real.exp (d+Ψ-v*K)≤ Real.exp (-ε') * Q at hD -- tune
 have hx: 0<Q:= by by_contra! hv; exact (Real.exp_pos _|>.not_ge) (hD.trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _|>.le) hv))
 obtain ⟨hz,he⟩:= shade_prior Y R.load R.load.ready R.load.willing
 rw [norm_div,div_le_iff₀ hx]; have hB': 0≤B':= pow_nonneg (hb.le) _
 apply le_trans (norm_integral_le_integral_norm F'); apply le_trans (integral_mono (μ:=city (side Y i s)) t.norm ((hz.const_mul _).const_mul _) (show ∀ U, ‖F' U‖≤ B'*(Real.exp g*D' U) from warps Y s i k R hb wb E F p o q l))
 rw [integral_const_mul,integral_const_mul]; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (Real.exp_pos _|>.le)) hB') ?_
 let A':=4*(1:ℝ)*Fintype.card I; let w:=A'+14*h*K; change B'*(Real.exp g*Real.exp C')≤ B'*Real.exp w*Q; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hB'
 rw [show w=(w+ε')+(-ε') from (by ring), Real.exp_add (w+_ ), mul_assoc]; refine le_trans ?_ (mul_le_mul_of_nonneg_left hD (Real.exp_pos _|>.le)); rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; have hv:v≤h:=R.load.health.1; change A'+6*h*K+Ψ+ε'+ C' ≤ _; unfold C' w; nlinarith only [mul_le_mul_of_nonneg_right hv (show 0≤K from zero_le_one.trans (sites_pos _))]


end YM.CF.Merino.Coin
