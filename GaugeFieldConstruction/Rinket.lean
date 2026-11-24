import GaugeFieldConstruction.Fillet
import YM.CF.Moto.Thistle
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Work.F03
open Housing ModuleB Flot
namespace HushP
open Pastry Haro
section
variable {E F G V:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G][NormedAddCommGroup V][NormedSpace ℝ V]
local notation "r" => ((↑(2:ℕ)): ℕ∞ω)
set_option maxHeartbeats 80000 in
lemma hessian_B (f:E→ F)(g:E→G)(i j x:E)(A:F→L[ℝ] (G→L[ℝ]V))(p:ContDiffAt ℝ r f x)(q:ContDiffAt ℝ r g x)(v:f x=0)(t:g x=0): let C (y):=A (f y) (g y)
 iteratedFDeriv ℝ 2 C x ![i,j]= A (fderiv ℝ f x i) (fderiv ℝ g x j)+A (fderiv ℝ f x j) (fderiv ℝ g x i):=by
 intro C; rw [iteratedFDeriv_two_apply]; let H(E₀:E→L[ℝ]V):= E₀ j; let X(y):= H (fderiv ℝ C y)
 let W(y):= A (fderiv ℝ f y j) (g y); let Z(y):= A (f y) (fderiv ℝ g y j)
 have he : X=ᶠ[𝓝 x] W+Z:=by
    filter_upwards [p.eventually (by norm_num), q.eventually (by norm_num)] with y p q; have ht:=(p.differentiableAt (by norm_num)).hasFDerivAt; have hu:=(q.differentiableAt (by norm_num)).hasFDerivAt; unfold X; rw [show fderiv ℝ C y=_ from ((A.hasFDerivAt.comp y ht).clm_apply hu).fderiv]; first | exact add_comm .. | rfl -- may order
 have hC: ContDiffAt ℝ r C x:= (A.contDiff.contDiffAt.comp x p).clm_apply q
 let L:= ContinuousLinearMap.apply ℝ V j
 let LG:= ContinuousLinearMap.apply ℝ G j; let LF:= ContinuousLinearMap.apply ℝ F j
 let Γf:= (p.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num); let Γg:= (q.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
 have hf:= ((A.hasFDerivAt.comp x (LF.hasFDerivAt.comp x Γf.hasFDerivAt)).clm_apply (q.differentiableAt (by norm_num)).hasFDerivAt).add ((A.hasFDerivAt.comp x (p.differentiableAt (by norm_num)).hasFDerivAt).clm_apply (LG.hasFDerivAt.comp x Γg.hasFDerivAt)); have hX:fderiv ℝ X x=L ∘L fderiv ℝ (fderiv ℝ C) x:= (L.hasFDerivAt.comp x ((hC.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt).fderiv; change (L ∘L _ ) _ = _; rw [←hX, he.fderiv_eq, show fderiv ℝ (W+Z) x= _ from hf.fderiv]
 -- simp
 simp only [_root_.add_apply,ContinuousLinearMap.comp_apply, Function.comp_apply,ContinuousLinearMap.apply_apply,v,t,map_zero, ContinuousLinearMap.zero_apply, add_zero,zero_add]; exact add_comm .. 
end
abbrev ζedge(i:GateI):rowS:= creditCue (Pi.single i 1)
def bloomT (L:leadF Gem Gem)(J:leadF Gem Sut):leadF rowS rowS:=by
 let f:=ContinuousLinearMap.fst ℝ Gem Sut; let g:=ContinuousLinearMap.snd ℝ Gem Sut; let X:= (((L.comp f).flip).comp f).flip; let Y:= (((J.comp f).flip).comp g).flip
 exact X+(Y+Y.flip)
lemma bloom_apply(L:leadF Gem Gem)(J:leadF Gem Sut)(i j:rowS): bloomT L J i j= L i.1 j.1+(J i.1 j.2+ J j.1 i.2):=rfl
lemma bloom_r(L:leadF Gem Gem)(v:L.flip=L)(J:leadF Gem Sut)(i j:rowS):bloomT L J i j=bloomT L J j i:=by rw [bloom_apply, bloom_apply,show L i.1 j.1=L j.1 i.1 from DFunLike.congr_fun (DFunLike.congr_fun v j.1) i.1,add_comm (J i.1 j.2)]
abbrev monover (a:ℂ): leadF SU.group.Color SU.group.Color := by
 let Q:= ContinuousLinearMap.compL ℝ SU.group.Color ℝ ℂ Complex.ofRealCLM; exact a • (Q.comp (innerSL ℝ)) -- tune
lemma mono_apply(a:ℂ)(x y:SU.group.Color): monover a x y=a*↑(inner ℝ x y):=rfl
abbrev Tickets := GateI × GateI
def ψTile (o:Skye.Seat n)(p:BudgetPoint)(b:Tickets)(a:ℂ)(x:Pane n) := monover a (πon o b.1 p x) (πon o b.2 p x)
abbrev νt (o:Skye.Seat n)(p:BudgetPoint)(Z:leadF rowS rowS)(i j:GateI):= (1/2:ℂ)*Z (ζedge i) (ζedge j)
def terrace (o:Skye.Seat n)(p:BudgetPoint)(Z:leadF rowS rowS)(x:Pane n) :=∑ i:Tickets,ψTile o p i (νt o p Z i.1 i.2) x
lemma ψTax (p:BudgetPoint)(Z:leadF rowS rowS)(o:Skye.Seat n): GaugeInvariant (terrace o p Z):=by intro k u; unfold terrace; apply sum_congr rfl; intro i _; unfold ψTile; rw [πGauge,πGauge,mono_apply,mono_apply,StressFlux.inner_adjoint]
lemma ψ_flat(p:BudgetPoint)(Z:leadF rowS rowS): terrace o p Z 1=0:=by unfold terrace ψTile; simp only [π_flat,mono_apply,inner_zero_right,Complex.ofReal_zero,mul_zero,sum_const_zero]
lemma merc (X: rowS) :∑ i:GateI, (cue X i) • ζedge i=X:=by unfold ζedge; simp_rw [← map_smul]; rw [← map_sum,show ∑ x: GateI,cue X x • Pi.single x (1:ℝ)=cue X from funext fun i=>by simp [Finset.sum_apply,Pi.single_apply]]; apply b_fact
private lemma mono_mix (Z:leadF rowS rowS)(x y:rowS)(i j:ℝ)(a:SU.group.Color): monover ((1/2:ℂ)* Z x y) (i • a) (j • a)=(1/2:ℂ)* Z (i • x) (j • y)*↑(inner ℝ a a):=by
 rw [mono_apply, real_inner_smul_left, real_inner_smul_right,map_smul]; change _=_ * (j • (Z (i • x) y)) * _; rw [map_smul]; change _=_*(j • (i • (Z x y))) *_; rw [Complex.real_smul,Complex.real_smul]; push_cast; ring
set_option maxHeartbeats 65000 in
lemma merc_E (Z:leadF rowS rowS)(x y:rowS)(e:SU.group.Color)(o:Skye.Seat n)(b:BudgetPoint):∑ i:Tickets, monover (νt o b Z i.1 i.2) (cue x i.1 • e) (cue y i.2 • e)=(1/2:ℂ)* Z x y * ↑(inner ℝ e e):=by
 let w(i):=cue x i; let u(i):= cue y i; let h:= inner ℝ e e
 rw [Fintype.sum_prod_type]; calc
    _=∑ i:GateI,∑ j:GateI,(1/2:ℂ)* Z (w i • ζedge i) (u j • ζedge j) * ↑h:= by
       apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; apply mono_mix -- helper
    _=(1/2:ℂ)* Z x y* ↑h:=by
       let Q:=fun i j:GateI=> Z (w i • ζedge i) (u j • ζedge j)
       have ht(i): ∑ j:GateI, Q i j=Z (w i • ζedge i) y:=by unfold Q; rw [←map_sum,show ∑ j:GateI,u j • ζedge j=y from merc y]
       change (∑ i:GateI,∑ j:GateI,(1/2:ℂ)*Q i j* ↑h)=_
       have hb(i):∑ j:GateI,(1/2:ℂ)*Q i j * (↑h:ℂ)= (1/2:ℂ)*Z (w i • ζedge i) y*↑h:=by rw [←sum_mul,←mul_sum,ht]
       simp_rw [hb]; rw [←sum_mul,←mul_sum]; congr 2; change (∑ i:GateI,Z.flip y (w i • ζedge i))= _; rw [←map_sum,show ∑ i:GateI,w i • ζedge i=x from merc x]; rfl

set_option maxHeartbeats 120000 in
lemma ψPlane (A B:tangD n)(e:SU.group.Color)(u:‖e‖=1)(Z:leadF rowS rowS)(x y:rowS)(H:∀ i j,Z i j=Z j i)(h:∀ i:GateI, HasDerivAt (fun t:ℝ=>πon o i p (increment 1 (t • A))) (cue x i • e) 0)(g:∀ i:GateI, HasDerivAt (fun t:ℝ=>πon o i p (increment 1 (t • B))) (cue y i • e) 0)
 (v:p.power≤3)(k:p.order≤6): let f:= terrace o p Z ∘ increment 1; iteratedFDeriv ℝ 2 f 0 ![A,B]=Z x y:=by
 intro f; obtain ⟨C,c,P⟩:= F_grade
 let X(i:Tickets):= ψTile o p i (νt o p Z i.1 i.2) ∘ increment 1
 let W(i:GateI):=πon o i p ∘ increment 1
 have hw(i):ContDiffAt ℝ ((2:ℕ):WithTop ℕ∞) (W i) 0:= ((P n o i p v k).rends 1 (ping_f p _)).paid.of_le (Nat.cast_le.mpr ((by decide:2≤6).trans p.order_ge))
 have he(i:Tickets):ContDiffAt ℝ ((↑(2:ℕ)):ℕ∞ω) (X i) 0:= ( (monover (νt o p Z i.1 i.2)).contDiff.contDiffAt.comp _ (hw i.1)).clm_apply (hw i.2)
 have hx(i:GateI): fderiv ℝ (W i) 0 A=cue x i • e:= (Push.side _ ((hw i).differentiableAt (by norm_num)) A).unique (h i); have hy(i):fderiv ℝ (W i) 0 B= cue y i • e:= (Push.side _ ((hw i).differentiableAt (by norm_num)) B).unique (g i)
 rw [show f=∑ i:Tickets,X i from (funext fun x=>by rw [Finset.sum_apply]; rfl), iteratedFDeriv_sum_apply]; swap; · exact fun i _=> he i -- name tune
 rw [_root_.sum_apply];
 have hz(i): W i 0=0:=by unfold W; rw [Function.comp_apply,at_zero,π_flat]
 calc
   _= ∑ i:Tickets, (monover (νt o p Z i.1 i.2) (cue x i.1 • e) (cue y i.2 • e)+monover (νt o p Z i.1 i.2) (cue y i.1 • e) (cue x i.2 • e)):= by
      apply sum_congr rfl; rintro ⟨a,b⟩ _; exact (hessian_B (W a) (W b) A B 0 (monover (νt o p Z a b)) (hw a) (hw b) (hz a) (hz b)).trans (by rw [hx,hy,hx,hy])
   _=_:= by rw [sum_add_distrib,merc_E, merc_E, H y x, real_inner_self_eq_norm_sq, u,one_pow,Complex.ofReal_one]; ring
end HushP
end Lenten
end YM.CF.TableF
end
