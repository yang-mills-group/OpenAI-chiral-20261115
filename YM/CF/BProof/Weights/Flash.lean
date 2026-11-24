import YM.CF.BProof.Weights.Pawn
import YM.CF.BProof.Pricing.Ease

/- short entries beam charge & light. sum black by b row index. price is PL polynomial
 multiples of indicated scale fees, uniformly. At test cut use sum with severe suppression.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Weights
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Release Release.hot Mapping House Pricing
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
local notation "G"=> SU.group
variable {s c': Side}(Y:Yard s)(g:Ratio c' s)
variable (M:ℝ→ℕ)(T:PathData G){θ R y w C v κ β:ℝ}{c:Clip}{K:Chart G}{P: Pub G}(p:Model K P c Y.short M R y κ)(u:Room Y (M y))(t:T.Bounds c w R v)(h:θ∈Set.Icc (1/2) 2)
variable (x x': Pawn Y) (b:Y.Col) (V: Finset (Block Y c'))
-- house tariffs
variable (θ)
def light := if b∈x.sev then 0 else Sky.light P Y T θ y p.X x.sev b x.gauss
def dim_step (M:ℝ→ℕ)(d:ℕ)(c:Clip)(R y:ℝ):= steady c d M R y+6*M y+steady c d M R y
abbrev prox (d r:ℕ):ℕ:= (2*r+1)^3*Beam.guard d
def frosty (i : Roll.Place Y):= x.gauss (b,i)* (Beam.black T θ p.X x.sev *ᵥ x.gauss) (b,i)
def fog := (∑ i, frosty Y M T θ p x b i)/2
variable {θ}
@[fun_prop] lemma light_m : Measurable (fun x:Pawn Y=> light Y M T θ p x b):=by
 refine Pawn.onSev (fun Z x=> if b∈Z then 0 else Sky.light P Y T θ y p.X Z b x.gauss) ?_; intro Z; split; exact measurable_const; unfold Sky.light; apply (Pub.dust_m ..).comp; let Q:=Beam.ζ T θ p.X Z; change Measurable (fun x:Pawn Y=>Function.curry (Q.mulVecLin x.gauss) b); unfold Function.curry; fun_prop
@[fun_prop] lemma fog_m : Measurable (fun x:Pawn Y=> fog Y M T θ p x b):=by
 apply Pawn.onSev (fun Z x=> (∑ i:Roll.Place Y,x.gauss (b,i)*(Beam.black T θ p.X Z *ᵥ x.gauss) (b,i))/2); intro Z; let Q:=Beam.black T θ p.X Z; change Measurable (fun x:Pawn Y=> (∑ i:Roll.Place Y,x.gauss (b,i)*(Q.mulVecLin x.gauss) (b,i))/2); fun_prop
lemma sum_fog : ∑ b,fog Y M T θ p x b=Beam.bill T θ p.X x.sev x.gauss:= by
 unfold fog Beam.bill dotProduct Roll.Stamp; rw [←sum_div]; conv_rhs=> rw [Fintype.sum_prod_type]
 rfl
lemma sum_light : ∑ b,light Y M T θ p x b=∑ b∈x.sevᶜ,Sky.light P Y T θ y p.X x.sev b x.gauss:= by
 let V:= Sky.light P Y T θ y p.X x.sev; conv_rhs=> rw [← show univ.filter (fun i=> i∉x.sev)=x.sevᶜ by ext; simp]
 rw [sum_filter]; exact sum_congr rfl fun i _=> by by_cases h:i∈ x.sev <;> simp [light,h]
variable (e:Pawn.Agreed g x x' V)
include e u
lemma view_h (p':Pawn.Shade g V b (steady c Y.short M R y)): light Y M T θ p x b=light Y M T θ p x' b:=by unfold light; refine if_congr (e.sev _ (Pawn.shade g V _ _ p')) rfl (congrArg (fun i=> Pub.dust P (CF.BProof.g y) i) (Pawn.pin_h g x x' V y T θ p.X u e b ((p.p_hor K P c M R Y y κ).symm ▸ p'))) -- tune motive implicit
lemma fog_h (p': Pawn.Shade g V b (dim_step M Y.short c R y)): fog Y M T θ p x b=fog Y M T θ p x' b:=by
 unfold fog; apply congrArg (fun x:ℝ=>x/2); apply sum_congr rfl; intro i hi; unfold frosty; rw [e.gauss (b,i) (Pawn.shade g V b _ p')]; refine congrArg (fun x:ℝ=> x'.gauss (b,i)*x) ?_; have hv:=Beam.meter T θ p.X u; rw [p.p_hor] at hv; exact Pawn.horizon g x x' V e b _ hv p' i
omit e
include t h
abbrev frost (r d:ℕ) (y:ℝ) := Beam.guard d*(prox d r* (trunc y*y⁻¹^2):ℝ)
abbrev fogC (M:ℝ→ℕ)(c:Clip)(d:ℕ)(R y:ℝ):= frost (dim_step M d c R y) d y
abbrev hotLight (P: Pub G)(c:Clip)(M:ℝ→ℕ)(R:ℝ)(d:ℕ)(y:ℝ):= Fintype.card (Pricing.apt d)* (P.C*(CF.BProof.g y*((SU.group.lieDim+1:ℕ)*(Beam.cost c d (steady c d M R y)*radius y))))
-- hot requires hT size ≤ P.radius. proved p.height. no Chart.cost.
lemma lights (v:Fares Y y x.gauss) : |light Y M T θ p x b| ≤ hotLight P c M R Y.short y:=by
 let A:= P.C; have he:P.C≥0:= P.cost; have ht:0≤ Beam.cost c Y.short (steady c Y.short M R y):=by have hx:0≤Beam.tide c Y.short:= (norm_nonneg _).trans ((Beam.measured T θ p.X u t h x.sev).2.2.1); unfold Beam.cost; positivity
 unfold light; split; · rw [abs_zero]; unfold hotLight; have hg:=coin_pos y (-1/2) 0 0; positivity
 unfold Sky.light; apply Pub.dust_c; intro i; rw [←tape_grant]; have hp:= beam_cost K P Y T θ κ p.X u t h x.sev x.gauss (p.bought K P c M R Y y κ) b (radius y) (sq_nonneg _) i (fun i _=> fairs Y x.gauss v i); rw [p.p_hor] at hp; exact hp; exact p.height.beam_to -- tune unfolding HotLight
lemma frosty_c (v:Fares Y y x.gauss)(i : Roll.Place Y) : |frosty Y M T θ p x b i| ≤ prox Y.short (dim_step M Y.short c R y)*(trunc y*y⁻¹^2):=by
 let A:=Gauss.base Y; let Q: Pool (Stamp Y):=Beam.black T θ p.X x.sev; let r:=dim_step M Y.short c R y; let F:=Gauss.edge Y; let J:=univ.filter fun i=> F.port i∈ A.ball b r; have hp:J.card≤prox Y.short r:= by have he:= F.vent_ball b r; unfold prox; rw [show Beam.guard Y.short= F.roof from (roof_eq _).symm]; convert! he using 1 <;> congr!
 have hl : ∀ j∈J, |Q (b,i) j|≤ y⁻¹^2 := fun j _=> (Gauss.RealM.entry Q _ _).trans ((Beam.wave T θ p.X x.sev u t h).2.2)
 have hZ : ∀ j:Stamp Y,j∉J→Q (b,i) j=0:= by
    intro j hj; have hg := Beam.meter T θ p.X u; rw [p.p_hor] at hg; exact hg.door _ _ _ (fun v=> hj (mem_filter.mpr ⟨mem_univ _,(A.ball_m ..).2 v⟩))
 have hg : |(Q *ᵥ x.gauss) (b,i)|≤ prox Y.short r*((y⁻¹)^2*radius y):=by
    change |∑ j,Q (b,i) j*x.gauss j|≤_; rw [←sum_subset (f:=fun j=>Q (b,i) j*x.gauss j) (subset_univ J) (fun i h k=>show _*_=0 by rw [hZ i k,zero_mul])]; apply (Finset.abs_sum_le_sum_abs ..).trans; apply le_trans (sum_le_sum (g:=fun _=>y⁻¹^2*radius y) (fun i hi=> (abs_mul ..).trans_le (mul_le_mul (hl i hi) (fairs Y x.gauss v i) (abs_nonneg _) (sq_nonneg _)))); rw [sum_const,nsmul_eq_mul]; gcongr
 unfold frosty; rw [abs_mul]; exact (mul_le_mul (fairs Y x.gauss v (b,i)) hg (abs_nonneg _) (sq_nonneg _)).trans_eq (by unfold trunc r; ring)
lemma fog_c (v:Fares Y y x.gauss) : |fog Y M T θ p x b|≤ fogC M c Y.short R y:=by
 have ht : |∑ i:Roll.Place Y,frosty Y M T θ p x b i| ≤ fogC M c Y.short R y := (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _=> frosty_c Y M T p u t h x b v i)).trans_eq (by unfold fogC frost; rw [sum_const,nsmul_eq_mul]; congr 2; simp [Roll.Place,Apt,TAxis,Gauss.Color, Beam.guard])) -- tune
 unfold fog; rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]; linarith [abs_nonneg (∑ i:Roll.Place Y,frosty Y M T θ p x b i)]
omit u h t
lemma fog_n (M:ℝ→ℕ)(u:PL fun y=>(M y:ℝ))(c:Clip)(d:ℕ)(R:ℝ)(h:0<d): NPL (fun y=>fogC M c d R y):=by
 let V(y:ℝ):= (dim_step M d c R y:ℝ); have hP:PL V:=by have hu:=steady_p c d M R h u; unfold V dim_step; push_cast; exact (hu.add ((PL.const _).mul u)).add hu
 have he:NPL (fun y=>trunc y*y⁻¹^2):=by
   apply NPL.by_le (g:=fun y:ℝ=>coin y (-2) 4 0) (coin_n (a:=-2) (b:=4) (by norm_num) _); filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy; apply le_of_eq; congr 1; unfold trunc radius scaleY; rw [show y⁻¹=coin y (-1) 0 0 by nth_rw 1 [← coinY hy]; rw [coin_inv]; ring_nf]; rw [coin_pow,coin_pow,coin_pow,coin_mul]; ring_nf
 unfold fogC frost; refine PL.muln (PL.const _) (PL.muln ?_ he); unfold prox; push_cast; exact (((((PL.const _).mul hP).add (PL.const _)).pow _).mul (PL.const _)) -- tune push cast
lemma hot_n (M:ℝ→ℕ)(u:PL fun y=>(M y:ℝ))(P: Pub G)(c:Clip)(R:ℝ)(d:ℕ)(h:0<d) : NPL (fun y=> hotLight P c M R d y):= by
 let f(y):=Beam.cost c d (steady c d M R y); let r(y):=coin y (-1/2) 2 0; have he(y): CF.BProof.g y*((SU.group.lieDim+1:ℕ)*(Beam.cost c d (steady c d M R y)*radius y))= (SU.group.lieDim+1:ℕ)*(f y*r y):= by rw [show r y=CF.BProof.g y*radius y by unfold radius scaleY; rw [coin_pow,coin_mul]; unfold r; ring_nf]; unfold f; ring
 unfold hotLight; simp_rw [he]; exact (PL.const _).muln ((PL.const _).muln ((PL.const _).muln ((beam_PL c d _ (steady_p c d M R h u)).muln (coin_n (a:= -1/2) (b:=2) (by norm_num) _))))
end YM.CF.BProof.Weights
