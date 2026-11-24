import YM.CF.Appel.Test
set_option autoImplicit false
noncomputable section
namespace YM.CF.Appel
open Char Summit Neige
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal NNReal
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c} {K v d s t:ℝ} {n:ℕ}
open Gaussian ProbabilityTheory AnalyticBridge.Annulus1AD
variable [MeasurableSpace E][BorelSpace E][CompleteSpace E][SecondCountableTopology E]
variable (β:ℝ)
variable {T':Teller G}{w D s:ℝ}{h: Allocation G S x w}{q:Chi}{J:ChartRatio G}
section defs
variable(T:Tube G S)(F:Forest S.ratio)(A:Stores S)(V:Config G c)(k:S.Choices)(x:ℝ)(l:ℕ)(q:Chi)(d:ℝ)(Y: LinkArray G (Frozen A x F))
abbrev realP (z:LogArray G (Active A x F)):= spinC (credW T A F k q d x Y l V) (coupling β) (liftN T x V k A F q d Y l) z
abbrev putU (z:LogArray G (Active A x F)):= tape (realP β T F A V k x l q d Y z)
abbrev fieldU(z:LogArray G (Active A x F)):= Next.SectorChange.physical A F V Y (putU β T F A V k x l q d Y z)
end defs
def reelX (h:Allocation G S x w)(q:Chi)(J:ChartRatio G)(x' d:ℝ)(T:Tube G S)(A:Stores S)(F:Forest S.ratio)(V:Config G c)(k:S.Choices)(l:ℕ)(g:Config G f→E)(Y: LinkArray G (Frozen A x F))(z:LogArray G (Active A x F)):=
   |(credW T A F k q d x Y l V).det| • (Real.exp (costU z /2) • regularized h A F V k q J d g Y (putU β T F A V k x l q d Y z))
set_option maxHeartbeats 800000 in
lemma ret (U:Config G f→E)(hX:Envelope U)(W: MossX n l x A F T V k C d t q)(h:Allocation G S x w)(hs:Standing (F:=F) (A:=A) h J d k V)(hJ:LocalRatio J)(hw:4*d<J.radius)(hd:0<d)(hβ:0<β)(hz:wireP G (coupling β) d (C*t) C ≤ s)(h₀:0<s):
 let I:= tableG G (Active A x F) s
 let N:= piHaar G (Frozen A x F)
 let g:=reelX β h q J x d T A F V k l U
 let u:=attending h A F V k U
 (∀ Y,Integrable (g Y) I)∧Integrable (uncurry g) (N.prod I)∧
 (∫ i,u i∂F.order G)= (spare J β * point G s)^Fintype.card (Active A x F) • (∫ Y, (∫ z, g Y z ∂I) ∂N):=by
 intro I N g u; haveI : IsProbabilityMeasure I:= how G h₀
 let c:= ((Real.sqrt (2*Real.pi*coupling β ^ 2))^Fintype.card G.ColorIndex* point G s)^Fintype.card (Active A x F)
 have ha:= coupling_pos hβ; have hc:0<c:=by unfold c; have he:=point_p (G:=G) h₀; positivity
 let f:=regularized h A F V k q J d U
 obtain ⟨hT,hF,hN,hπ,h₃⟩:=regularized_price h A F V k hJ q hd hw hs U W.ready.rules hX
 have hx(Y: LinkArray G (Frozen A x F)): Integrable (g Y) I∧ (∫ i, f Y i)= c • ∫ z,g Y z ∂I ∧ (∫ i,‖f Y i‖)= c • ∫ z,‖g Y z‖ ∂I:=by
   let J':=credW T A F k q d x Y l V; let e:= bang J' (coupling β) (liftN T x V k A F q d Y l) (f Y); have hm(i):g Y i= |J'.det| • e i:= rfl; obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩:= W.jumps Y
   have ht(z:LogArray G (Active A x F))(hp:f Y (putU β T F A V k x l q d Y z)≠ 0):z∈surface G (Active A x F) s:=by
      let U' := putU β T F A V k x l q d Y z;
      have he : ‖liftN T x V k A F q d Y l‖≤ C*t:=by simpa only [show Vmove x V 0=V from by simp [Vmove]] using h2.value -- tune
      have hh : doors q d U' ≠ 0:=fun H=>hp (by unfold f regularized; change (_*doors q d U') • _ = _; rw [H,mul_zero,zero_smul]); have H:=spins J' h7 _ _ he h8 z q ha hd hh; exact fun i hi=>closedBall_subset_closedBall hz (H i hi)
   obtain ⟨h,e'⟩:=spin_ledger J' h7 _ _ (f Y) ha (hF Y) h₀ ht
   refine ⟨?_,?_,?_⟩
   · rw [show g Y= |J'.det| • e from rfl]; exact h.smul _
   · simp_rw [hm,e',integral_smul,smul_smul]; rw [mul_comm c]
   obtain ⟨-,he⟩:=spin_ledger J' h7 _ _ (fun x=> ‖f Y x‖) ha (hF Y).norm h₀ (fun i hi=> ht i (norm_ne_zero_iff.mp hi)); rw [he]; simp_rw [hm,norm_smul,Real.norm_of_nonneg (abs_nonneg _),integral_const_mul]; change |J'.det| *c*_= c*(|J'.det| *∫ z,‖e z‖ ∂I) -- lex
   have hu(i) : bang J' (coupling β) (liftN T x V k A F q d Y l) (fun x=> ‖f Y x‖) i=‖e i‖:=by unfold e bang; rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]; rfl
   simp_rw [hu]; ring!
 have hj:Measurable (uncurry g):=by
   let J':=credW T A F k q d x 1 l V
   let X':=LinkArray G (Frozen A x F) × LogArray G (Active A x F)
   let B: X'→ LogArray G (Active A x F):=fun z=> putU β T F A V k x l q d z.1 z.2; have hm:Measurable B:=by
      unfold B putU realP spinC; simp_rw [W.still]; exact tape.measurable.comp ((W.moves.measurable.comp measurable_fst).add (((acts_meas J').comp (tape.symm.measurable.comp measurable_snd)).const_smul (coupling β)))
   have hcU:Measurable (fun x:LogArray G (Active A x F)=> costU x) := Finset.measurable_fun_sum _ fun i _ => ((measurable_pi_apply i).comp tape.symm.measurable).mul ((measurable_pi_apply i).comp tape.symm.measurable)
   have he : Measurable (fun i: X'=>Real.exp (costU (Prod.snd (i:LinkArray G (Frozen A x F) × LogArray G (Active A x F)))/2)):=Real.continuous_exp.measurable.comp ((hcU.comp measurable_snd).div_const 2)
   change Measurable (fun i:X'=> |(credW T A F k q d x i.1 l V).det| • (Real.exp (costU i.2/2) • f i.1 (B i)))
   simp_rw [W.still]
   have hp:Measurable (uncurry f):=regularized_meas h A F V k hJ q hd hw U W.ready.rules hX
   let u : X' → LinkArray G (Frozen A x F):= Prod.fst
   have hv:= hp.comp ((show Measurable u from measurable_fst).prodMk hm)
   have he' := (he.smul hv).const_smul |J'.det|
   exact he' 
 refine ⟨fun Y=>(hx Y).1,(integrable_prod_iff hj.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun i=> (hx i).1,?_⟩,?_⟩
 · change Integrable (fun Y=>∫ i,‖f Y i‖) N at hN; simp_rw [fun i=> (hx i).2.2] at hN; have ht:= hN.smul c⁻¹; change Integrable (c⁻¹ • c • fun Y=> ∫ z, ‖g Y z‖ ∂I) N at ht; rwa [smul_smul,inv_mul_cancel₀ hc.ne',one_smul] at ht
 change (∫ i,u i ∂_) = _ • ∫ Y, (∫ a, f Y a)∂N at h₃; simp_rw [h₃,fun i=> (hx i).2.1,integral_smul,smul_smul]; congr 1; unfold spare c; ring
end YM.CF.Appel
