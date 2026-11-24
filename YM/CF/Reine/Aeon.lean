import YM.CF.Reine.Vesta
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
lemma cutM(O:Stores S)(F:Forest S.ratio)(j:ℕ)(h:1≤radiusB x): Fintype.card (Frozen O x F) ≤ latticeFieldEstimates O j x:=by
 let r:=(j+104)*radiusB x; let V:=bareStores S; let X:=locals V O x F r; let B(i:Frozen O x F):Active V x F:=⟨i.val,notChilled S F x _⟩; have he(i:Frozen O x F): B i∈X:=by
    refine mem_filter.mpr ⟨mem_univ _,?_⟩; unfold witnesses; have ht:O.dome (10*radiusB x)⊆ O.dome r:=farther (Nat.mul_le_mul_right _ (by omega)); exact i.property.imp (fun i=>ht i) fun i=>ht i -- tune projection chill
 have ht : Fintype.card (Frozen O x F) ≤ Fintype.card X:= Fintype.card_le_of_injective (fun i=> (⟨B i,he i⟩:↥X)) fun i j p=> Subtype.ext (congrArg (fun i:Active V x F=>i.val) (Subtype.ext_iff.mp p))
 rw [Fintype.card_coe] at ht; exact ht.trans (tune j h).2.2.2
abbrev shotM (R:ChartRatio G)(Y:ℝ)(β:ℝ):= spare R β*point G Y
lemma bill_l (R:ChartRatio G)(p:LocalRatio R)(L:Side): ∃ f, Lento f ∧ ∀ᶠ x in atTop,∀ B:ℝ,1 ≤ B→∀ β∈Set.Icc (Scales.y G L x/2) (2*y G L x), 0<shotM R B β ∧(shotM R B β)⁻¹ ≤ f x:=by
 let n:= Fintype.card SU.group.ColorIndex; let C:=Real.sqrt (2*Real.pi); let l:=point G 1; let F(x):= 2*y G L x; let f(x):= l⁻¹*(R.scale⁻¹*(C⁻¹*F x)^n); have hl:0<l:= point_p (by norm_num); have hp:0<C:= Real.sqrt_pos.mpr (by positivity)
 refine ⟨f,(Lento.sun _).times ((Lento.sun _).times (((Lento.sun _).times ((Lento.sun _).times (Lento.yearB L))).power n)),?_⟩
 filter_upwards [(year G L).eventually_ge_atTop 2] with x h B ht β hβ
 have hq:1≤β:= (by linarith only [h]: (1:ℝ) ≤ Scales.y G L x/2).trans hβ.1; have hv:=zero_lt_one.trans_le hq; let u:= coupling β; have hh:0<u:=coupling_pos hv; have ht' := point_p («G»:=G) (zero_lt_one.trans_le ht); have hr:l ≤ point G B :=ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (closedBall_subset_closedBall ht)); unfold shotM; refine ⟨mul_pos (spare_pos _ p hv) ht',?_⟩
 have hE: u⁻¹ ≤ F x:=by change (Real.sqrt β)⁻¹⁻¹ ≤ _; rw [inv_inv]; exact (Real.sqrt_le_left hv.le|>.mpr (by nlinarith)).trans hβ.2
 have hC:spare R β= (C*u)^n*R.scale:=by unfold C u spare; rw [Real.sqrt_mul (by positivity),Real.sqrt_sq hh.le]
 apply le_trans (inv_anti₀ (mul_pos (spare_pos _ p hv) hl) (mul_le_mul_of_nonneg_left hr (spare_pos _ p hv).le)); rw [hC,mul_inv_rev,mul_inv_rev,←inv_pow,mul_inv_rev,mul_comm u⁻¹]; have hP:=p.scale; unfold f; gcongr -- tune hr ↑₁
lemma pauce(R:ChartRatio G)(p:LocalRatio R)(g:ℝ)(h:0<g)(P:Patch)(j:ℕ):∀ᶠ x in atTop,∀ B:ℝ,1 ≤ B→∀ β∈Set.Icc (y G P.L x/2) (2*y G P.L x),0<shotM R B β ∧∀{c f:Side}(S:StepData c f),S.patch=P →∀ (F:Forest S.ratio)(O:Stores S), |trig ((j+100)*radiusB x) O * (shotM R B β)⁻¹^Fintype.card (Frozen O x F)| ≤ Real.exp (g*Scales.p G P.L x^2 * O.shares):=by
 obtain ⟨f,p,hf⟩:= bill_l R p P.L; let v:=g/3; have hp:0<v:=by positivity
 filter_upwards [hf,cardS P (fun _=>price0 P) j v (Lento.sun _) hp,cardS P (fun _=>price1 P) j v (Lento.sun _) hp, cardS P f j v p hp, Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hX hY hP hv hF B t β ht; obtain ⟨h₁,h₂⟩:=hX B t β ht; refine ⟨h₁,fun S h F O=>?_⟩
 let a:= shotM R B β; have he:|a⁻¹|≤ |f x|:= by rw [abs_of_nonneg (inv_nonneg.mpr h₁.le)]; exact h₂.trans (le_abs_self _)
 obtain ⟨v',k',-⟩:=tune (A:=O) (O:=O) (F:=F) j hF
 let u:= Real.exp (v*Scales.p G P.L x^2*O.shares); have ht': u*u*u= _ := show u*u*u=Real.exp (g*Scales.p G P.L x^2 * O.shares) from by unfold u; simp only [←Real.exp_add]; congr 1; unfold v; ring
 unfold trig; rw [abs_mul,abs_mul,abs_pow,abs_pow,abs_pow,h]; have hy:= Real.exp_pos (v*Scales.p G P.L x^2*O.shares); exact (mul_le_mul (mul_le_mul (hY S h O _ v') (hP S h O _ k') (by positivity) hy.le) ((pow_le_pow_left₀ (abs_nonneg _) he _).trans (hv S h O _ (cutM O F j hF))) (by positivity) (mul_nonneg hy.le hy.le)).trans_eq ht'
end YM.CF.Reine
