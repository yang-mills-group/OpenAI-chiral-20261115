import YM.SU5.Relativistic.LinCap
import YM.SU5.FiniteGaugeData.Pannier.Appraise
/-! # gauge leading pressure P.Resource. -/
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ENNReal
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Vale
open Corne
open Py.Rate.Pannier
section links
variable {G:Gauge}(R:ChartRatio G)(p:LocalRatio R)(k:KernelChoices)
local notation "d"=> Fintype.card G.ColorIndex
open SectorNext.Vacuum
include p
private lemma narrowPrec : Real.log (SectorNext.Vacuum.narrow R k.penalty)=logFlat R-d / (2:ℝ)*Real.log k.penalty:=by
 have h:= k.penalty_pos; unfold SectorNext.Vacuum.narrow; rw [Real.log_mul p.scale.ne' (Real.rpow_pos_of_pos (by have := Real.pi_pos; positivity) _|>.ne'), Real.log_rpow (by have := Real.pi_pos; positivity)]
 rw [show Real.pi/(k.penalty/2)=(2*Real.pi)/k.penalty by ring,Real.log_div (mul_pos zero_lt_two Real.pi_pos|>.ne') h.ne']
 have he:Module.finrank ℝ G.Color=d:= by simp [Gauge.Color]; -- scope
 change Real.log _+(Module.finrank ℝ G.Color:ℝ)/2*(Real.log _-Real.log _)=_; unfold logFlat; rw [he]; ring
lemma link_b (ε:ℝ)(e:0<ε):∀ᶠ b in atTop,∀ {m n:Side}(S:StepData m n), S.kernel=k → |Real.log (S.penaltyZ b G) - (Real.log (Next.SectorChange.spare R b)-(halfLie G)*Real.log k.penalty)|≤ ε:=by
 let f(t:ℝ):=t^(Module.finrank ℝ G.Color)*linkZ G (k.penalty*t^2)
 have ht:= ((first_asymptotic R p _ k.penalty_pos).log (SectorNext.Vacuum.narrow_pos R p _ k.penalty_pos|>.ne')).sub_const (Real.log (SectorNext.Vacuum.narrow R k.penalty)); rw [sub_self] at ht
 filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_sqrt_atTop.eventually (ht.abs.eventually (ge_mem_nhds (abs_zero.trans_lt e)))] with b h W
 intro m n S p'; let t:=Real.sqrt b; have he:t^2=b:=Real.sq_sqrt h.le
 have hx:linkZ G (k.penalty*t^2)=S.penaltyZ b G:=by rw [he]; unfold StepData.penaltyZ StepData.penaltyWeight linkZ SectorNext.Vacuum.mouth; rw [p']; congr 1; ext; ring_nf
 change |Real.log (t^(Module.finrank ℝ G.Color)*linkZ G (k.penalty*t^2))-Real.log _|≤_ at W; rw [hx,Real.log_mul (pow_ne_zero _ (Real.sqrt_pos.mpr h|>.ne')) (S.penaltyZ_pos ..).ne',Real.log_pow,narrowPrec R p] at W
 rw [spare_formula _ p.scale h, ←shadowLie]
 apply le_trans (le_of_eq ?_) W; congr 1; rw [←shadowLie,show Real.log t=_ from Real.log_sqrt h.le,halfLie]; ring
end links
section point
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}(V:Grace K R L)
local notation "G"=> SU.group
lemma striding (D:Stake.Pilot)(e:ℝ)(h:0<e):∀ᶠ x:ℝ in atTop,∀ r≥D.hat R x/4,0< Appel.point G r ∧ |Real.log (Appel.point G r)|≤ e:=by
 have hh:Tendsto (fun x=> D.hat R x/(4:ℝ)) atTop atTop:= ((Scales.peak G R.L).const_mul_atTop D.high).atTop_div_const (by norm_num) -- check
 have hb:Tendsto (fun n:ℕ=> Appel.point G n) atTop (𝓝 1):=by
    let μ:=rice G
    have ht:Monotone (fun i:ℕ=> closedBall (0:(G).Color) (i:ℝ)):=fun a b p=> closedBall_subset_closedBall (by exact_mod_cast p)
    have he:= tendsto_measure_iUnion_atTop ht (μ:=μ)
    rw [show (⋃ i:ℕ, closedBall (0:(G).Color) (i:ℝ))=Set.univ from ?_] at he; swap
    · apply Set.eq_univ_of_forall; intro x; obtain ⟨k,e⟩:=exists_nat_gt ‖x‖; exact Set.mem_iUnion.mpr ⟨k,by simpa [mem_closedBall,dist_zero_right] using e.le⟩
    have hT: Tendsto (fun i:ℕ=> Appel.point G i) atTop (𝓝 (μ Set.univ).toReal):= (ENNReal.tendsto_toReal (a:=μ Set.univ) (measure_ne_top _ _)).comp he; simpa [μ] using hT
 obtain ⟨n, hn, hz⟩:= ((hb.log one_ne_zero |>.abs |>.eventually (ge_mem_nhds (show |Real.log 1|<e by simpa using h))).and (eventually_gt_atTop 0)).exists
 filter_upwards [hh.eventually_ge_atTop n] with x he r e'; have hc: (n:ℝ)≤r:= he.trans e'; have hk:=point_p («G»:=G) (v:= (n:ℝ)) (by positivity); have hv: Appel.point G n≤ Appel.point G r:= ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (closedBall_subset_closedBall hc))
 have ha: Appel.point G r ≤1:= (show Appel.point G r ≤ (rice G Set.univ).toReal from ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))).trans_eq (by simp)
 have hr:=hk.trans_le hv; have hb:=Real.log_le_log hr ha; have hh:= Real.log_le_log hk hv; exact ⟨hr,abs_le.mpr ⟨(abs_le.mp hn).1.trans hh, by rw [Real.log_one] at hb; linarith only [h,hb]⟩⟩
-- define PRESS logs on Dir colored gauge
abbrev views (L:ChartRatio SU.group)(n:Side)(β:ℝ) := (3*(Fintype.card (Site n):ℝ)-3) * Real.log (Next.SectorChange.spare L β)
-- Hessian depends on actual stationary Gold. Counts physical beta at scale (important offset reference depends on both β). Keep logs as real cost.
def preGa (n:Side)(p:ℕ)(β:ℝ) := views L n β + -(1/2:ℝ)*Real.log (costDet G (V.L.H p) n)
include V
variable (B0:Stake.Pilot)
local notation "κ"=> K.bind.penalty
open Next.Fluctuations.Sector Stake Reine
lemma creneaux (h:LocalRatio L) (ε:ℝ)(p:0<ε):∀ᶠ x in atTop,∀ {c f:Side}(v:f.val=c.val*R.L.val)(i:ℕ)(M:Monk G (V.L.op i v)),Cert R K (V.L.op i v) (V.L.mint i v) x →∀ β∈ Year R x,∀ u≥B0.hat R x/4,
 let S:=V.L.op i v; let y:=prefactor S G β; let t:=shotM L u β
 0<y ∧ 0<t ∧ |Real.log (y*(t^Fintype.card M.park.Free))+Corne.arcD (V.L.mint i v) x M - (preGa V f i β-preGa V c (i+1) β)| ≤ ε*Fintype.card (Site f):=by
 let e:=ε/9; have he:0<e:=by unfold e; positivity
 obtain ⟨b,g⟩:= eventually_atTop.mp (link_b L h K.bind _ he)
 filter_upwards [striding (R:=R) B0 e he,(Scales.year G R.L).eventually_ge_atTop (2*b), (Scales.year G R.L).eventually_gt_atTop 0, arc_toll V he] with x p₁ x₁ x₂ A₁
 intro c f v i M a β ht u p' S y t; have hp:0<β:=by linarith only [ht.1,x₂]
 obtain ⟨hb,hc⟩:=p₁ u p'
 have h₁:0<y:= prefactor_pos ..; have h₂:0<t:=mul_pos (spare_pos _ h hp) hb
 let A:ℝ:=Fintype.card (Site f); let B:ℝ:=Fintype.card (Site c); have hw:B ≤ A:=Nat.cast_le.mpr (Fintype.card_le_of_injective _ S.ratio.embed_injective)
 have hx:0≤ B:=Nat.cast_nonneg _
 have hQ:Fintype.card (Edge (Site c))= Fintype.card (Site c)*4:=Fintype.card_prod ..
 have hf:(Fintype.card M.park.Free:ℝ)=3*A+B:=thinWireCount S.ratio M.park
 have hg:=g β (by linarith only [x₁,ht.1]) S rfl; rw [shadowLie] at hg; let l:=Real.log (Next.SectorChange.spare L β)
 have hz: Real.log (y*(t^Fintype.card M.park.Free))= -(4*B)*Real.log (S.penaltyZ β G)+(3*A+B)*(l+Real.log (point G u)):=by
    rw [Real.log_mul h₁.ne' (pow_pos h₂ _|>.ne'),Real.log_pow, hf]; unfold y t; rw [prefactor,Real.log_pow,Real.log_inv,hQ,shotM,Real.log_mul (spare_pos _ h hp).ne' hb.ne']; push_cast; unfold B l; ring
 let δ:= Fintype.card SU.group.ColorIndex; let Z:= arcD (V.L.mint i v) x M
 have hA: |Z- -(1/2:ℝ)*(Real.log (costDet G (V.L.H i) f)+ (4*B*δ)*Real.log κ-Real.log (costDet G (V.L.H (i+1)) c))|≤ ε/9*A:=by rw [show 4*B*(δ:ℝ)=Fintype.card (Ink G c) from ?_]; exact A₁ v i M a; change _=((Fintype.card ((Edge (Site c))×(G).ColorIndex)):ℝ); rw [Fintype.card_prod,hQ]; push_cast; unfold B δ; ring
 refine ⟨h₁,h₂,?_⟩; rw [hz]; unfold preGa views; rw [abs_le] at hg hc hA ⊢; change -(ε*A) ≤ _ ∧ _ ≤ ε*A
 have hk:= mul_le_mul_of_nonneg_left hg.1 hx; have hk' := mul_le_mul_of_nonneg_left hg.2 hx
 have hV: 0≤ 3*A+B:=by linarith
 have hI:=mul_le_mul_of_nonneg_left hc.1 hV; have hJ:=mul_le_mul_of_nonneg_left hc.2 hV
 unfold Z A B e at *
 unfold l
 constructor <;> nlinarith only [p,hk,hk',hI,hJ,hA.1,hA.2,hw]
end point
end YM.CF.Papyrus.GaugeFlux
