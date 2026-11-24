import GaugeFieldConstruction.GapLog
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
open Py Trees Hake FlightFlux TableF Boom Axon Lenten.ModuleB Flot Taxi
open HarmP
namespace BellPrice
open Lenten FlightFlux Fluxim
open Planned.PrimaryIntegral295 Carrier
private abbrev Ski (K:Side)(B:Bool→ℝ)(i:ℕ):ℝ:=24^3*10^3 * (1800* B false *B true*(SpanL K)^2*(αN K)^(3+i))
lemma Aster {c f:Side}(G:Ratio c f)(B:Bool→ℝ)(i:ℕ): ScoreBB B G i=Ski G.count B i:=by unfold ScoreBB Ski; rw [OvKos]
private lemma frontS(B: Bool→ℝ)(b:∀ x,0≤ B x)(L:Side)(i:ℕ):0≤ Ski L B i:=by unfold Ski; have hi:= b true; have hg:= b false; have hv:=α_pos L; positivity
-- make a single small ξ & δ. and ε after.Tp
private lemma hp_M (x y:ℝ): mintPay (x*y)=mintPay x*y:=by unfold mintPay; ring
variable {c f L:Side}{k:ℕ}{V:ℝ}
lemma Crest_P(L:Side)(k:ℕ)(B:Bool→ℝ)(b:∀ x,0≤B x)(a:ℝ)(u:0≤a) (χ:ℝ)(p:0<χ):∃ m:ℕ,∀ (c f:Side)(G:Ratio c f)(t:G.count=L)(d z:ℝ)(v:z≤a)(ht:0≤d),∀ r≤k,m ≤c.val → OriginPrice c f G B r z (Haro.flavor^2*d) ≤ χ*d :=by
 let P(i:ℕ):= labelB*a*Ski L B i*Haro.flavor^2; have h (i):0 ≤P i:=by unfold P; exact mul_nonneg (mul_nonneg (mul_nonneg labelPos u) (frontS B b L i)) (sq_nonneg _)
 let D:=∑ i∈range (k+1),P i; have hx:0 ≤D:=sum_nonneg fun i _=> h _
 obtain ⟨Y,e⟩:= eventually_atTop.mp (show ∀ᶠ x:ℕ in atTop,mintPay D/(x:ℝ) ≤ χ from (show Tendsto (fun x:ℕ=> mintPay D/(x:ℝ)) atTop (𝓝 0) from (tendsto_const_nhds (x:=mintPay D)).div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually (ge_mem_nhds p)) -- tune R
 refine ⟨Y,fun c f G t d z v h' r hr E=>?_⟩; unfold OriginPrice; rw [Aster,t]; have he:0 ≤ (c.val:ℝ):=by positivity
 apply le_trans _ (mul_le_mul_of_nonneg_right (e _ E) h');
 have hv:mintPay D/(c.val:ℝ)*d=mintPay (D*d/c.val):=by simp_rw [div_eq_mul_inv,hp_M]; ring
 rw [hv]; apply mintOrder; apply div_le_div_of_nonneg_right _ he;
 apply le_trans _ (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=P) (s:=range (k+1)) (fun i _=> h i) (mem_range.mpr (show r<k+1 from by omega))) h');
 unfold P; apply le_trans _ (le_of_eq (Eq.symm (mul_assoc ..)) -- tune sign?
 ); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left v labelPos) (frontS B b L r)) (by positivity)
-- time savings. Uniform smooth approximate.
lemma Shoot(L:Side)(B:Bool→ℝ)(s:ℝ)(b:∀ x,0≤B x)(p:0<s)(V:ℝ)(hv:0<V):∃ δ> (0:ℝ),GauDebt 1 s (δ/2) δ ≤ V ∧ mintPay ((caboose*16)* (xHoch 6*(δ/2)*Ski L B 0*Haro.flavor^2)) ≤ V/2 ∧ mintPay ((caboose*16)* ((xHoch 6*((δ/2)*(4*s))+δ+δ)* Ski L B 0* Haro.flavor^2))≤V/2 :=by
 let K:=(𝓝[>] (0:ℝ)); let f(d:ℝ):= GauDebt 1 s (d/2) d; let S:= Ski L B 0; let t:= caboose*16; let P(d:ℝ):= mintPay (t*(xHoch 6*(d/2)*S*Haro.flavor^2)); let Y(d:ℝ):= mintPay (t*((xHoch 6*((d/2)*(4*s))+d+d)*S* Haro.flavor^2))
 have hp: Continuous f:=by unfold f GauDebt mToll; fun_prop
 have hT: Continuous P:=by unfold P mintPay; fun_prop
 have hV: Continuous Y:=by unfold Y mintPay; fun_prop
 let X:= nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)) (a:=0) -- tune names
 have H:∀ᶠ d in K, f d≤ V:=((hp.tendsto _).mono_left X).eventually (ge_mem_nhds (by simpa [f,GauDebt,mToll] using hv))
 have HK:=((hT.tendsto _).mono_left X).eventually (ge_mem_nhds (show P 0<V/2 from by simpa [P,mintPay] using half_pos hv))
 have Hx:=((hV.tendsto _).mono_left X).eventually (ge_mem_nhds (show Y 0<V/2 from by simpa [Y,mintPay] using half_pos hv))
 exact ((show ∀ᶠ d in K,0<d from self_mem_nhdsWithin).and (H.and (HK.and Hx))).exists
structure Postumi (L:Side)(x' x s δ V:ℝ) (B:Bool→ℝ) : Prop where
 holds :∀ (N P J:Side)(G: Ratio (mid N J) (mid P J))(X:Scree.Hub (mid P J))(S:StepData (Domain N J) (Domain P J)), G.count=L→ S.patch.L=L →∀ (p q:BudgetPoint), Short S q X.val.2→ q.threshold=temp (x+x') → q.B≤ 2*radiusB x → p.threshold ≤ 2*q.threshold → radiusB x ≤(mid N J).val → ∀ (c:ℝ)(r:ℕ),r ≤2 →0 ≤ c → Polaris X p q s (δ/2) δ G B c r≤ V*c
lemma luck_S (L:Side)(B:Bool→ℝ)(x' s:ℝ)(p:0<s)(v:∀ x,0≤B x)(V:ℝ)(hV:0<V):∃ δ>(0:ℝ), ∀ᶠ x in atTop, Postumi L x' x s δ V B:=by
 obtain ⟨δ,y,h,c,d⟩:=Shoot L B s v p V hV; let K:=caboose*16; let A:=unitStep L^2*2; let b:= (4*s+A)*(1+(24:ℝ))^3+δ; have hp:0 < b:=by unfold b A; have ht:=unitStep_pos L; positivity
 have hb:0 ≤ waist 1:= waist_pos _ zero_le_one
 obtain ⟨n,H⟩:=Crest_P L 2 B v (A+1) (by unfold A; positivity) (V/2) (half_pos hV); let W:=Ski L B 0
 refine ⟨δ,y,?_⟩; filter_upwards [bspokes x' L 1 (waist 1*b) δ y, Work.E01.radiusB_tendsto.eventually_ge_atTop n] with x tY tV; constructor; intro N P J G X S t r p' q u ht z hk v' C j g ht'
 apply max_le; · refine le_trans (le_of_eq (show GauDebt _ _ _ _=GauDebt 1 s (δ/2) δ*C from ?_)) (mul_le_mul_of_nonneg_right h ht'); unfold GauDebt; ring
 let α:=Λgear 1 p'.threshold q.threshold G.count; have hi:0≤ A:=by unfold A; have he:=unitStep_pos L; positivity
 let Hx:= H (mid N J) (mid P J) G t C; let s':= tV.trans v'
 apply max_le
 · have hs:= Hx 1 (by unfold A; linarith) ht' j g s'
   change prices0 _ _ _ _+_ ≤_; apply le_trans (add_le_add _ hs) (le_of_eq (show V/2*C+V/2*C=V*C from by ring)); apply le_trans _ (mul_le_mul_of_nonneg_right c ht'); apply le_of_eq; unfold prices0; rw [Aster,t]; simp_rw [mintPay]; ring
 have hpA:α ≤A:=by unfold α; rw [t]; exact (μpre L 1 p' q hk).2
 have hq:waist (αSpring q X (Tpulse q s δ α)) ≤ δ:=by
    have hh:= tY _ _ S q X ht z r u; rw [waist_h]; unfold αSpring; have he:Tpulse q s δ α ≤ b:=by unfold Tpulse b; gcongr
    have hp':0≤q.threshold:=q.threshold_pos.le; apply le_trans _ hh; rw [pow_one]; rw [←mul_assoc,←mul_assoc]; exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hb) hp') (le_add_of_nonneg_left zero_le_one) (by positivity) (by positivity)
 apply le_trans (add_le_add ?_ (Hx α (hpA.trans (le_add_of_nonneg_right zero_le_one)) ht' 0 (by omega) s')) (le_of_eq (show V/2*C+V/2*C=V*C from by ring))
 apply le_trans _ (mul_le_mul_of_nonneg_right d ht'); let U:=xHoch 6*((δ/2)*(4*s))+δ; change mintPay (K*((U+waist _)* ScoreBB B G 0 * _)) ≤ mintPay _*C
 rw [show Λgear 1 p'.threshold q.threshold G.count=α from rfl,Aster,t,←hp_M]; apply mintOrder
 rw [mul_assoc K, mul_assoc (_* Ski L B 0) (Haro.flavor^2)] -- tune K occurrence
 exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (add_le_add_right hq _) (frontS B v L 0)) (by positivity)) (mul_nonneg cab_pos.le (by positivity))
end BellPrice
end YM.CF.Oath
end
