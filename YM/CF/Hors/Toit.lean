import YM.CF.Hors.Luke
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hors
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Push.Uniform (address Primary tint)
open Next.SectorChange Next.SectorChange.Wisps PatchReads
open Push.Uniform (weaker signedFine entryWidth Beacon)
variable {q:Clip}{R:PathData G}
lemma bolt_entry {ι:Type}[Fintype ι]{x:Fish ι}{f:Fish ι→ E}(h:ContDiffAt ℝ (n+1:ℕ) f x)(i:Fin (n+1)→ι) :Uniform.entry f x i= Uniform.entry (glance f (i (Fin.last n))) x (Fin.init i):=by
 let L:=ContinuousLinearMap.apply ℝ E (bolt (i (Fin.last n)))
 have he : ContDiffAt ℝ n (fderiv ℝ f) x:= h.fderiv_right (by norm_cast)
 unfold Uniform.entry; rw [show glance f _= _ from rfl] -- tune
 rw [iteratedFDeriv_succ_apply_right]; change _= iteratedFDeriv ℝ n (L ∘ (fderiv ℝ f)) _ _; rw [L.iteratedFDeriv_comp_left he le_rfl]; rfl
lemma entry_scale{ι:Type}[Fintype ι](f:Fish ι→ E)(s:ℝ)(i:Fin n→ι)(a:Fish ι)(h:ContDiffAt ℝ n f (s•a)) : Uniform.entry (fun y=> f (s•y)) a i= s^n • Uniform.entry f (s•a) i:=by
 let L:=s • ContinuousLinearMap.id ℝ (Fish ι); change iteratedFDeriv ℝ n (f ∘ L) _ _=_; rw [Uniform.iter_lin_at (L:=L) h, ContinuousMultilinearMap.compContinuousLinearMap_apply]; let v:=iteratedFDeriv ℝ n f (s•a); change v (fun j=> s • _) = _; rw [v.map_smul_univ]; simp; rfl
lemma residue(p:R.Bounds q s C Q)(m:ℕ)(U:Config G c):
 mainTerm q R U-mainTerm q (grainA R m) U=Patch.average (fun i:Signed=>uncut (rod R m) (pull i 0 U)+uncut (haste m R.cubic) (pull i 0 U)+ uncut (haste m R.quartic) (pull i 0 U)):=by
 unfold mainTerm Patch.average; rw [← mul_sub,← Finset.sum_sub_distrib]; congrm _ * ?_
 refine Finset.sum_congr rfl fun i _=>?_ ; unfold quadratic uncut; simp_rw [Fintype.sum_prod_type, Finset.sum_add_distrib,uncut_pair p, uncut_high _ p.width p.three,uncut_high _ p.width p.four, Finset.sum_sub_distrib]; dsimp only [grainA]; abel
open Finset
def yearZ(f:E→ℝ)(n:ℕ)(x:E)(w:Fin n→E):= iteratedFDeriv ℝ n f x w
lemma winds_C (f:Signed→ E→ℝ)(x:E)(h:∀ i,ContDiffAt ℝ n (f i) x)(v:Fin n→E)(hp:∀ i,|yearZ (f i) n x v| ≤ C): |yearZ (fun y=>Patch.average fun i=>f i y) n x v| ≤ C:=by
 have hv:0<(Fintype.card Signed:ℝ):=by positivity
 let g:=fun y=> ∑ i,f i y; let s:=(Fintype.card Signed:ℝ)⁻¹; have he : ContDiffAt ℝ n g x:= ContDiffAt.sum (s:=Finset.univ) fun i _=> h i
 rw [show (fun y=>Patch.average fun i=> f i y)=s • g from rfl,yearZ, iteratedFDeriv_const_smul_apply he,_root_.smul_apply, smul_eq_mul,abs_mul,abs_of_pos (show s>0 from inv_pos.mpr hv)]
 rw [show g=∑ j,f j from funext fun y=>(Finset.sum_apply y _ f).symm, iteratedFDeriv_sum_apply (u:=Finset.univ) (fun i _ => h i), _root_.sum_apply] -- tune
 apply (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (fun i _ => hp i))) (show 0 ≤ s from (inv_pos.mpr hv).le)).trans; rw [sum_const, card_univ,nsmul_eq_mul,← mul_assoc, inv_mul_cancel₀]; simp; exact hv.ne'
def stip(G:Gauge)(n k:ℕ)(D s:ℝ):= let v:=weaker (n+1) (entryWidth (n+1) 1 (s/2)); composeCost n (fareX G k (n+1) D (s/2) 1 * (1+Uniform.townCost G*Uniform.countCost v)^n) 1
lemma lead(q:ℕ→Atom G l)(p:SumBudget (fun i=> (q i).budget (s/2)) (tollE s i*C))(hs:0<s)(hc: 2 ≤ c.val)(h:Uniform.PaintSupply G (n+1) D)(t:Signed)(v:Fin (n+1)→Primary c G):
 let F(y:Mast G c):= uncut q (pull t 0 (facadeX G y)); ContDiffAt ℝ ω F 0 ∧ |Uniform.entry F 0 v| ≤ tollE s i * (C * stip G n l D s):=by
 intro F
 obtain ⟨hp,hq⟩:= priceCut p (half_pos hs) h hc 0 (by simp [zero_lt_one]) t (v (Fin.last n)); refine ⟨hp,?_⟩
 rw [bolt_entry (hp.of_le le_top)]; apply ((Uniform.entry_bound (f:=glance F _) (p:=0) _).trans (hq.norm_le n le_rfl)).trans; exact Eq.le (by unfold stip composeCost; ring)
lemma cany(h:Uniform.PaintSupply G (n+1) D)(p:R.Bounds q s C Q)(v:Fin (n+1)→ Primary c G)(hc:2 ≤ c.val)(i:ℕ):
 let F(y:Mast G c):=mainTerm q R (facadeX G y)-mainTerm q (grainA R i) (facadeX G y)
 ContDiffAt ℝ ω F 0 ∧ |Uniform.entry F 0 v| ≤ tollE s i * (Stationary.gramCost G C*stip G n 2 D s + C*stip G n 3 D s+ C*stip G n 4 D s):=by
 intro F; have he(t:Signed):= lead _ (hurry p i) p.width hc h t v; have hp(t:Signed):= lead _ (pastA _ p.width p.three i) p.width hc h t v; have hz(t:Signed):= lead _ (pastA _ p.width p.four i) p.width hc h t v
 unfold F; simp_rw [residue p]; constructor
 · exact (ContDiffAt.sum (s:=Finset.univ) fun t _ => (((he t).1).add (hp t).1).add (hz t).1).const_smul ((Fintype.card Signed:ℝ)⁻¹) -- needs left smul
 apply winds_C (n:=n+1) _ 0 (fun t=> ((((he t).1).add (hp t).1).add (hz t).1).of_le le_top) (fun i=>bolt (v i)) ?_
 intro j; unfold yearZ; erw [iteratedFDeriv_add_apply (((he j).1.add (hp j).1).of_le le_top) ((hz j).1.of_le le_top),iteratedFDeriv_add_apply ((he j).1.of_le le_top) ((hp j).1.of_le le_top)]; rw [_root_.add_apply,_root_.add_apply]; exact (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add (he j).2 (hp j).2)) (hz j).2 |>.trans_eq (by ring)) -- tune
end YM.CF.Hors
