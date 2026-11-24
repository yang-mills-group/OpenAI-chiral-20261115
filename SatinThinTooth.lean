import SatinThinDuty
import YM.CF.Moto.Pin
import YM.CF.Mica.Shut
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Ione Moto
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations StressFlux AnalyticBridge.VerifiedReset Push.Local
open Taxi
open Vow
local notation "G₅"=> SU.group

/-- Transform Skate by Sweep, convention price like `base_Q`.
  X later represented array -> compares at **earlier** Hub.
  On shape, take earlier slots labeled by **pushed** edges.
  So use `symm`. -/
def spinScar (s:Signed)(x:PlaqAxes):ℝ := sign s x.val.1*sign s x.val.2*
  (if s.perm x.val.1 < s.perm x.val.2 then 1 else -1)
lemma scar_abs (s:Signed)(x:PlaqAxes): |spinScar s x|=1:=by unfold spinScar sign; split_ifs<;>norm_num
lemma scar_sq (s:Signed)(x:PlaqAxes): spinScar s x*spinScar s x=1:=by unfold spinScar sign; split_ifs<;>norm_num
local notation "re" s:max=> PlaqAxes.transform s
noncomputable def costSkate (s:Sweep n)(F:Skate):Skate:= fun x y=> let d:=(re s.s).symm x; let e:=(re s.s).symm y; (spinScar s.s d*spinScar s.s e) • cast_B (wageZ s⁻¹) (F d e)
lemma cost_price (s:Sweep n)(F:Skate)(x y:PlaqAxes) : costSkate s F ((re s.s) x) ((re s.s) y)=(spinScar s.s x*spinScar s.s y) • cast_B (wageZ s⁻¹) (F x y):=by simp [costSkate]
lemma cornerFlux {G:Gauge}(s:Signed)(b:PlaqAxes)(h:Flux G) : reframe h s b= spinScar s b • h ((re s) b):=by
 unfold spinScar reframe; let i:= s.perm b.val.1; let j:=s.perm b.val.2
 rcases lt_or_gt_of_ne (show i≠j from s.perm.injective.ne b.property.ne) with p|p
 · unfold i j at p; simp only [orderedDir,p,not_lt_of_gt p,↓reduceDIte,sub_zero, ↓reduceIte,mul_one]; apply congrArg; refine congrArg h (Subtype.ext ?_); change (i,j)=(min i j,max i j); rw [min_eq_left p.le, max_eq_right p.le]
 unfold i j at p; simp only [orderedDir,p,not_lt_of_gt p, ↓reduceDIte,zero_sub, ↓reduceIte,mul_neg,mul_one,smul_neg,neg_smul]; apply congrArg Neg.neg; apply congrArg; refine congrArg h (Subtype.ext ?_); change (j,i)= (min i j,max i j); rw [min_eq_right p.le,max_eq_left p.le]
lemma rampFlux {G:Gauge}(i:PlaqAxes)(s:Signed) : reframe (Averaging.ray (G:=G) ((re s) i)) s=spinScar s i • Averaging.ray i:=by
 funext j; rw [cornerFlux]; simp only [Averaging.ray,Equiv.apply_eq_iff_eq,Pi.smul_apply]; split; rename_i p; rw [p]; simp
lemma rampPrice {G:Gauge} (q : PlaqAxes → PlaqAxes → ℝ) (hG : G.Simple) (a b : PlaqAxes) (u v : ℝ) :
    AnalyticBridge.VerifiedReset.quad q (u • (Averaging.ray a (G:=G))) (v • Averaging.ray b) = q a b * (u*v) := by
  -- as in VerifiedReset/Isotropy
  rw [AnalyticBridge.VerifiedReset.quad, Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]; swap
  · intro x _ hx; simp [Averaging.ray,hx]
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ _)]; swap
  · intro y _ hy; simp [Averaging.ray,hy]
  simp [Averaging.ray,real_inner_smul_left,real_inner_smul_right,spike_norm hG,mul_comm v u]

abbrev phaseB (s:Sweep n):= cast_B (wageZ s⁻¹)
lemma life_step (s:Sweep n)(f:InkD n) : Taxi.lifeH (step_F s f)= (phaseB s) ∘ (Taxi.lifeH f) ∘ flashA s:=funext fun i=> Beau.pot_Z s⁻¹ (f (flashA s i))
private lemma tooth_step (s:Sweep n) (g:s∈cycleSweep n) (v:s.charge=false)(F:Scree.Hub n)(f:InkD n)(p:PressB P (moveHub s F) f h c)(hx:0≤h)(Z:4 ≤ (More n).val)(he:Nonwrapping (moveHub s F).val.2 (moveHub s F).val.1):
 tooth F.val.1 P (step_F s f) = costSkate s (tooth (moveHub s F).val.1 P f) :=by
 funext i j; obtain ⟨k,rfl⟩:=(re s.s).surjective i; obtain ⟨l,rfl⟩:=(re s.s).surjective j
 rw [cost_price]; let X:= moveHub s F; let G:= step_F s f; let i:=(re s.s) k; let j:=(re s.s) l; let t:=Thera.yet_one
 have hd(L:ℂ→L[ℝ]ℝ) : L (tooth F.val.1 P G i j)=(spinScar s.s k*spinScar s.s l)*L (phaseB s (tooth X.val.1 P f k l)):=by
    let A:=(assembly n).embed s.b; let M:= L.comp (phaseB s); let Vx:=M ∘ lifeH f; let W:=L ∘ lifeH G
    have heW: W= Vx ∘ pull s.s A:=by unfold W; rw [show G=step_F s f from rfl,life_step s f]; refine funext fun y=>?_ ; simp only [Function.comp_apply,revoke,v]; rfl
    rw [cym P G F (consume_Q P s _ _ g p hx) hx L i j]; change _= _*M (tooth _ P f k l); rw [cym P f X p hx]
    have hu (a b:Flux SU.group): AnalyticBridge.VerifiedReset.quad (AnalyticBridge.VerifiedReset.coeff W F.val.1) a b=AnalyticBridge.VerifiedReset.quad (AnalyticBridge.VerifiedReset.coeff Vx X.val.1) (reframe a s.s) (reframe b s.s):=by
       let D:=(pintK P); have hc:= (show D.Regular X.val.2 Vx from (cashR _ X p hx M _ le_rfl).regular); have hy:= flux_hessian_pull s.s A X.val.1 t hc he Z a b
       rw [←heW,← (chart_p s F).1] at hy; rw [flux_formula _ t (show D.Regular F.val.2 W from (cashR _ F (consume_Q P s _ _ g p hx) hx L _ le_rfl).regular),flux_formula _ t hc] at hy; exact hy
    have hy:= hu ((1:ℝ) • Averaging.ray i) ((1:ℝ) • Averaging.ray j); rw [rampPrice _ t,one_smul,one_smul,rampFlux k s.s,rampFlux l s.s,rampPrice _ t,one_mul,mul_one] at hy; change AnalyticBridge.VerifiedReset.coeff W F.val.1 i j*_=_; rw [hy]; ring
 refine Complex.ext ?_ ?_
 · change _=Complex.reCLM ((spinScar s.s k*spinScar s.s l) • _); rw [map_smul]; exact hd Complex.reCLM
 change _=Complex.imCLM ((spinScar s.s k*spinScar s.s l) • _); rw [map_smul]; exact hd Complex.imCLM

-- charge component. cf Mica/Sleet and Taxi/Pout.pure_e
open Beau
open Reef
private lemma roseB (t:Bool)(u: Skye.Seat n)(c: PlaqAxes)(x:SU.group.Color):
 cape_v t ((AnalyticBridge.VerifiedReset.wedge c x).field u)=(AnalyticBridge.VerifiedReset.wedge c (if t then Reef.frolic x else x)).field u:=by
 cases t; rfl
 change Reef.cloak _ _=_; funext i; unfold Reef.cloak; simp only [ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,wedge_field,ite_true]; split_ifs; exact Reef.frolic.map_smul _ _; exact Reef.frolic.map_zero
lemma tooth_echo (s:Sweep n) (F:Scree.Hub n)(f:InkD n)(p:PressB P F f h c)(hx:0≤h)(i j:PlaqAxes):
 tooth F.val.1 P (step_F (τV s) f) i j= phaseB (τV s) (tooth F.val.1 P f i j):=by
 let X:= F.val.1; let G:= step_F (τV s) f; let H:=phaseB (τV s)
 let T:=Thera.yet_one; have hz(c:Bool): ‖(if c then Reef.frolic (AnalyticBridge.VerifiedReset.spike SU.group) else AnalyticBridge.VerifiedReset.spike SU.group)‖=1:=by cases c<;>simp [spike_norm T,Reef.frolic.norm_map]
 have hd(L:ℂ→L[ℝ]ℝ) : L (tooth X P G i j)=L (H (tooth X P f i j)):=by
    let M:=L.comp H; let A:= M ∘ lifeH f; let B:= L ∘ lifeH G; have hc:= (cashR _ F p hx M _ le_rfl).regular; let W:= cape_v (n:=n) s.charge
    change L (tooth F.val.1 P _ i j)=M (tooth F.val.1 P _ i j); rw [cym P G F (consume_Q P (τV s) _ _ (show Beau.τV s ∈ cycleSweep n from quad_id) ((cupE s F).symm ▸ (show PressB P F _ _ _ from p)) hx) hx, cym P f F p hx]; refine congrArg (· * P.threshold^2) ?_
    have he : AnalyticBridge.VerifiedReset.germ B= AnalyticBridge.VerifiedReset.germ A ∘ W:= funext fun y=>by change L (lifeH G _)=_; unfold G; rw [life_step,Function.comp_apply,Function.comp_apply, Beau.warP]; rfl
    let z:=AnalyticBridge.VerifiedReset.spike SU.group; let w(i:PlaqAxes):=(AnalyticBridge.VerifiedReset.wedge i z).field X
    have hh:logHessian B (w i) (w j)=logHessian A (W (w i)) (W (w j)):=by
       let U:= ![w i,w j]; change iteratedFDeriv ℝ 2 (AnalyticBridge.VerifiedReset.germ B) _ U=_; rw [he, jets_linear W (f:=AnalyticBridge.VerifiedReset.germ A) (k:=2) (by exact AnalyticBridge.VerifiedReset.germ_diff hc)]
       change iteratedFDeriv ℝ 2 _ _ (fun k=> W (U k)) =_; rw [show (fun k:Fin 2=>W (U k))= (![W (w i),W (w j)]:Fin 2→tangD n) from funext fun k=> by fin_cases k <;>rfl]; rfl
    change logHessian B (w i) (w j)=_; rw [hh,roseB s.charge X i z,roseB s.charge X j z, label_color X T hc]
    unfold z; rw [real_inner_self_eq_norm_sq,hz _,one_pow,mul_one]
 exact Complex.ext (hd Complex.reCLM) (hd Complex.imCLM)
lemma tooth_cost (s:Sweep n)(g:s∈cycleSweep n)(F:Scree.Hub n)(f:InkD n)(p:PressB P (moveHub s F) f h c)(hx:0≤h)(Z:4 ≤ (More n).val)(he:Nonwrapping (moveHub s F).val.2 (moveHub s F).val.1):
 tooth F.val.1 P (step_F s f) = costSkate s (tooth (moveHub s F).val.1 P f) :=by
 let u:=τR s; let v:=τV s; have hg:u*v=s:=sash s; let X:=moveHub u F; have hp : X=moveHub s F:=((cupE s (moveHub u F)).symm.trans (step_k ..)).trans (congrArg (moveHub · F) hg)
 have hs: step_F s f=step_F u (step_F v f):=by funext i; simp only [step_F,Function.comp_apply,lights,hg,moon_Y]; rw [←mul_inv_rev,hg]
 let A:=consume_Q P v X c (cycleQ _|>.mpr quad_id) ((cupE s X).symm ▸ (show PressB P X f h c from (hp.symm ▸ p))) hx -- need rewrite cupE
 rw [hs,tooth_step u (cycleQ _|>.mpr ((cycleQ _).mp g)) rfl F _ A hx Z (hp.symm ▸ he)]
 funext i j; obtain ⟨i,rfl⟩:= (re u.s).surjective i; obtain ⟨j,rfl⟩:= (re u.s).surjective j
 rw [cost_price]; have hq:=p; rw [← hp] at hq; rw [tooth_echo s X f hq hx]; change _= costSkate s _ ((re s.s) _) ((re s.s) _); rw [cost_price]; apply congrArg (fun z:ℂ=> (spinScar s.s i*spinScar s.s j) • z); rw [show (phaseB v)=(cast_B (wageZ v⁻¹)) from rfl,castT,castT,castT]; change payZ u⁻¹ (payZ v⁻¹ (tooth X.val.1 P f i j)) = payZ s⁻¹ (tooth _ _ _ i j); rw [hp,←hg,mul_inv_rev,←warX]; -- oops payZ order, hp unfolded s in RHS, correct after commute
 unfold Spire.payZ; rw [sign_seq,sign_seq,Bool.xor_comm (wageZ u⁻¹)]
end YM.CF.QuadClock
