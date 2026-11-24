import YM.CF.Vp929.Canon.Moss
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
-- directional wave estimate. coord centered lift at anchor site. increment subgroup RollH.
variable {q:ℝ} {L n:Side} {P:BudgetPoint}
local notation "J_"=> spike SU.group
local notation "It"=> Skye.Seat n
local notation "b"=> (More n).val
local notation "cd"=> AnalyticBridge.VerifiedReset.coord
abbrev rtape (q:ℝ)(x:It):= q*(lift x 0:ℝ)
abbrev blade (q:ℝ)(x:It) :ℝ:= Real.sin (rtape q x)/q
abbrev tileX : Lattice.PlaqAxes:= ⟨(0,1),by decide⟩
lemma sin_relay (h:Frequency L n q)(X Y:Cover)(t:wrap (More n) X=wrap (More n) Y)(d:ℝ):Real.sin (q*(X 0:ℝ)+d)=Real.sin (q*(Y 0:ℝ)+d):=by
 have ht:wrap (More n) (X-Y)=0:=by rw [map_sub,t,sub_self]
 obtain ⟨i,z⟩:=((ZMod.intCast_zmod_eq_zero_iff_dvd ((X-Y) 0) _).mp (congr_fun ht 0))
 obtain ⟨k,e⟩:= h.gauge; let o:= (k:ℤ)*i; have hp: (X 0:ℝ)- (Y 0:ℝ)=(b:ℝ)*(i:ℝ):=by exact_mod_cast z
 have hB:(b:ℝ)≠0:=by exact_mod_cast (More n).pos.ne'
 rw [show q* (X 0:ℝ)+d=q*(Y 0:ℝ)+d+ (o:ℝ)*(2*Real.pi) by rw [show (X 0:ℝ)=(b:ℝ)*(i:ℝ)+(Y 0:ℝ) by linarith,e]; unfold o; push_cast; field_simp <;> ring, Real.sin_add_int_mul_two_pi]
lemma sin_anchor (h:Frequency L n q)(x y:It)(d:ℝ) : Real.sin (rtape q y+d)=Real.sin (rtape q x+q*cd x y 0+d):=by
 have hp : wrap (More n) (lift y) = wrap (More n) (lift x+lift (y-x)):=by simp;
 convert sin_relay h (lift y) _ hp d using 2
 unfold rtape AnalyticBridge.VerifiedReset.coord; rw [Pi.add_apply,Int.cast_add]; ring
private lemma blade_lift (h:Frequency L n q)(x y:It): |blade q y-blade q x|≤ separation y x:=by
 unfold blade; rw [show Real.sin (rtape q y)=Real.sin (rtape q x+q*cd x y 0) from ?_,←sub_div,abs_div,abs_of_pos h.pos]; rotate_left
 · simpa only [add_zero] using sin_anchor h x y 0
 apply (div_le_iff₀ h.pos).2; apply (Real.abs_sin_sub_sin_le ..).trans; rw [add_sub_cancel_left,abs_mul,abs_of_pos h.pos]; exact (mul_le_mul_of_nonneg_left (small_coord x y _) h.pos.le).trans_eq (mul_comm ..)
lemma blade_amp (h:Frequency L n q)(x:It): |blade q x|≤ b:=by
 have hv:=h.pos; unfold blade; rw [abs_div,abs_of_pos hv]; apply (div_le_iff₀ hv).2; obtain ⟨k,e⟩:=h.gauge; apply (Real.abs_sin_le_one _).trans; rw [e]
 have he: k≥1:= Nat.pos_of_ne_zero fun t=> by rw [t] at e; simp at e; exact hv.ne' e;
 have hB:(b:ℝ)≠0:=by exact_mod_cast (More n).pos.ne'
 rw [show (b:ℝ)*((k:ℝ)*(2*Real.pi/(b:ℝ)))=2*Real.pi*k by field_simp <;> ring]; have hp:(k:ℝ)≥1:=by exact_mod_cast he
 nlinarith [Real.pi_gt_three]
private lemma sinSec (a c:ℝ): |Real.sin (a+c)-Real.sin a-Real.cos a*c|≤c^2:=by
 let f(x:ℝ):= Real.sin x-Real.cos a*x; have H(x:ℝ): HasDerivAt f (Real.cos x-Real.cos a) x:= by convert (Real.hasDerivAt_sin x).sub ((hasDerivAt_id' x).const_mul (Real.cos a)) using 1 <;> (first| rfl| simp [f]| trivial)
 have hp:= (convex_closedBall a |c|).norm_image_sub_le_of_norm_deriv_le (s:=closedBall a |c|) (fun i _=> (H i).differentiableAt) (C:=|c|) (fun i w=> show ‖deriv f i‖ ≤ _ from (H i).deriv.symm ▸ (Real.abs_cos_sub_cos_le i a).trans (show _≤_ from w)) (mem_closedBall_self (abs_nonneg _)) (y:=a+c) (by rw [mem_closedBall,Real.dist_eq,add_sub_cancel_left]); rw [show _-Real.sin a-_=f (a+c)-f a by unfold f; ring]; exact hp.trans_eq (by rw [add_sub_cancel_left,Real.norm_eq_abs,←sq,sq_abs])
private lemma blade_slope (h: Frequency L n q)(x y:It): |blade q y-blade q x - cd x y 0*Real.cos (rtape q x)|≤ q*(separation y x:ℝ)^2 :=by
 let d:= cd x y 0; let a:= rtape q x; have hp:=sinSec a (q*d); have he:Real.sin (rtape q y)=Real.sin (a+q*d):=by simpa [a,d] using sin_anchor h x y 0
 have H:= h.pos
 change |_-_-d*Real.cos a| ≤ _; rw [show blade q y-_-d*Real.cos a=(Real.sin (a+q*d)-Real.sin a-Real.cos a*(q*d))/q by unfold blade; rw [he]; unfold a; field_simp <;> ring, abs_div,abs_of_pos H]; apply (div_le_iff₀ H).2; refine hp.trans ?_; have hf: d^2≤ (separation y x:ℝ)^2:=by rw [←sq_abs d]; gcongr; exact small_coord ..
 nlinarith [sq_nonneg q]
-- Adjust wave by pure gauge. Coarser crossing estimate b*(2r+1).
abbrev score (q:ℝ) (x:Edge It):=if x.2=1 then blade q x.1 else 0
abbrev wand (q:ℝ)(o:It)(x:Edge It):= score q x - blade q o*(cd o (x.1+Lattice.step x.2) 1-cd o x.1 1)
def pitch (q:ℝ)(o:It) : tangD n:=fun x=> wand q o x • J_
lemma jaunty (q:ℝ)(x:It)(t:ℝ):Lattice.gauge (fun y=> Cascade.rollH J_ (t*blade q x*cd x y 1)) (increment 1 (t • transverse q))=increment 1 (t • pitch q x):=by
 funext i; have he:(transverse q i:SU.group.Color)=score q i • J_:=by unfold transverse score; split_ifs; rfl; rw [zero_smul]
 let r:= i.1+Lattice.step i.2
 change ( _*(SU.group.lieExp (t • transverse q i)*1))*_=(SU.group.lieExp (t • (wand q x i • J_))*1)
 rw [mul_one,mul_one,he,smul_smul,smul_smul]; change Cascade.rollH J_ _ * Cascade.rollH J_ _ * (Cascade.rollH J_ (t*blade q x*cd x r 1))⁻¹ = Cascade.rollH J_ _; rw [Cascade.roll_inv, ←Cascade.rollAdd,←Cascade.rollAdd]; congr 1; unfold wand r; ring
private lemma wandLocal (q:ℝ)(x:It)(e:Edge It)(h:10*separation e.1 x < b)(hb:4≤ b) : wand q x e=if e.2=1 then blade q e.1-blade q x else 0:=by
 unfold wand score; rw [coord_step h hb]; by_cases he:e.2=1 <;> simp [he,eq_comm]
def soundX(q:ℝ)(o:It): tangD n:= fun e=> if e.2=1 then ((blade q e.1 - blade q o) • J_) else 0
def tiltX(q:ℝ)(o:It): tangD n:= (AnalyticBridge.VerifiedReset.wedge tileX (Real.cos (rtape q o) • J_)).field o
lemma affineTilt(q:ℝ)(o:It): IsAffineDirection o (tiltX q o):= (AnalyticBridge.VerifiedReset.LinearJet.isAffine o).2 ⟨_,rfl⟩
lemma meet (V:Vast L.val P.B n) (X:Scree.Hub n) (t:shortHub P L.val X) (hB:4≤ b): Agrees X.val.2 (pitch q X.val.1) (soundX q X.val.1):=by
 intro i v w; unfold pitch soundX; rw [wandLocal _ _ _ (V.unwrap L.val X t i.1 v) hB,ite_smul,zero_smul]
lemma pitch_L (hb:4≤ b)(h:Frequency L n q)(o:It)(e:Edge It): ‖pitch q o e‖≤300*(1+(separation e.1 o:ℝ))^2:=by
 unfold pitch; rw [norm_smul,spike_norm Thera.yet_one,Real.norm_eq_abs,mul_one]
 let d:ℝ:= separation e.1 o; have hu:0≤d:=by unfold d; positivity
 by_cases ht: 10*separation e.1 o < b
 · rw [wandLocal _ _ _ ht hb]; split; exact (blade_lift h _ _).trans (by change d≤ 300*(1+d)^2; nlinarith); rw [abs_zero]; positivity
 let m:ℝ:= b; have hm:m ≤ 10*d:=by unfold m d; exact_mod_cast (le_of_not_gt ht)
 let x:=e.1+Lattice.step e.2; have hw(i:It): |cd o i 1|≤ m:=by
    unfold AnalyticBridge.VerifiedReset.coord;
    have e:=lift_centers (i-o) 1; unfold m; exact_mod_cast (show |lift (i-o) 1|≤ (b:ℤ) by rw [abs_le]; omega)
 have he: |score q e| ≤ m:=by unfold score; split; apply blade_amp h; rw [abs_zero]; unfold m; positivity
 unfold wand; apply (abs_sub ..).trans; rw [abs_mul]; calc
    _ ≤ m+m*(m+m):= by gcongr; exact blade_amp h _; exact (abs_sub ..).trans (add_le_add (hw _) (hw _))
    _ ≤ _ := by change _ ≤300*(1+d)^2;
                have H:0≤ m:=by unfold m; positivity
                nlinarith
lemma sound_L (h:Frequency L n q)(o:It)(e:Edge It): ‖soundX q o e‖≤ separation e.1 o:=by
 unfold soundX; split; · rw [norm_smul,spike_norm Thera.yet_one,mul_one]; exact blade_lift h o e.1
 rw [norm_zero]; positivity
private lemma tilt_at (o:It)(e:Edge It) : tiltX q o e = if e.2=1 then (cd o e.1 0* Real.cos (rtape q o)) • J_ else 0:=by
 unfold tiltX; rw [AnalyticBridge.VerifiedReset.wedge_field]; dsimp only [tileX]; simp [smul_smul,eq_comm]
lemma tilt_L (o:It)(e:Edge It): ‖tiltX q o e‖≤ separation e.1 o:=by
 rw [tilt_at]; split
 · rw [norm_smul,spike_norm Thera.yet_one,Real.norm_eq_abs,mul_one,abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans (small_coord ..)
 rw [norm_zero]; positivity
lemma difference_L(h:Frequency L n q)(o:It)(e:Edge It): ‖soundX q o e-tiltX q o e‖≤ q*(1+(separation e.1 o:ℝ))^2:=by
 unfold soundX; rw [tilt_at]; split_ifs
 · rw [←sub_smul,norm_smul,spike_norm Thera.yet_one,mul_one]; exact (blade_slope h o e.1).trans (mul_le_mul_of_nonneg_left (by gcongr; exact le_add_of_nonneg_left zero_le_one) h.pos.le)
 have hv:=h.pos; rw [sub_self,norm_zero]; positivity
end Test
end YM.CF.Py.Rate
