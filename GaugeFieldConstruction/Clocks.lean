import GaugeFieldConstruction.Gracile
import GaugeFieldConstruction.Boros
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Oath Roots Riant
open Oath Roots Riant TableF Lenten Layout Fren
open SectorNext.Remainder.Scales Stockpile
open CoeffArc
variable (R:Patch){k:ℕ}
abbrev QLife (x:ℝ) := coin₂ R x
abbrev VLife(x:ℝ):= QLife R (x+Vale.billX R.L)
abbrev ζlife : ℝ:= RamoK R.L
lemma age_w (ε:ℝ)(f:ℝ→ℝ)(p:sizeK R.L 3 f)(h:0<ε):∀ᶠ x in atTop,f x ≤ ε* QLife R x:= (pill_R f h p).mono fun _ h=> le_of_lt h
lemma size_C {k:ℕ}(P:ℝ→ℝ)(h:sizeK R.L (k+2) P):sizeK R.L k fun x=> P x/ QLife R x:=by
 obtain ⟨t,v⟩:=h; refine ⟨t,?_⟩; filter_upwards [(year SU.group R.L).eventually_gt_atTop 0,v] with x u v;
 let V:= QLife R x; let f:=Scales.g SU.group R.L x; have hv:0<f:=gauge SU.group R.L u; have hf:0<V:= pow_pos hv _
 rw [abs_div,abs_of_nonneg hf.le,div_le_iff₀ hf]; exact v.trans (le_of_eq (by rw [pow_add]; unfold V QLife coin₂; ring)) -- tune
lemma wage_growth (P:Pinewood R): sizeK R.L 1 fun x=> WageAge (P.Γ x) (radiusB x) :=by
 let B(x):= degreePrice (radiusB x) (P.Γ x) Sour.wΨ; let Q:= fun x=>(1-B x)⁻¹; have hf:sizeK R.L 1 B:=(fee_Q HI P.Γ P.bank).cost_d (by filter_upwards [hall_l HI] with i p; change |B i| ≤ |zeST HI P.Γ i|; unfold B zeST; rw [p])
 have he: Tendsto Q atTop (𝓝 1):= by simpa only [sub_zero,inv_one] using ((tendsto_const_nhds (x:=1)).sub hf.spine |>.inv₀ (show (1:ℝ)-0≠0 by simp)) -- tune
 exact P.bank.tint ((sizeK.mild R.L 2).cost_d (he.abs.eventually (ge_mem_nhds (by norm_num: |(1:ℝ)| < |(2:ℝ)|)))) -- space
lemma α_year (t:ℝ) : Tendsto (fun x=>coin₂ R (x+t)/coin₂ R x) atTop (𝓝 1):=by
 have hx:= SectorNext.Remainder.Scales.year SU.group R.L
 let u:=Scales.y SU.group R.L
 have he:Tendsto (fun x=> t / u x) atTop (𝓝 0):= tendsto_const_nhds.div_atTop hx
 have hv:Tendsto (fun x=>(1+ t/u x)⁻¹) atTop (𝓝 1):=by simpa only [add_zero,inv_one] using ((tendsto_const_nhds (x:=(1:ℝ))).add he|>.inv₀ (show (1:ℝ)+0≠0 from (by norm_num)))
 refine hv.congr' ?_; filter_upwards [hx.eventually_gt_atTop 0,(hx.comp (Filter.tendsto_atTop_add_const_right _ t tendsto_id)).eventually_gt_atTop 0] with x p v
 have hQ(z:ℝ)(p:0<u z):coin₂ R z= (u z)⁻¹:=by
    calc
       _ = (u z)⁻¹*(u z*coin₂ R z):=by rw [←mul_assoc,inv_mul_cancel₀ p.ne', one_mul]
       _ = _:=by rw [show u z*coin₂ R z=1 from Scales.yg2 SU.group R.L p,mul_one]
 let U:=u x; have hz:0<U:=p; have H₀: u (x+t)=U+t:=by unfold U u Scales.y betaF; ring
 have h:0<U+t:=H₀ ▸ v
 rw [hQ x hz,hQ (x+t) (show 0<u (x+t) from H₀.symm ▸ h), H₀]; change (1+t/U)⁻¹ = (U+t)⁻¹/U⁻¹; field_simp -- tune
lemma trick_Q (C:ℝ)(p:0≤C): ∀ᶠ x in atTop,C* QLife R x ≤ dleaf R.L x:=by
 let F(x):=Scales.g SU.group R.L x; have ht:= Chill_v.cheap (clove_p R) C |>.spine_a; filter_upwards [ht.eventually (ge_mem_nhds zero_lt_one),(year SU.group R.L).eventually_gt_atTop 0,eventually_gt_atTop (0:ℝ)] with x t u v; let A:=F x; have ha:0<A:=gauge SU.group R.L u; have hv:=Work.E09.temp_pos v;
 have hp: C*A ≤ temp x:=by change C*(A/temp x) ≤ 1 at t; rw [←mul_div_assoc,div_le_iff₀ hv, one_mul] at t; exact t
 change _≤_;change C*A^2≤ A*temp x; nlinarith only [mul_le_mul_of_nonneg_right hp ha.le]
-- mixed α small.Patch size.
abbrev TinyF (F:ℝ→ℝ)(x:ℝ):= Roots.hope_E (radiusB x) (F x)
lemma Tiny_P (i:ℕ){F:ℝ→ℝ}(p:sizeK R.L 0 F):sizeK R.L i (TinyF F):= ((wing_x0 (L:=R.L) (a:=1/16) (by norm_num) i|>.tint (sizeK.mild _ Roots.Zprice)).tint p) -- shape signs rfl?
-- Chill_v combined outputs inc Capsule.Of.Service
variable (P:Pinewood R) (G Kf:ℝ→ℝ) {W1 W2 W3 V1:ℝ→ℝ}
variable {R}
abbrev YardK (L:Side):= Directory.Maxi L
abbrev YAge (P:Pinewood R)(x:ℝ):=WageAge (P.Γ x) (radiusB x)
abbrev PrK (r:ℝ)(L:Side)(U:ℝ→ℝ)(n:ℕ)(x:ℝ):=Charges r (YardK L) (U x) (U x) (radiusB x) n
abbrev Pcal (P:Pinewood R)(x:ℝ):= ωCost x*(P.E x+P.D x)
abbrev Gcal (P:Pinewood R)(x:ℝ):=chi_f 6* Pcal P x
abbrev W_star (F:Pinewood R)(L:Side)(r:ℝ)(n:ℕ)(x:ℝ):= Charges r (YardK L) (Gcal F x) (YAge F x) (radiusB x) n
abbrev U_star (b c:ℝ→ℝ)(L:Side)(r:ℝ)(n:ℕ)(x:ℝ):= b x + (WidthP r |c x| (YardK L) (radiusB x) n+hope_E (radiusB x) 0)
abbrev P_star (R: Patch)(r:ℝ)(F:Pinewood R)(n:ℕ)(x:ℝ):= WidthP r (βLo R (QLife R x)) 1 (radiusB x) n+hope_E (radiusB x) (Pcal F x)
lemma PcS (R:Patch) (P:Pinewood R) : sizeK R.L 2 (Pcal P):= (ωCredit (R:=R)).tint (P.earnings.accrue (P.elite.low (by omega)))
variable {P Kf G}
structure ProfileS (P:Pinewood R)(Kf G T:ℝ→ℝ)(n:ℕ) (r:ℝ):Prop where
 milli : ∀  i:ℕ,sizeK R.L i (TinyF (Pcal P)) -- change forall
 milK :∀ i:ℕ,sizeK R.L i (TinyF Kf)
 milW :∀ i:ℕ,sizeK R.L i (TinyF (Gcal P))
 wheel:Chill_v (W_star P R.L r n)
 price :Chill_v (fun x=> PrK r R.L Kf n x / QLife R x)
 cup:Chill_v (U_star G T R.L r n)
-- T*=0 all m via trivial, P_z charges.
variable {X Y:ℝ→ℝ}(p:BladeQ R X Y V1 Kf) (v:Chill_v G)(hX:sizeK R.L 2 W2)
include p v hX
lemma ζDate (P:Pinewood R)(r:ℝ)(t:ℕ):ProfileS P Kf G W2 t r:=by
 let U:= Kf; have hK:sizeK R.L 2 Kf:=p.kF.height_r; have hc:= PcS R P; have hg: sizeK R.L 2 (Gcal P):= hc.scale _; have hp(i):= Tiny_P R i (hc.low (by decide:0≤2)); have hW(i):= Tiny_P R i (hg.low (by decide:0≤2)); have hu(i):=Tiny_P R i (hK.low (by decide:0≤2)); refine ⟨hp,hu,hW,?_,?_,?_⟩
 · unfold W_star Charges WidthP; change Chill_v (fun x=>_+(_+TinyF _ x+TinyF _ x)); exact Chill_v.coin ((wage_growth R P).accrue ((((hg.low (by decide:1≤2)).scale _).accrue (hW 1)).accrue (hW 1))) -- tune parentheses
 · let W(x):= Kf x/ QLife R x; let s (r):= TinyF Kf r/ QLife R r; have he:Chill_v W:=p.mint; have hx:Chill_v s:= Chill_v.coin (size_C R _ (hu 3)); let L:= YardK R.L; let V:ℝ:= t*(r*L)
   unfold PrK Charges WidthP; simp_rw [add_div, mul_div_assoc ((t:ℝ)*(r*YardK R.L)) (Kf _)]; exact (he.noteR (((he.cheap V).noteR hx).noteR hx))
 apply Chill_v.noteR v; refine Chill_v.noteR ?_ ?_
 · unfold WidthP
   have h: sizeK R.L 2 (fun x=>|W2 x|):= Py.lL_p _ _ hX; -- tune
   exact Chill_v.coin (( (h.low (by omega)).scale ((t:ℝ)*(r* YardK R.L))).accrue (Tiny_P R 1 (h.low (by omega))))
 simp_rw [hope_E,mul_zero]; intro i; simp only [mul_zero]; exact tendsto_const_nhds
end Focus
end Pitching
end YM.CF.Py.Rate
end
