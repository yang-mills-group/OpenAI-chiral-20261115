import YM.SU5.Fineness.Stitch
import SatinThinWheel
set_option autoImplicit false
set_option maxHeartbeats 164000
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
open Pitching.Focus AnalyticBridge.Annulus1AD
local notation "H'"=> Pannier.halfLie SU.group
variable {P}
private lemma logMeritDrive (L:Side) (M:ℝ)(z:ℝ)(p:z>0)(h:0<M): ∀ᶠ x:ℝ in atTop,∀ a b:ℝ,x/2 ≤ a→ x/2≤b → |a-b| ≤ M → |Real.log a-Real.log b| ≤ z* merit L x :=by
 let r:= billX L
 have hf:Tendsto (fun x=> Real.sqrt (Scales.y SU.group L x)) atTop atTop:= Real.tendsto_sqrt_atTop.comp (Scales.year SU.group L)
 filter_upwards [eventually_ge_atTop r,eventually_gt_atTop (4:ℝ), hf.eventually_ge_atTop 2, merit_size L (z/4) (by positivity) _ ((sizeK.main L).square 2|>.low (k:=1) (by omega)|>.scale M)] with x ht hz hb hF a b hA hB H
 let y:=(x+r); let k:=Real.sqrt y; let m:= merit L x
 have hp:0<x:= lt_trans (by norm_num) hz
 have hw:0<y:= add_pos_of_pos_of_nonneg hp (Vale.pitch _)
 have he:0< m:=merit_pos L hw
 have hE : M≤(z*m)*x/2:= by
    let g:=(Scales.g SU.group L x); have hv:y*g^2=1:=yg2 SU.group L hw
    change |M*g^2| ≤ z/4*m at hF; have hh:= mul_le_mul_of_nonneg_right ((le_abs_self _).trans hF) hw.le; have he':y≤2*x:=by unfold y; linarith only [ht]
    nlinarith only [hh,hv, he',he,p,mul_le_mul_of_nonneg_right he' (mul_nonneg p.le he.le), congr_arg (fun x => M*x) hv]
 rw [abs_le] at H ⊢
 have he{a b:ℝ}(hA:x/2≤a)(hB:x/2≤b)(t:a-b≤M): Real.log a-Real.log b≤z*m:=by
    have ha:0<a:= lt_of_lt_of_le (half_pos hp) hA; have hb:0<b:=lt_of_lt_of_le (half_pos hp) hB
    rw [← Real.log_div ha.ne' hb.ne']; refine (Real.log_le_sub_one_of_pos (div_pos ha hb)).trans (sub_le_iff_le_add.mpr ((div_le_iff₀ hb).mpr ?_)); nlinarith only [t,hE, mul_le_mul_of_nonneg_right hB (mul_nonneg p.le (show 0≤ m from he.le))]
 refine ⟨neg_le.mp ?_,he hA hB H.2⟩; rw [neg_sub]; exact he hB hA (by linarith only [H.1])
lemma entryFuelMerit (Q : Grace K R L)(H: LocalRatio L) (M:ℝ)(z:ℝ)(p:z>0)(t: M>0): ∀ᶠ x:ℝ in atTop,∀ a b:ℝ,x/2≤a → x/2≤b →|a-b| ≤ M → ∀ i n F,|entryFin Q i n F a - entryFin Q i n F b|≤ z* merit R.L x * sites n:=by
 let f:=H'+1; have hf : 0≤ H':=Pannier.pen_log_nonneg _; have he:0<f:= add_pos_of_nonneg_of_pos hf zero_lt_one; let e:= z/(3*f)
 filter_upwards [eventually_gt_atTop (0:ℝ), logMeritDrive R.L M e (div_pos p (by positivity)) t] with x ht hx a b ha hb hΔ i n F
 have hh:=hx a b ha hb hΔ; let W:=sites n; have hw:1 ≤ W:=sites_pos n
 have hp: entryFin Q i n F a-entryFin Q i n F b= -(H'*(Real.log a-Real.log b)* (3*(W-1))):=by
    unfold entryFin Fineness.gaugedBase; rw [spare_formula _ H.scale ((half_pos ht).trans_le ha),spare_formula _ H.scale ((half_pos ht).trans_le hb),Pannier.shadowLie, sites_as_price]; unfold W; ring
 rw [hp, abs_neg,abs_mul,abs_mul,abs_of_nonneg hf,abs_of_nonneg (show 0≤3*(W-1) by linarith only [hw])]; calc
    _ ≤ (H'*(e*merit R.L x))*(3*W):=by
       have h_X:0< merit R.L x:= merit_pos R.L (add_pos_of_pos_of_nonneg ht (Vale.pitch _)); have h_Y: e>0:= by unfold e; positivity
       gcongr <;> linarith
    _ ≤ (f*(e*merit R.L x))*(3*W):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (mul_nonneg (div_nonneg p.le (by positivity)) (Real.sqrt_nonneg _))) (by positivity)
    _ = _:= (by change _=z* merit R.L x* W; unfold e; field_simp)
/- slope estimate adapted to favor linear recursion -/
theorem merit_hat_stride (R:Patch)(z:ℝ)(h:Tendsto (hat R.L z) atTop atTop):
 let Q(s):=merit R.L (hat R.L z s); ∀ᶠ s in atTop, Q s>0 ∧ Q s ≤2* Q (s+1):=by
 intro Q
 let X:= hat R.L z; let B:= billX R.L
 have hv:B≥0:=Vale.pitch _
 filter_upwards [h.eventually_gt_atTop 0] with s p
 let Z:= X s+B; let Y:= Z+B; have ht:0<Z:=add_pos_of_pos_of_nonneg p hv; have ht':0<Y:=add_pos_of_pos_of_nonneg ht hv; have hp:Y ≤ 2*Z:=by unfold Y Z; linarith only [p]
 have hY: (Scales.y SU.group R.L (X (s+1)))=Y:= by rw [show X (s+1)=X s+B from hat_succ ..]; rfl
 refine ⟨merit_pos R.L ht,?_⟩
 let q:= Next.Scheduling.Clock.gap Z; let v:= Next.Scheduling.Clock.gap Y
 have hx: q ≤ 2*v:=by
    let f:=Real.sqrt Z; let g:=Real.sqrt Y
    change f⁻¹≤2*g⁻¹; rw [← div_eq_mul_inv, ← one_div]; apply (div_le_div_iff₀ (Real.sqrt_pos.mpr ht) (Real.sqrt_pos.mpr ht')).mpr; nlinarith [Real.sq_sqrt ht.le, Real.sq_sqrt ht'.le,Real.sqrt_pos.mpr ht]
 change Real.sqrt q ≤2*merit R.L (X _); unfold Scales.merit Scales.g; rw [hY]
 let A:= Real.sqrt q; let E:=Real.sqrt v; have hf:0<A:=Real.sqrt_pos.mpr (Next.Scheduling.Clock.gp ht); have hg:0<E:=Real.sqrt_pos.mpr (Next.Scheduling.Clock.gp ht')
 nlinarith only [hf,hg,hx, Real.sq_sqrt (Next.Scheduling.Clock.gp ht|>.le), Real.sq_sqrt (Next.Scheduling.Clock.gp ht'|>.le)]
/-- Every polynomial in the *unshifted* watch at height argument is still permitted after paying merit -/
theorem merit_any (L:Side) (k:ℕ) : Tendsto (fun x:ℝ => Next.Scheduling.Clock.watch 2 x^k* merit L x) atTop (𝓝 0):= by
 apply squeeze_zero' _ _ (earning L k)
 · filter_upwards [(Scales.year SU.group L).eventually_gt_atTop 0] with x h; exact mul_nonneg (pow_nonneg (Next.Scheduling.Clock.wp ..).le _) (merit_pos L h|>.le)
 filter_upwards [ ((Next.Scheduling.Clock.clock)).eventually_ge_atTop 0,eventually_gt_atTop (1:ℝ)] with x h ht
 refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Next.Scheduling.Clock.wp ..).le ?_ _) (Real.sqrt_nonneg _)
 unfold Scales.p; rw [Next.Scheduling.Clock.watch_two,Next.Scheduling.Clock.watch_two]; apply Real.exp_monotone; apply pow_le_pow_left₀ h; apply Real.log_le_log (Real.log_pos ht); exact Real.log_le_log (by linarith) (le_add_of_nonneg_right (Vale.pitch L))

-- density monotonic growth; compression factor does not normalize by |Γ|
lemma height_meritEarns (Q: Grace K R L)(B:Side) (x:ℝ) : ∀ (C q:ℝ),0 < q → ∀ᶠ i in (atTop :Filter ℕ), ∀ m, C ≤ (q*merit R.L (hat R.L x i))*sites (cell m B R.L i):=by
 intro C q h
 let X:= hat R.L x; let U(n):= merit R.L (X n)
 let relation(n:ℕ):=∀ m:Side, let v_n:= cell m B R.L n; 2*(U n* sites v_n) ≤ U (n+1)*sites (cell m B R.L (n+1))
 have v₁:(4:ℝ)≤ (R.L.val:ℝ)^4:= by
    have hx:2 ≤ (R.L.val:ℝ):= by exact_mod_cast (show 2≤R.L.val from le_trans (by decide) Q.tallX)
    calc (4:ℝ)≤ 2^4:= by norm_num
         _ ≤ _:= pow_le_pow_left₀ (by norm_num) hx _
 obtain ⟨N,hN⟩:= eventually_atTop.mp (merit_hat_stride R x (stage_slope Q x)|>.mono (p:=fun s=>_) (q:=fun n=>0 < U n ∧ relation n) -- tune
     fun n ⟨u,v⟩=>by
        refine ⟨u, fun m=>?_⟩; intro v_n; rw [show sites (cell m B R.L (n+1))= (R.L.val:ℝ)^4*sites v_n from ?_]; let V:=sites v_n; change 2*(U n*V)≤ U (n+1)*(_*V); have f: 0 ≤ V:=zero_le_one.trans (sites_pos _); nlinarith only [show 0≤ U (n+1) from Real.sqrt_nonneg _,v₁, mul_le_mul_of_nonneg_right (show _ from v) f, mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right v₁ f) (show 0≤ U (n+1) from Real.sqrt_nonneg _)]
        unfold sites v_n cell CSide More; rw [mesh_succ]; push_cast; ring)
 let u:=U N; have hu: u>0:= (hN _ le_rfl).1
 have v(n:ℕ):∀ m,2^n*u≤ U (N+n)* sites (cell m B R.L (N+n)):=by
    intro m; induction n with
    | zero => rw [pow_zero,one_mul,Nat.add_zero]; exact le_mul_of_one_le_right hu.le (sites_pos _)
    | succ n ih=>
       rw [← Nat.add_assoc]; exact ((hN _ (Nat.le_add_right N n)).2 m).trans' ((by rw [pow_succ]; linarith only [ih]) :2^(n+1)*u ≤ 2*(U (N+n)* sites (cell m B R.L (N+n))))
 have hg:= ((Tendsto.const_mul_atTop h (Tendsto.atTop_mul_const hu (tendsto_pow_atTop_atTop_of_one_lt (by norm_num:(2:ℝ)>1)))).eventually_ge_atTop C)
 obtain ⟨k,hk⟩:= eventually_atTop.mp hg; filter_upwards [eventually_ge_atTop (N+k)] with s t m; obtain ⟨r,rfl⟩:= Nat.exists_eq_add_of_le (show N ≤ s by omega); rw [mul_assoc]; exact (hk r (by omega)).trans (mul_le_mul_of_nonneg_left (v r m) h.le)
open Fineness
namespace Branch
local notation "X"=> hat R.L x
variable {A:Branch W m k x N0}
variable {i:ℕ}{α:ℝ}(p:Hallway J q h P N0) (a:Bon J q h D delay A)(H:Service V U W J q h D C R0 P N0 delay)
local notation "ζ" n:max=> sites (cell m B R.L n)
local notation "dL" => 8* H'*Real.log R.L.val
include p H
lemma brakeMerit (E:LocalRatio L)(s:ℝ)(hv:s>0):∀ᶠ i in atTop,∀ (m:Side)(k:ℕ)(A:Branch W m k x N0)(b:Bet k), Bon J q h D delay A → Solved P A α b→ A.last.music W.z → i<k →
 let G: ℕ→ℝ := fun n=>entryFin V (k-n) (cell m B R.L n) (A.gram P b n).J ((A.gram P b n).beta); let Z(n):=(A.gram P b n).v.re; |(Z i-Z (i+1))-(G (i+1)-G i)| ≤ s*merit R.L (hat R.L x i)*sites (cell m B R.L i):=by
 let C':= dL; let d:= s/3; have ht:d>0:= div_pos hv (by norm_num); let M:=guardFee (W:=W); let T':=1+|M|
 filter_upwards [(stage_slope V x).eventually (p.toll d ht), height_meritEarns V B x |dL| d ht, (stage_slope V x).eventually (entryFuelMerit V E T' d ht (by unfold T'; positivity))] with i u h ξ m k A b t c a e G Z
 let X₀:=A.toSpine.address i; let F:=A.gram P b; let v:= (b.read (i+1)).re; let Hφ:=A.active P b i; let w:=A.corr P b (i+1); let U₀:= A.offset P b (i+1); let P':=A.op P i
 obtain ⟨hu,hκ,hA⟩:= yearFit t H c e a; let G':= entryFin V (k-i) _ (F i).J v
 have hpV:|G' - G i| ≤ d*merit R.L (hat R.L x i)*sites (cell m B R.L i):=ξ v (F i).beta hu hκ ((by rw [abs_sub_comm]; exact hA.trans ((le_abs_self M).trans (le_add_of_nonneg_left zero_le_one))) : |v-(F i).beta| ≤ T') _ _ _
 have H₀: Heed V X₀ (d*merit R.L (hat R.L x i)) v U₀ (F i).v :=by
    have hr:=u _ _ _ _ _ (t.request i e) v w.1 (hat_step i ▸ (t.beta_ok H c.toRealQ (i+1) e).2) (t.flow (t.charged H c.toRealQ (i+1) e)) U₀; change Heed V X₀ (d*merit R.L (hat R.L x i)) v U₀ (A.offset P b i); rw [offset.eq_1 P A b i,dif_pos e]; exact hr
 have hR:crestDue V X₀ v= G (i+1)-G'-C':=by unfold crestDue; change entryFin V (k-1-i) _ _ _-entryFin V (k-1-i+1) _ _ _-_= _; rw [show k-1-i+1=k-i from by omega,show k-1-i=k-(i+1) from by omega]; rfl
 unfold Heed at H₀; rw [hR] at H₀
 have he:=abs_le.mp (h m); change -_ ≤ C'∧C' ≤ d*merit R.L (hat R.L x i)*sites (cell m B R.L i) at he
 change |Z i-Z (i+1)-(G (i+1)-G'-C')| ≤ d*merit R.L (hat R.L x i)*sites (cell m B R.L i) at H₀; rw [abs_le] at hpV H₀ ⊢; unfold d at *; constructor <;> linarith only [he.1,he.2,H₀.1,H₀.2,hpV.1,hpV.2]

end Branch
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Branch.brakeMerit
