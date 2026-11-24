import GaugeFieldConstruction.Acacia
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
lemma followC (L:Side): followV [] L^4=αN L^6:=by
 let v:ℝ:=L.val; have h:0<v:=by unfold v; exact_mod_cast L.property
 change (Real.sqrt v/v^2)^4=v⁻¹^6; rw [div_pow, ←pow_mul, show Real.sqrt v ^4=(Real.sqrt v ^2)^2 from by ring, Real.sq_sqrt h.le]; field_simp
lemma fisc (A:ℝ)(u:0≤A): ∃ D:ℝ, 1 ≤ D ∧ ∀ᶠ L:Side in atTop, D*followV [] L ≤1 ∧∀ r1:ℝ,0≤r1→∀ᶠ h:ℝ in atTop, let Q:=Coin_ ((4:ℝ)^3*h) (population*(A*followV [] L)) (population*r1) 5 (5+90) (6+2); 0≤Q∧ Q ≤ D*followV [] L*h := by
 let E:=Real.exp (5*(Yaw.χ 95:ℝ)); let t:= population; let z:= lip 8
 let d:= E*2*(z*4^3*t*A)+1
 have hz:0 ≤ z:= richP _; have hp:0 < E:=by unfold E; positivity
 have ht:0 ≤ t:=by unfold t population; positivity
 have hd:1 ≤ d:=by unfold d; exact le_add_of_nonneg_left (by positivity)
 have hv:= (show Tendsto αN atTop (𝓝 0) from SlowP.spinReal.inv_tendsto_atTop).pow 6 |>.const_mul (d^4)
 refine ⟨d,hd,(hv.eventually (ge_mem_nhds (by simp : d^4*(0:ℝ)^6<1))).mono (fun L h=> ?_)⟩
 let Q:= followV [] L; have hu:0<Q:=Vpos ..
 refine ⟨le_of_pow_le_pow_left₀ (by decide : (4:ℕ)≠0) zero_le_one ?_,?_⟩; · rw [mul_pow,followC,one_pow]; exact h
 intro r' u'; let q:=1+4*(E*z*(t*r')+1); filter_upwards [eventually_ge_atTop (q/Q),eventually_ge_atTop (0:ℝ)] with h i v
 dsimp only; have he: Coin_ _ _ _ _ _ _= q+(E*2*(z*4^3*t*A))*Q*h:=show Coin_ ((4:ℝ)^3*h) (t*(A*followV [] L)) (t*r') 5 (5+90) (6+2)=_ from by unfold Coin_; change 1+(E* (2*(z*((4^3*h)*(t*(A*Q)))))+4*(_+1))=_; unfold E q z; ring
 rw [he]; change 0≤ _ ∧ _≤ d*Q*h; have hq:0 ≤ q:=by unfold q; positivity
 refine ⟨add_nonneg hq (by positivity),?_⟩; unfold d; rw [add_mul,one_mul,add_mul,add_comm q]; rw [mul_comm Q h]; exact add_le_add_right ((div_le_iff₀ hu).mp i) _
abbrev RopeTune(R:Side)(A r0 r1 h γ:ℝ) (x:ℝ): Prop := |Xot h h 5 (A*followV [] R) r0 r1 5 6 (radiusB x) 3| ≤ γ ∧5*2*(Yaw.χ (5+90):ℝ) ≤ (radiusB x:ℝ)*(r0/2)
lemma rope_early (L:Side)(A r0 r1 γ:ℝ)(v:0<r0)(hb:0<γ):∀ᶠ h:ℝ in atTop,∀ᶠ x:ℝ in atTop,RopeTune L A r0 r1 h γ x:=by
 let t:= Real.exp (5*Yaw.χ (5+90))*(lip (6+2)*(population*r1)); let Z:=lorp 5 (5+90) 3 (population*(A*followV [] L)); let f(h:ℝ):= t/h^2
 have he:Tendsto f atTop (𝓝 (0:ℝ)):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega:(2:ℕ)≠0))
 filter_upwards [eventually_gt_atTop (0:ℝ),he.abs.eventually (gt_mem_nhds (show |(0:ℝ)|<γ from (by rw [abs_zero]; exact hb)))] with h u p
 let B(x:ℝ):= (radiusB x:ℝ); let y(x):= Real.exp (-(r0/2)*B x)*Z*(h^2*lip (6+2)^2)
 have hh:Tendsto B atTop atTop:=tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
 have hx:Tendsto (fun x:ℝ=>t+y x) atTop (𝓝 t):=by
    have hv:= (Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg (show -(r0/2)<0 from by linarith) hh)).mul_const Z |>.mul_const (h^2*lip (6+2)^2); simpa only [Function.comp_apply, zero_mul,add_zero,y] using (tendsto_const_nhds (x:=t)).add hv
 have hb:= hh.atTop_mul_const (half_pos v) -- tune
 exact (((hx.div_const (h^2)).abs.eventually (ge_mem_nhds p)).and (hb.eventually_ge_atTop _))
abbrev LotPre (W:ℝ)(ζ:SkyC 6 W)(t s:ℝ):= Bask₁ W 5 3 6 (1/4) ζ t s 5
private abbrev tFac(R:Side)(n:ℕ):= Real.exp (-(1/4)*(n:ℝ))*(R.val:ℝ)^6
lemma oldLot:∃ D:ℝ,0 < D ∧∀ n:ℕ,∀ L:Side, L.val ≤ n^3→ Real.exp (-(1/4)*(n:ℝ)) ≤ D*αN L^6 :=by
 let v(n:ℕ):=(n:ℝ)^18*Real.exp (-(1/4)*n); have hp(n:ℕ):0 ≤ v n:=by unfold v; positivity
 have he: Summable v:= Real.summable_pow_mul_exp_neg_nat_mul 18 (r:=1/4) (by norm_num)
 let D:=∑' i,v i; have hd:0 ≤ D:= tsum_nonneg hp
 refine ⟨D+1,by positivity,fun n L p=>?_⟩
 have hr: tFac L n ≤ v n:=by
    unfold v tFac; rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; refine (pow_le_pow_left₀ (Nat.cast_nonneg _) (show (L.val:ℝ) ≤ n ^ (3:ℕ) from ?_) 6).trans_eq ?_
    · exact_mod_cast p
    ring
 have hh:0 < (L.val:ℝ):=by exact_mod_cast L.property
 unfold αN; rw [inv_pow,←div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos hh _)).mpr; exact hr.trans ((Summable.le_tsum he n (fun i _=>hp i)).trans (le_add_of_nonneg_right zero_le_one))
-- expense at D and S, include assumptions c scaled additive $Lx1$. For Mayor ($1/4$). We price with |PE| to avoid knot.
structure LotLeaf (L:Side)(W:ℝ)(X:SkyC 6 W)(M a D γ C:ℝ): Prop where
 worn (n:ℕ)(b:ℝ)(hb:0≤b)(u:L.val≤n^3): Wot 6 5 3 n M a W X 5 (1/4) γ b ≤ C*αN L^6*b
 terse (n:ℕ)(b:ℝ)(hb:0≤b): Vot 6 5 3 n M a W X 5 (1/4) γ b (D*followV [] L)+ αN L^6 * (Real.exp (-(1/4)*(n:ℝ))*LotPre W X M a*b)≤ C*αN L^6*b
lemma lotFund (W:ℝ)(X:SkyC 6 W) (M a D:ℝ):∃ C:ℝ,1 ≤ C ∧∀ (L: Side)(f:ℝ→ℝ), Tendsto f atTop (𝓝 0) →∀ᶠ x in atTop, LotLeaf L W X M a D (f x) C:=by
 obtain ⟨B,v,g⟩:=oldLot; let P:=LotPre W X M a; let C:= |P|
 have hc:0 ≤ C:= abs_nonneg _
 let U:=max (B*C*(1+1)) (C*(D^4+1)+C)+1; have hp:1 ≤ U:=le_add_of_nonneg_left ((show 0 ≤ B*C*(1+1) from by positivity).trans (le_max_left ..))
 refine ⟨U,hp,fun L f v=>?_⟩; let m:=αN L; have hx:0< m:=α_pos _; have ht:m^6 ≤1:=pow_le_one₀ hx.le (αsmall L)
 have hy:= v.const_mul P; have hT:= (((Real.continuous_exp.tendsto _).comp hy).mul hy).abs
 filter_upwards [hT.eventually (ge_mem_nhds (show |Real.exp (P*0)*(P*0)|< m^6 from (by rw [mul_zero,mul_zero,abs_zero]; positivity)))] with x u
 let R:= Real.exp (P*f x)*(P*f x); have hr:|R|≤ m^6:=u
 have ht(z y d:ℝ)(hz:|y|≤d):P*y ≤ C*d:=by -- z unused
    apply le_trans _ (mul_le_mul_of_nonneg_left hz (abs_nonneg P)); exact le_trans (le_abs_self _) (abs_mul P y).le
 constructor
 · intro n b hv q; let e:=Real.exp (-(1/4)*(n:ℝ)); have he:e≤ B*m^6:=g n L q; change e*(P*(1+R))*b≤ _
   refine mul_le_mul_of_nonneg_right (le_trans ?_ (mul_le_mul_of_nonneg_right (show B*C*(1+1)≤ U from (le_max_left ..).trans (le_add_of_nonneg_right zero_le_one)) (pow_nonneg hx.le 6))) hv -- ht shadow
   calc
   _ ≤ B*m^6 * (C*(1+1)) := ((mul_le_mul_of_nonneg_left (ht 0 _ _ ((abs_add_le ..).trans (add_le_add (le_of_eq abs_one) (hr.trans (pow_le_one₀ hx.le (αsmall L)))))) (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right he (by positivity)))
   _ = _:= by ring
 intro n b p; let z:=Real.exp (-(1/4)*(n:ℝ)); have ht':z ≤ 1:= Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
 unfold Vot; dsimp only; rw [mul_pow, followC]
 change z*(P*(D^4*m^6+R))*b+m^6*(z*P*b)≤ _
 have hb₁: z * P ≤ C:= (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le).trans (mul_le_of_le_one_left hc ht')
 have he: z*(P*(D^4*m^6+R)) ≤ C*(D^4+1)*m^6:=by
    have hz:|D^4*m^6+R|≤ D^4*m^6+m^6 := (abs_add_le ..).trans (add_le_add (le_of_eq (abs_of_nonneg (by positivity))) hr); exact ((mul_le_mul_of_nonneg_left (ht 0 _ _ hz) (Real.exp_pos _).le).trans (mul_le_of_le_one_left (by positivity) ht')).trans_eq (by ring)
 apply (add_le_add (mul_le_mul_of_nonneg_right he p) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb₁ p) (pow_nonneg hx.le 6))).trans; refine le_trans (le_of_eq (show C*(D^4+1)*m^6*b +m^6*(C*b)=(C*(D^4+1)+C)*m^6*b from by ring)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_add_of_nonneg_right zero_le_one)) (pow_nonneg hx.le 6)) p)
end BellPrice
end YM.CF.Oath
end
