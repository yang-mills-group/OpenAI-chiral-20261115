import YM.Primitives.HAAR_LOG_JETS.Guard
import YM.CF.Tarn.Wage
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
-- post-L
variable {T:Tube G S}{K:Teller G}{s y:ℝ}
open Stationary Push.Loops Hors
lemma crystal (a Θ:ℝ)(h:0<a)(ht:0 ≤ Θ) : ∀ᶠ x in atTop,∀ {L: Side},radiusB x≤ L.val→ (Fintype.card (Site L):ℝ)*Θ*Real.exp (-a*L.val)≤ temp x:=by
 let t:=a/2; have hp:0<t:=half_pos h
 let f(n:ℕ):ℝ:= (n:ℝ)^4*Real.exp (-t*n)
 have he:Tendsto f atTop (𝓝 0):=by
    let g(n:ℕ):ℝ:=t*n
    have hT:Tendsto g atTop atTop:= Tendsto.const_mul_atTop hp tendsto_natCast_atTop_atTop
    have hs:= ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hT).const_mul (t⁻¹^4)
    rw [mul_zero] at hs; apply hs.congr; intro n; unfold f Function.comp g; dsimp only; rw [mul_pow]; rw [neg_mul]; field_simp -- tune
 obtain ⟨N,hN⟩:= eventually_atTop.mp (he.eventually (ge_mem_nhds zero_lt_one)); filter_upwards [Newt.smallF (n:=1) hp Θ,Work.E01.radiusB_tendsto.eventually_ge_atTop N] with x hx hpX L ht'
 have hx': (Stores.till x:ℝ) ≤ (L.val:ℝ):=by exact_mod_cast ((show Stores.till x ≤ radiusB x from Nat.div_le_self ..).trans ht')
 apply le_trans ?_ (show _≤temp x from hx.trans (pow_one _).le); rw [show (Fintype.card (Site L):ℝ)=(L.val:ℝ)^4 from by norm_cast; simp [Site,Four,Per,Axis,ZMod.card]]
 have he:(L.val:ℝ)^4*Θ*Real.exp (-a*L.val) = f L.val * (Real.exp (-t*L.val)*Θ):=by unfold f; have hb:-a * L.val= (-t*L.val)+(-t*L.val):=by { unfold t; ring }; rw [hb,Real.exp_add]; ring
 rw [he]; refine (mul_le_of_le_one_left (by positivity) (hN _ (hpX.trans ht'))).trans (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonpos_left hx' (neg_nonpos.mpr hp.le))) ht)
lemma courtT(L:Side)(s B:ℝ)(p:0<s)(h:0≤ B):∀ᶠ x in atTop,B*tollE s (cart x L)≤ temp x:=by
 let v:=s/(4*L.val); have hp:0<v:= by unfold v; positivity
 filter_upwards [Newt.smallF (n:=1) hp B,Work.E01.radiusB_tendsto.eventually_ge_atTop (100000*L.val)] with x hx ht
 let Y:= cart x L
 apply le_trans ?_ (hx.trans (pow_one _).le); have hh : L.val ≤ Stores.till x:=by unfold Stores.till; omega
 have hQ: Stores.till x ≤ 2*L.val*Y:=by
    have hp:L.val ≤ L.val*Y:= le_mul_of_one_le_right (by positivity) (Nat.div_pos hh L.property); rw [mul_assoc]; have hx:Stores.till x % L.val + L.val* Y= Stores.till x:=Nat.mod_add_div ..; have hy : Stores.till x % L.val < L.val:= Nat.mod_lt (Stores.till x) L.property; omega
 rw [mul_comm B]; apply mul_le_mul_of_nonneg_right _ h; unfold tollE; apply Real.exp_monotone; unfold v; have he:(Stores.till x:ℝ) ≤2*(L.val:ℝ)*(Y:ℝ):=by exact_mod_cast hQ
 change _*(Y:ℝ)≤ _; field_simp; linarith
lemma nib_raise(L:Side)(b:ℕ)(G':Gauge): nib (fun i=>raised G' L (b*i)):=by
 -- 4
 unfold Hors.raised touchH; dsimp only; push_cast
 -- use plot directly
 let M(i:ℕ):=touchH (b*i) L; have hp:CapY M:=?_; convert (nib_const (Push.Uniform.townCost G') (by positivity)).mul (plot_n hp) using 1; ext1; unfold M touchH plot; push_cast; rfl
 unfold M touchH; exact (((CapY.lives.scal b).scal L.val).add (seedR L.val)) -- tune order
open RG Precision Pressure
variable{B:ℝ}
lemma proxS (n:ℕ)(T: Pressure.Tube G S)(P:Tab S)(q: Chi)(J:ChartRatio G)(l:ℕ)(t v d α u:ℝ)(h:FreshT T v u q J t α B n l P C m)(hv:2 ≤ n)(hp:0<u)(hx:∀ i, let f:=Souk.golden T P.1 P.2 J q d α v l; ContDiffAt ℝ (2:ℕ) f 0 ∧|Push.Uniform.entry f 0 (i:Fin 2→Push.Uniform.Primary c G)|≤ D): Prox (Coin T v u q J t d α l P) 2 D:=by
 let P':=Coin T v u q J t d α l P; let f:= Souk.golden T P.1 P.2 J q d α v l; let F(z):=f z-f 0; let L:= chair T P.1; let Q:= Complex.ofRealCLM
 have ht:satX (∑ i,P' i)=ᶠ[𝓝 0] Q∘ F ∘ L:=by
    let R:=u⁻¹ • L; filter_upwards [R.continuous.continuousAt.eventually (isOpen_ball.mem_nhds (show R 0∈ ball (0:Mast G c) 1 by simp))] with i hi; have ht:=h.pureT _ (mem_ball_zero_iff.mp hi) d
    dsimp only at ht; unfold satU at ht; rw [show u • R i=L i from smul_inv_smul₀ hp.ne' _,show facadeX G (L i)=_ from chap T P.1 i] at ht; change (∑ i,P' i) _ = _; rw [Finset.sum_apply]; exact ht
 intro i s; let w:=fun k=>(i k,s k); let z(j):= flaw G (i j) (s j); obtain ⟨hΔ,hS⟩:=hx w
 have hf: ContDiffAt ℝ (2:ℕ) F (L 0):= by rw [map_zero]; exact hΔ.sub contDiffAt_const
 have hz: (iteratedFDeriv ℝ 2 (satX (∑ i,P' i)) 0 z)= Q (Push.Uniform.entry f 0 w):=by
    rw [(ht.iteratedFDeriv ℝ 2).eq_of_nhds, Q.iteratedFDeriv_comp_left (hf.comp _ L.contDiff.contDiffAt) le_rfl, Push.Uniform.iter_lin_at (L:=L) hf,map_zero]; change Q ((iteratedFDeriv ℝ 2 F 0) (fun t=>L (z t))) = _; rw [show F=f-(fun _=>f 0) from rfl,iteratedFDeriv_sub_apply hΔ (show ContDiffAt ℝ (2:ℕ) _ _ from contDiffAt_const),iteratedFDeriv_const_of_ne (by decide:2≠0) ,Pi.zero_apply,sub_zero]; unfold L z; simp_rw [voice_y]; rfl -- tune
 rw [sumF (Coin T v u q J t d α l P) 2 _ (fun j=>(((h.bonds d j).1.ledger _ (by simpa using hp)).order hv).smooth)]; unfold cake; rw [_root_.smul_apply,hz,norm_smul]; refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ((Complex.norm_real _).trans_le hS); norm_num [Nat.factorial]
end YM.CF.Tarn
