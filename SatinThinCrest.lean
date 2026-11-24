import SatinThinPageantry
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
/-! # Sparse projection resulting state & compass; holder price use ANY such solid mover at this height below purchase. -/
variable {z A c:ℝ}




open Regis Head.Garland Head.Etch Lamour.Bridge Celeste Clock Hookah Hookah.Blaze

open Papal -- needed addgap namespace
set_option linter.unusedVariables false
-- probes fare template incumbent
variable (z:PlaqAxes→ℝ) {I:Type}[Fintype I]
local notation "xθ" s:max=>hat P.R.L P.x s
local notation "ρ" s:max=>Real.sqrt (hat P.R.L P.x s)
local notation "N" s:max i:max=> (Journey.side Y i s)
local notation "ℰ" s:max=> meterC (xθ s)
abbrev MoteFee (P:Preparation)(v:ℝ)(m:ℕ)(A:ℝ)(q:ℂ)(x:ℝ)(z:PlaqAxes→ℝ):=CallLate P v m A q.re x z + plenitS q (Regis.Head.Garland.costZ z x ^ m)
variable {A B b:ℝ} (Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k → ShelterCost b Y s i k)
include Z
lemma mote {t:ℕ}(h:4 < A)(p:B + A * t < 1) : ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k → ∀ q:ℂ,‖q‖≤trailℓ B (xθ s)→ ∀ {I:Type}[Fintype I](o:Tour I (More (side Y i s)))(w:Fintype.card I=t) (L:List (Hookah (side Y i s))), Sown z o (ρ s) (temp (xθ s)) q 0 L → ‖Journey.compass Y i k s (Hookah.buffet L)‖ ≤ Real.exp (14* (ℰ s)* sites (N s i)+ L.length*MoteFee P (CallBook Y s i k z A o) t A q (xθ s) z):=by
 filter_upwards [sell.{0} Y z t A B h p,Z] with s v u; filter_upwards [u] with i u k hz hk q b I _ o w L χ
 let f:= RootBook Y i k s; let F:= f.p; let Z' := Y.meter.a s; obtain ⟨t',_,_⟩:=Papal.prices_plot Y s i k hk
 let a:= xθ s; have hu : F=Z':= t'; have hy: F.threshold=temp a:= hu ▸ (Y.meter.boot s).1
 have hb:= (Y.voyage i).paths k; have hY: Rue.IsleB SU.group F.threshold:=by rw [hu]; exact hb.paid.can.isle _
 let c:= u k hz hk; obtain ⟨W,b',hW,hO,hF,hφ⟩:= Sown.chart (A:=o) (L:=L) (z:=z) (τ:=q) (p:=0) (x:=Real.sqrt (xθ s)) F (by rw [hy]; exact χ) hY ((Y.voyage i).CapeT s)
 have hx:= marketPack Y s i k c hz χ.occupy.env (grandEnv (p:=F) z (ρ s) W) b' hF hφ (v _ _ hk q.re ((Complex.abs_re_le_norm q).trans b) _ _ c.load.ready c.load.willing _ W w hW hO); refine hx.trans_eq (?_); unfold MoteFee; congr 1; rw [w,Fintype.card_fin,hy]; unfold Regis.Head.Garland.costZ; unfold a; ring
omit Z
lemma call_bound {s i k:ℕ}(o:Tour I (More (side Y i s))) : |CallBook Y s i k z A o|≤ (padC z SU.group A (xθ s)).arc^Fintype.card I:= vision_limit ..
lemma exposure {s i k:ℕ}(o:Tour I (More (side Y i s)))(a:ℂ) : -(|a.re| * (padC z SU.group A (xθ s)).arc^Fintype.card I)≤ MoteFee P (CallBook Y s i k z A o) (Fintype.card I) A a (xθ s) z:=by
 let V:= a.re; let P':= CallBook Y s i k z A o; unfold MoteFee CallLate plenitS; have h0 := mul_le_mul_of_nonneg_left (call_bound (k:=k) (A:=A) Y z o) (abs_nonneg V); rw [←abs_mul V] at h0; have h1:0≤Regis.trend:= by unfold trend; positivity
 linarith only [(abs_le.mp h0).1, mul_nonneg (bank0 z gaugeRules A (Fintype.card I) (xθ s)) (abs_nonneg V),mul_nonneg (mul_nonneg h1 (sq_nonneg (sunstroke (Fintype.card I) P.K.top.clip 2 (padC z SU.group A (xθ s))))) (sq_nonneg V),mul_nonneg (sq_nonneg ‖a‖) (sq_nonneg (Regis.Head.Garland.costZ z (xθ s)^Fintype.card I))] -- tune
-- buying at all large s. `b' width s` also moving parameter. adapt paying.
include Z
open Cliplet
variable (H:Real.exp 1≤ P.x)
include H
lemma mote_paid {d:ℕ}(q':ℕ→ℂ)(pA:∀ (s:ℕ), ‖q' s‖ ≤ trailℓ B (xθ s)) (h:4<A)(p:B+A*d<1)(ε:ℕ→ℝ)(pE:∀ s, 0<ε s)(g:ℕ→ℕ)(g0:∀ᶠ s in atTop, 14* (ℰ s)* (4*((g s:ℝ)+(addgap (tent Y H):ℝ)))^4 ≤ ε s):
     ∀ᶠ s in atTop, ∀ᶠ i in atTop,∀ᶠ k in atTop,∀ (o:Tour I (More (side Y i s)))(V:Hookah (side Y i s)),Vote z o (ρ s) (temp (xθ s)) (q' s) V → Fintype.card I=d → (∀ i,cows i (Lattice.halo 0 V.S) (g s)) → ‖Journey.compass Y i k s V.x‖≤ Real.exp (MoteFee P (CallBook Y s i k z A o) (Fintype.card I) A (q' s) (xθ s) z+3* ε s):=by
 let K:= tent Y H; filter_upwards [g0,mote Y z Z h p] with s ho hr; filter_upwards [hr,(count_grows Y s).eventually_ge_atTop (g s+addgap K)] with i hf hX
 let N':=side Y i s; let B':=4*(g s+addgap K); let P':=Y.meter.a s; let Z':= (padC z SU.group A (xθ s)).arc^Fintype.card I; let ψ:=-(|(q' s).re| * Z'); let M:=portraitS (q' s) (Regis.Head.Garland.costZ z (xθ s)^Fintype.card I); have hp:0<ε s:=pE s
 let D:= (More N').val ^ 4; let U:=Real.exp (ε s); have ht:M≥1:=portraits_h (pow_nonneg (cost0 z _) _) _; have hM:0<M:=zero_lt_one.trans_le ht; let E:= min 1 (Real.exp ψ); have hv:0<E:=lt_min one_pos (Real.exp_pos _); let g':= ((U-1)* E^D)/M^D; have he:1<U:=Real.one_lt_exp_iff.mpr hp; have hz:0<U-1:=sub_pos.mpr he; have hg:0<g':=by unfold g'; positivity
 filter_upwards [ferry_later Y s i, thaw_plot Y g' hg s] with k X V o A' D' h0 p'
 obtain ⟨T,t',h₀,h₁,h₃,e⟩:= Hookah.Blaze.trifecta (revive Y H s i k X) (terrain Y H (Y.ir i) s).symm (show g s+addgap K≤ N'.val from hX) _ D' p'; let n:=T.length; let x':= MoteFee P (CallBook Y s i k z A o) (Fintype.card I) A (q' s) (xθ s) z; let y:= Real.exp (x'+ε s); have hy:ψ ≤ x':=exposure Y z o (q' s); have hy': E≤y:=min_le_right .. |>.trans (Real.exp_monotone (hy.trans (le_add_of_nonneg_right hp.le))); have y0:0<y:=Real.exp_pos _
 let F:= Journey.compass Y i k s;
 let F':= solder Y i k X.depth s; let W:= Hookah.buffet T; have hF:‖F W‖≤ y^n:=by
    refine (hf k X.depth X.enters (q' s) (pA s) o h0 T t').trans ?_; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; have ht: sites N' ≤ (n:ℝ)*(B':ℝ)^4:=by unfold sites; exact_mod_cast h₃
    have he: 14 * (ℰ s)*sites N' ≤ ε s*n:=by
       refine (mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num) (BProof.coin_pos ..|>.le))).trans ((mul_le_mul_of_nonneg_left ho (Nat.cast_nonneg (α:=ℝ) n)).trans' (Eq.le ?_)|>.trans_eq (mul_comm ..)); unfold B'; push_cast; ring
    rw [←h0]; change 14* _*_ + (n:ℝ)*x'≤(n:ℝ)*(x'+ε s); linarith only [he]
 have ha(c:ℕ)(t:c≤D)(v:Mark N')(H:Envelope v)(u:∀ x,‖v x‖≤ M^D): ‖F v-F' v‖ ≤ (U-1)* y^c:= by
    apply (V i X.depth v (M^D) H u).trans; unfold g'; rw [div_mul_cancel₀ _ (pow_pos hM _).ne']; exact mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one hv.le (min_le_left ..) t).trans (pow_le_pow_left₀ hv.le hy' _)) hz.le
 change n≤D at h₁; change 1≤n at h₀
 have hh':P'.threshold=temp (xθ s):= (Y.meter.boot _).1; have hP':Sown z o (ρ s) P'.threshold (q' s) 0 T:= hh'.symm ▸ t'
 have heP: ‖F W-F' W‖ ≤ (U-1)*y^n:= ha n h₁ _ t'.occupy.env (fun j=>by apply (hP'.rain P' j).trans; rw [hh']; exact pow_le_pow_right₀ ht h₁); change ‖F' A'.x‖^n≤ ‖F' W‖ at e
 have hu : ‖F' A'.x‖≤ U*y:=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by unfold U; positivity) (by omega:n≠0)).1; rw [mul_pow]; refine (e.trans ((norm_sub_rev (F' W) (F W)) ▸ (norm_le_norm_sub_add (F' W) (F W)))).trans ?_
    refine (le_trans (add_le_add heP hF) ((show U ≤ U^n from by simpa only [pow_one] using (pow_le_pow_right₀ (a:=U) ‹1<U›.le h₀)) |> (fun g=> (mul_le_mul_of_nonneg_right g (pow_nonneg y0.le n)).trans' (le_of_eq (by ring)))))
 have hh: ‖F A'.x -F' A'.x‖≤ (U-1)*y:=by
    refine (ha 1 (Nat.le_trans h₀ h₁) _ D'.owner.env (fun j=> ?_)).trans_eq (by rw [pow_one]); have hx := (show Vote z o (ρ s) P'.threshold (q' s) A' from hh'.symm ▸ D').early P' j; rw [hh'] at hx; apply hx.trans; change M≤ M^D; exact (by simpa only [pow_one] using (pow_le_pow_right₀ ht (Nat.le_trans h₀ h₁)))
 apply (norm_le_norm_sub_add (F A'.x) (F' A'.x)).trans ((add_le_add hh hu).trans ?_)
 change _≤ Real.exp (x'+3*ε s); rw [show x'+3*ε s= ε s+(ε s+(x'+ε s)) from (by ring),Real.exp_add (ε s) (ε s+_),Real.exp_add (ε s)]; change _ ≤ U*(U*y); nlinarith only [mul_nonneg (sq_nonneg (U-1)) y0.le]
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.mote_paid
