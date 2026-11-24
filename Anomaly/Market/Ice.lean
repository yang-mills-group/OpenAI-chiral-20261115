import Anomaly.Market.Trim
import SatinThinVista
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








local notation "ξ" s:max => meterC (hat P.R.L P.x s)
open Regis Head.Garland -- paths tune ambiguity
open Lamour.Bridge
open Regis.Head.GeometryP Lamour.Bridge Celeste Clock Hookah Hookah.Blaze
open CF.Swell.Sonar
universe w
local notation "Ω" s:max i:max=> side Y i s
local notation "Xo" s:max=> Papal.xhood (P:=P) s
open Papal Cliplet
variable {I:Type} [Fintype I]
variable {m:ℕ}{z d:ℝ}(pK:4<d) (α T Γ':ℝ)(hα:0 < α)(ht:0 ≤ T)(hΓ:0 ≤ Γ')(hv:z+d*2*m<1) -- Π variable
local notation "xθ" s:max=> hat P.R.L P.x s
local notation "ℰ" s:max=> meterC (xθ s)
variable (H:Real.exp 1 ≤ P.x) (Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k → ShelterCost c Y s i k)
open Tower.SlabMark
variable {ri rk:ℕ→ℕ}(gi:Tendsto ri atTop atTop)(gk: ∀ s,∀ᶠ r in atTop,Ferry Y s (ri r) (rk r))(vk:IcePath Y ri rk)
private lemma icePay {ri:ℕ→ℕ}(g:Tendsto ri atTop atTop)(s:ℕ)(p q b:ℝ)(u:0<p)(v:0<q)(l:0<b): ∀ᶠ i:ℕ in atTop, let n:=side Y (ri i) s; let m:=(More n).val^4
                                        iceRate Y s (ri i)*p^m ≤ b*q^m:=by
 let z:= fun i=>(side Y (ri i) s).val; let A:=Real.log p; let B:=Real.log q; let C:=Real.log b; let U:=16* |A|+16* |B|+|C|
 have he(i:ℕ): Real.exp (A*i)=(p^(i:ℕ)):= by unfold A; rw [mul_comm,Real.exp_nat_mul, Real.exp_log u]
 have hh(i:ℕ): Real.exp (B*i)=(q^(i:ℕ)):= by unfold B; rw [mul_comm,Real.exp_nat_mul, Real.exp_log v]
 have h:= (count_grows Y s).comp g
 filter_upwards [(tendsto_natCast_atTop_atTop.comp (show Tendsto z atTop atTop from h)).eventually_ge_atTop U] with i hi n m
 rw [← he, ← hh]; unfold Tower.SlabMark.iceRate; apply le_trans ?_ ((Eq.le (by rw [←Real.exp_add] : Real.exp (Real.log b + (B*m))=Real.exp (Real.log b)*Real.exp (B*m)))|>.trans_eq (by rw [Real.exp_log l]))
 rw [←Real.exp_add]; apply Real.exp_monotone
 have h0: U ≤ (n.val:ℝ):=hi; have hv: (m:ℝ)=16*(n.val:ℝ)^4:=by unfold m; rw [show (More n).val=n.val*2 from rfl]; push_cast; ring
 have hn: - ((n.val:ℝ)^5) = - (n.val:ℝ)^5:=rfl -- Lean - x^5 precedence!
 change -((n.val:ℝ)^5)+ _ ≤ _ -- if parser.
 rw [hv]; unfold U at h0; have hq:1≤ (n.val:ℝ)^4:= one_le_pow₀ (Nat.one_le_cast.mpr n.property);
 nlinarith only [mul_le_mul_of_nonneg_right (neg_abs_le B) (show 0≤ (n.val:ℝ)^4 from by positivity), mul_le_mul_of_nonneg_right (le_abs_self A) (show 0≤ (n.val:ℝ)^4 from by positivity),mul_le_mul_of_nonneg_right h0 (show 0≤ (n.val:ℝ)^4 from by positivity), mul_le_mul_of_nonneg_left hq (abs_nonneg C),neg_abs_le C]
include H pK hα ht hΓ hv Z gi gk vk
lemma nightly (q':ℕ→ℂ)(pA:∀ (s:ℕ), ‖q' s‖ ≤ trailℓ z (xθ s)) (ε:ℕ→ℝ)(pE:∀ s, 0<ε s)(g:ℕ→ℕ)(g0:∀ᶠ s in atTop, 14* (ℰ s)* (4*((g s:ℝ)+(addgap (tent Y H):ℝ)))^4 ≤ ε s):
     ∀ᶠ s in atTop, ∀ᶠ r in atTop, let i:=ri r; let k:=rk r; ∀ (o:Tour I (More (side Y i s)))(V:Hookah (side Y i s)),∀ (FΩ HΩ:I→Pane (Ω s i)→ℂ)(oΩ:I→Site (More (Ω s i)))(DΩ:I→tableQ SU.group (More (Ω s i)) ℂ), KnotLaw Y s i k α T Γ' FΩ HΩ oΩ DΩ→∀ fp:ℂ→L[ℝ] ℝ, ‖fp‖ ≤ 1 → Propeller oΩ FΩ o fp (q' s) V → Fintype.card I=m → (∀ i,cows i (Lattice.halo 0 V.S) (g s)) → ‖Journey.compass Y i k s V.x‖≤ Real.exp (ΞDay d T Γ' (xθ s) (whisper Y s i k d o DΩ fp) (Fintype.card I) P.K.top.clip (q' s)+3* ε s):=by
 let K:= tent Y H; filter_upwards [g0,charter Y m pK α T Γ' hα ht hΓ hv Z,Z] with s ho hr hα'
 let B':=4*(g s+addgap K);  let Z':= ((2*lensD d (Xo s))^2*T)^Fintype.card I; let ψ:=-(|(q' s).re| * Z'); let M:=portraitS (q' s) (helmξ (xθ s)^Fintype.card I); have hp:0<ε s:=pE s
 have UT:=ht
 let U:=Real.exp (ε s); have ht:M≥1:=portraits_h (pow_nonneg (CF.BProof.coin_pos ..).le _) _; have hM:0<M:=zero_lt_one.trans_le ht; let E:= min 1 (Real.exp ψ); have hv:0<E:=lt_min one_pos (Real.exp_pos _); have he:1<U:=Real.one_lt_exp_iff.mpr hp; have hz:0<U-1:=sub_pos.mpr he
 filter_upwards [gi.eventually hr,gi.eventually hα',gk s,vk s,gi.eventually ((count_grows Y s).eventually_ge_atTop (g s+addgap K)), icePay Y gi s M E (U-1) hM hv hz] with j hf hα' X V hX hL i k o A' FΩ HΩ oΩ DΩ hPΩ fp ov D' h0 p'
 let N':=side Y i s; let D:= (More N').val ^ 4
 obtain ⟨EΩ,t',h₀,h₁,h₃,e⟩:= Hookah.Blaze.shuttle (revive Y H s i k X) (terrain Y H (Y.ir i) s).symm (show g s+addgap K≤ N'.val from hX) _ D' p'; let n:=EΩ.length; let x':= ΞDay d T Γ' (xθ s) (whisper Y s i k d o DΩ fp) (Fintype.card I) P.K.top.clip (q' s); let y:= Real.exp (x'+ε s); have hy:ψ ≤ x':=ExpoPositive T Γ' (show 0 ≤ T from UT) hΓ (Fintype.card I) _ _ _ _ (hα' k X.depth X.enters).load.clear.le (whisper_law Y T ov _ o DΩ (Exists.choose_spec hPΩ.2.2).2.bunker); have hy': E≤y:=min_le_right .. |>.trans (Real.exp_monotone (hy.trans (le_add_of_nonneg_right hp.le))); have y0:0<y:=Real.exp_pos _
 let F:= Journey.compass Y i k s;
 let F':= solder Y i k X.depth s; let W:= Hookah.buffet EΩ; have hF:‖F W‖≤ y^n:=by
    refine (hf k X.depth X.enters (q' s) (pA s) o h0 fp ov FΩ HΩ oΩ DΩ hPΩ EΩ t').trans ?_; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; have ht: sites N' ≤ (n:ℝ)*(B':ℝ)^4:=by unfold sites; exact_mod_cast h₃
    have he: 14 * (ℰ s)*sites N' ≤ ε s*n:=by
       refine (mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num) (BProof.coin_pos ..|>.le))).trans ((mul_le_mul_of_nonneg_left ho (Nat.cast_nonneg (α:=ℝ) n)).trans' (Eq.le ?_)|>.trans_eq (mul_comm ..)); unfold B'; push_cast; ring
    rw [←h0]; change 14* _*_ + (n:ℝ)*x'≤(n:ℝ)*(x'+ε s); linarith only [he]
 have ha(c:ℕ)(t:c≤D)(v:Mark N')(H:Envelope v)(u:∀ x,‖v x‖≤ M^D): ‖F v-F' v‖ ≤ (U-1)* y^c:= by
    apply le_trans ((V X.depth v (M^D) H u).trans hL); exact mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one hv.le (min_le_left ..) t).trans (pow_le_pow_left₀ hv.le hy' _)) hz.le
 change n≤D at h₁; change 1≤n at h₀
 have heP: ‖F W-F' W‖ ≤ (U-1)*y^n:= ha n h₁ _ t'.occupy.env (fun j=>by apply (taunt t' ov hPΩ.1 (CF.BProof.coin_pos ..).le j).trans; exact pow_le_pow_right₀ ht h₁); change ‖F' A'.x‖^n≤ ‖F' W‖ at e
 have hu : ‖F' A'.x‖≤ U*y:=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by unfold U; positivity) (by omega:n≠0)).1; rw [mul_pow]; refine (e.trans ((norm_sub_rev (F' W) (F W)) ▸ (norm_le_norm_sub_add (F' W) (F W)))).trans ?_
    refine (le_trans (add_le_add heP hF) ((show U ≤ U^n from by simpa only [pow_one] using (pow_le_pow_right₀ (a:=U) ‹1<U›.le h₀)) |> (fun g=> (mul_le_mul_of_nonneg_right g (pow_nonneg y0.le n)).trans' (le_of_eq (by ring)))))
 have hh: ‖F A'.x -F' A'.x‖≤ (U-1)*y:=by
    refine (ha 1 (Nat.le_trans h₀ h₁) _ D'.owner.env (fun j=> ?_)).trans_eq (by rw [pow_one]); have hx:= spinGuts D' ov hPΩ.1 j; apply hx.trans; change M≤ M^D; exact (by simpa only [pow_one] using (pow_le_pow_right₀ ht (Nat.le_trans h₀ h₁)))
 apply (norm_le_norm_sub_add (F A'.x) (F' A'.x)).trans ((add_le_add hh hu).trans ?_)
 change _≤ Real.exp (x'+3*ε s); rw [show x'+3*ε s= ε s+(ε s+(x'+ε s)) from (by ring),Real.exp_add (ε s) (ε s+_),Real.exp_add (ε s)]; change _ ≤ U*(U*y); nlinarith only [mul_nonneg (sq_nonneg (U-1)) y0.le]
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
