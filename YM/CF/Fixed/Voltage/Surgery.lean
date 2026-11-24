import YM.CF.Fixed.Voltage.Curtain
/-!
BudgetPoint surgery: small tilt in β while preserving actual identity at each step. Readdress rank through chosen short correction with long refunds. Only at finite volumes; can require arbitrarily small slip.
-/
set_option autoImplicit false
set_option maxHeartbeats 720000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Fixed.Voltage
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
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup Collection
open Trees Salt Beau Push.BetaTransport Reef
variable{n:Side} {x Δ B₁ B₂ B₃ e C0 d k v w:ℝ}{L0:ℕ}
variable(P:BudgetPoint)(R:PathData SU.group){q:Clip}{σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(hp:Geo.Width P q σ)(ht:1 ≤ w)(r: Rare R)
local notation "M"=> More n
abbrev deltaF (P:BudgetPoint)(R:PathData SU.group)(q:Clip)(v:ℝ)(E:RegBudget n) : InkD n:= v • (moldV n ∘ kinetic R q P) - exponentL P E
variable (F E:RegBudget n)(K:ForceBudget n) (hκ:∀ D:Support (More n),Metered P D (oV (Taxi.moldV n ∘ kinetic R q P)) w B₁) (X:Lord P E k w L0)(Y: Dark Utrue K P w B₂)
abbrev payDelta(n:Side)(P:BudgetPoint)(b w k:ℝ):ℝ:=w*b+wholePrice P n*k -- here w≥abs(value)
abbrev sliceF (P:BudgetPoint)(R:PathData SU.group)(q:Clip)(v:ℝ)(F:RegBudget n): RegBudget n:=pipeline P (deltaF P R q v F)
abbrev totter(b:ℝ):= b*Real.exp 1
abbrev payTheta (P:BudgetPoint)(b k:ℝ)(n:Side):ℝ:= totter b * markPrice P n k
abbrev jetF (P:BudgetPoint)(R:PathData SU.group)(q:Clip)(v:ℝ)(E:RegBudget n)(K:ForceBudget n) (U:Orbit n):= (exp (deltaF P R q v E U.1)-1)*fueled P K U
abbrev tiltF (P:BudgetPoint)(R:PathData SU.group)(q:Clip)(v:ℝ)(E:RegBudget n)(K:ForceBudget n):ForceBudget n:= visorP P (jetF P R q v E K)
private lemma Tsim (U:Pane n)(δ:ℝ): δ * kinetic R q P U= R.inChannels q P (d+δ) U - R.inChannels q P d U:=by rw [channels_split U (d+δ),channels_split U d]; ring
local notation "C₁"=> payDelta n P B₁ e k
variable (D:Support (More n))
include hκ ht X
lemma measuredΔ (u:|Δ|≤e): Metered P D (oV (deltaF P R q Δ E)) w (payDelta n P B₁ e k):= by
 let H:Metered P D (oV (deltaF P R q Δ E)) w (|Δ| * B₁+wholePrice P n*k):= ((hκ D).stow Δ).diff (meter_hub P D E X.tax ht); unfold payDelta; exact H.mono (add_le_add_left (mul_le_mul_of_nonneg_right u ((hκ D).holds (zero_le_one.trans ht))) _)
omit hκ ht
include p r hp
lemma gain_p (x:ℝ):Vision (deltaF P R q x E):=by
 intro s W t V; let Φ:= tintY s W; have he:= exponent_review s t X.tax trivial V; unfold deltaF; simp only [Pi.sub_apply,Pi.smul_apply,Function.comp_apply, tune_E P R p hp r s _,he,map_sub,map_smul]; change x • ((kinetic R q P V) • 1)-_=x • (Φ ((kinetic R q P V) • 1))-_ ; rw [map_smul,map_one]
include Y
lemma vision_V (x:ℝ):Speed (jetF P R q x E K):=by
 intro s U t V v; let Y':= jetF P R q x E K; have hx: Continuous (tintY s U):=(tintY s U).toLinearMap.continuous_of_finiteDimensional; letI:NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ _
 unfold jetF; change (exp (deltaF _ _ _ _ E (flashA s V.1))-1)*_= _; rw [gain_p P R p hp r E X x s U t V.1, fueled_review s t Y trivial V v, map_mul,map_sub,map_one,map_exp _ hx] -- order
omit p r hp
include hκ ht
lemma money_V (g:|Δ|≤e)(u:payDelta n P B₁ e k ≤1): Metered P D (jetF P R q Δ E K) w (payTheta P (payDelta n P B₁ e k) B₂ n):=by
 let H:= measuredΔ P R ht E hκ X D g; have hx:= zero_le_one.trans ht; have hN:0≤ markPrice P n B₂:=flagp_pos (holder_scale P B₂ (spent_D _ _ Y ht)); have he:= (H.powered hx).cross (meter_fuel P D K Y ht) hx; apply (show Metered P D (jetF P R q Δ E K) w (Real.exp C₁*C₁* markPrice P n B₂) from he).mono; unfold payTheta; apply mul_le_mul_of_nonneg_right _ hN; rw [totter,mul_comm C₁]; exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr u) (H.holds hx)
omit hκ ht Y X
section cost
variable {ξ:ℂ}
private lemma exp_cost (C:ℝ)(V:Cipher n): exp (moldV n C+V)=Real.exp C • exp V:=by
 letI: NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ _
 rw [NormedSpace.exp_add, mon_v,← Iva.yeaH, ←Complex.ofReal_exp, ← mon_v]; change (Real.exp C • (1:Cipher n))* _ = _; rw [Algebra.smul_mul_assoc,one_mul]
open Haro
-- actual stove. Off-shell β step lit curves. We leave scalar already-monetized.
noncomputable def relabel (Q: GramM n)(F:RegBudget n)(K:ForceBudget n)(β:ℝ) : GramM n:= {Q with F:=F,K:=K,beta:=β}
lemma board_relabel (Q:GramM n)(V:Orbit n)(i:FleetS Q.p.threshold V.1)(F: RegBudget n)(δ:ℝ):let Y:=relabel Q (Q.F+F+sliceF Q.p Q.path Q.funds δ F) (Q.K+tiltF Q.p Q.path Q.funds δ F Q.K) (Q.beta+δ); Y.board V= (Real.exp (δ*kinetic Q.path Q.funds Q.p V.1)) • Q.board V:=by
 intro Y; let U:=V.1; let D:= flags Q.p.threshold U; let C:=δ*kinetic Q.path Q.funds Q.p U; let Z:= deltaF Q.p Q.path Q.funds δ F U; let S:=fleetT Q.p (deltaF Q.p Q.path Q.funds δ F) U
 let F_:=Q.K+tiltF Q.p Q.path Q.funds δ F Q.K; let K:=fueled Q.p Q.K V; let v:= exponentL Q.p Q.F U+exponentL Q.p Q.slip U; let V':=exponentL Q.p F U
 have hζ:V' + Z=moldV n C:=by
    unfold V' Z deltaF; rw [Pi.sub_apply,Pi.smul_apply]; change _+ (δ • moldV n (kinetic Q.path Q.funds Q.p U)-_)= _; rw [add_sub_cancel]; exact (map_smul (moldV n) _ _).symm
 letI : NormedAlgebra ℚ (Cipher n) := NormedAlgebra.restrictScalars ℚ ℝ _
 change exp (exponentL Q.p (Q.F+F+pipeline Q.p (deltaF Q.p Q.path Q.funds δ F)) V.1+exponentL Q.p Q.slip U)*fueled Q.p F_ V= Real.exp C • (exp v*K)
 rw [ripe_H Q.p V,ripe_H Q.p V, pipe_T]; change exp (exponentL Q.p Q.F U+V'+S+exponentL Q.p Q.slip U)*_=_
 rw [show exponentL Q.p Q.F U+V'+S+_ = (V'+S)+v from (by unfold V'; unfold v; abel)]
 by_cases h:flags Q.p.threshold U=∅
 · have he:U∈deck_F Q.p (∅:Support M):= ⟨i,h⟩; rw [show S=Z from Set.indicator_of_mem he _, hζ,exp_cost,fuel_one _ _ _ h, show K=1 from fuel_one _ _ _ h,mul_one,mul_one]
 have hb:=visor_take (R:=Q.K) Q.p D (jetF Q.p Q.path Q.funds δ F Q.K) (nonempty_iff_ne_empty.mpr h) V (show V.1∈deck_F Q.p D from ⟨i,rfl⟩); have hh:fueled Q.p F_ V=exp Z*K:=(sub_eq_iff_eq_add.mp hb).trans (show (exp Z-1)*K+K= _ from (by ring)); have hu:S=0:= Set.indicator_of_notMem (fun t:U ∈ deck_F Q.p (∅:Support M)=> h t.2) _
 rw [hu,add_zero,hh,← Algebra.smul_mul_assoc, ← exp_cost, ← hζ, show exp (V'+v)=_ from NormedSpace.exp_add, show exp (V'+Z+v) = _ from NormedSpace.exp_add, show exp (V'+Z)= _ from NormedSpace.exp_add]; ring -- tune
private lemma tank_scale (Q:Op (Single n))(V:Cipher n)(t:ℝ):tank Q (t • V)=(↑t:ℂ) • tank Q V :=by
 unfold tank; rw [smul_sum]; apply sum_congr rfl; intro i _; change (t • crumb V.val i) • _=_; rw [Complex.real_smul]; exact mul_smul ..
lemma reprT {m B J:Side}{o:Odd J.val}{j:ℕ}{V:Pricing j J o (Vault.Thread j)} (U:Grasp V B e) (A:Loom (mid m B))(Q:GramM (mid m B))(v:Orbit (mid m B))(i:FleetS Q.p.threshold v.1)(F:RegBudget (mid m B))(δ:ℝ):let Y:=relabel Q (Q.F+F+sliceF Q.p Q.path Q.funds δ F) (Q.K+tiltF Q.p Q.path Q.funds δ F Q.K) (Q.beta+δ); denZ Y U A v=denZ Q U A v:=by
 intro Y; let S:=δ*kinetic Q.path Q.funds Q.p v.1; let y:= Q.betaL A v; have he: Y.betaL A v + (S:ℂ)=y:=by
    unfold y GramM.betaL GramM.H0; dsimp only [Y,relabel]; rw [show S= _ from Tsim (d:=Q.beta) Q.p Q.path v.1 δ, Complex.ofReal_sub]; ring
 have hp:Y.board v= Real.exp S • Q.board v:= board_relabel Q v i F δ
 unfold denZ; rw [hp,tank_scale,act_smul, smul_smul, Complex.ofReal_exp,← Complex.exp_add, he]; rfl
#print axioms reprT
#print axioms money_V
end cost
end YM.CF.Fixed.Voltage
