import ForceSatin.Horizon
import ForceSatin.Wallet
import ForceSatin.Ramp
import ForceSatin.Falcon
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip

-- uniform scalar exponents charges
open _root_.YM.Next.Rank.Spindle
open Gentle.Solace Rail
open _root_.YM.Regis.Resonance Lull
open Fineness
namespace Moon
-- genuine Mark polynomial & cost. Keep support and masks explicit; period registration asserted separately
variable {N:Side}{cN:Side}{r:Lattice.Ratio cN (More N)} (T:Tiling cN N r)
variable (S:Support (More N)){H₁:Bed} {Z:PathData SU.group}  {q:Clip} {η CS W t x β y:ℝ}
variable (R:Rules SU.group)(B:Z.Bounds q η CS W) (P₁:Attached H₁ Z)(L:Side)
variable {v' τ:ℝ}(M0:Floor H₁ q (More N) τ v') (O:Bid.Sworn H₁ (More N) SU.group)
open ProbabilityTheory
open Lifted Afterglow Satin Cygnet Loaves Horizons InnerProductSpace
open _root_.YM.Regis.Head
-- unnormalized face covariance (W). preserve lim all displacements. convenience invoice Σ Mark.Deck
variable {S0 N':Side}
lemma sun_linear (y:ℝ)(i:LensGauge N): Sun B P₁ y i=y • Sun B P₁ 1 i:=by apply ext_inner_right ℝ; intro b; rw [real_inner_smul_left]; change inner ℝ (toCone _ _ _) b=y*inner ℝ (toCone _ _ _) b; rw [Solace.cone,Solace.cone]; change y * _ = y*(1*_); rw [one_mul]
lemma sun_rate (i:LensGauge N): ‖Sun B P₁ 1 i‖≤chordAllowance q 1:=by
 apply (cone_p ..).trans; refine ContinuousLinearMap.opNorm_le_bound _ (beam_low (M:=(1:ℝ)) zero_le_one) fun x=>?_; change |1*((Real.sqrt q.direct)⁻¹*x (i.1,false,i.2))|≤ _; rw [one_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt q.direct)⁻¹)]; unfold chordAllowance; rw [one_mul]; exact mul_le_mul_of_nonneg_left ((coordinate _ (mem_univ _) _).trans (norm_gains _)) (by positivity)
lemma global_w (G:Horizon)(N:Side)(B:Z.Bounds q η CS W)(P₁:Attached H₁ Z)(y:ℝ): axisSumC (Glass N G).lo _root_.id B P₁ y=priceW (fun i j=> y*y*(pairP (Sun B P₁ 1 ∘ DirN N) i j)) G.face:=by
 let K:= Sun B P₁ y ∘ DirN N; rw [show priceW (fun i j=> _) G.face= memo (G.face.map K) from Lull.shining _ _ _ (fun i j=> ?_) le_rfl]; · unfold axisSumC Horizons.Glass; rw [List.map_map]; rfl
 unfold K pairP; dsimp only [Function.comp_apply]; rw [sun_linear B P₁ y,sun_linear B P₁ y,real_inner_smul_left,real_inner_smul_right, mul_assoc]; -- tune
lemma wicked_unit (A:Horizon)(Q:Wave (Single N))(t:ℝ): wickedF (Glass N A) t B P₁ Q= (A.cabin.map (fun i=>Rail.cost 1 i.step)).prod * (↑(priceW (fun i j=> t*t*(pairP (Sun B P₁ 1 ∘ DirN N) i j)) A.face):ℂ) * alleyR (mateK N) Q (chartP N A.song):=by rw [wickedF,global_w]; unfold gust carG SatinForce.cadence Horizons.Glass; rw [List.map_map]; apply congrArg (fun x=> x* _*_); apply congrArg List.prod; apply List.map_congr_left; intro i _; exact ride_flat _
-- projections. Path Pick: strictly mon. any EB & reservation on spine. choice diagonal independent of lengths. yLimit.Rcal. 
structure Picker (u v:ℕ→ℕ) (W:ℕ→ HorizonLens→ HorizonLens→ℝ)(β:ℕ→ℝ) :Prop where
 mass(s) : Tendsto (fun i=> (gram Y s (u i) (v i)).beta) atTop (𝓝 (β s))
 cost(s p q) : Tendsto (fun i=>
    let t:=Y.uv (v i)-s; let N:=count Y s (u i); pairP (Sun (P.V.L.mood t) (P.V.L.tied t) 1 ∘ DirN N) p q) atTop (𝓝 (W s p q))
section
variable {per cut:ℕ→ℕ} {Hr:Real.exp 1≤ P.x} {I E}(u:Universal Y Hr per cut I E) {A D:ℕ→ℕ} {G}(p:Tower.Coherent Y Hr (i:=per) (k:=cut) (E:=E) G A D)
variable {v:ℕ→ℕ}(hp:Tendsto v atTop atTop)
local notation "U₀" => per ∘ A ∘ v
local notation "D₀" => cut ∘ D ∘ v
local notation "Rꜰ"=> P.R.L
include p u hp
lemma stripΘ :∃ (d:ℕ→ℕ) (Wp:ℕ→ HorizonLens→HorizonLens→ℝ) (β:ℕ→ℝ), StrictMono d ∧ Picker Y (U₀∘ d) (D₀ ∘ d) Wp β:=by
 let K:= HorizonLens; let X:=ℕ × Option (K × K); let J(i):=Y.uv (D₀ i); let f (s i:ℕ):=gram Y s (U₀ i) (D₀ i); let r(s i:ℕ): K→K→ℝ:= pairP (Sun (P.V.L.mood (J i-s)) (P.V.L.tied (J i-s)) 1 ∘ DirN (count Y s (U₀ i))); let b:= fun i:X=> |ℶ i.1| *2 + chordAllowance P.K.top.clip 1 ^ 2
 let W (s:X)(i:ℕ):ℝ:=s.2.elim ((f s.1 i).beta) (fun p=> r s.1 i p.1 p.2); let g(i:ℕ)(s:X):ℝ:= if s.1 ≤ J i then W s i else 0; let Z:= fun (i:X)=> closedBall (0:ℝ) (b i); let V:=Set.pi Set.univ Z
 have he(i:X):IsCompact (Z i):= isCompact_closedBall ..; have hZ: IsCompact V:= isCompact_univ_pi he; let m:=chordAllowance P.K.top.clip 1;
 letI:Countable X:=inferInstanceAs (Countable (ℕ × Option (HorizonLens × HorizonLens))) -- letI tune
 have hw(i:ℕ):g i∈ V:=by
    rintro ⟨s,_|e⟩ _ <;> (apply mem_closedBall_zero_iff.mpr; change ‖g i _‖ ≤ |ℶ s| *2+m^2; unfold g; split; rotate_left)
    all_goals first| (rw [norm_zero]; positivity)| (skip) -- order tune
    · change |(f s i).beta|≤_; have h:= (prices_plot Y s (U₀ i) (D₀ i) (by assumption)).2.2.2.1; change matchedX (ℶ s) _ at h; obtain ⟨h0,h1⟩:= h; rw [abs_le]; constructor <;> linarith [abs_nonneg (ℶ s),le_abs_self (ℶ s),sq_nonneg m]
    change |inner ℝ _ _| ≤_; refine (abs_real_inner_le_norm ..).trans ((mul_le_mul (sun_rate ..) (sun_rate ..) (norm_nonneg _) (beam_low zero_le_one)).trans ((by ring:m*m=m^2).le.trans (le_add_of_nonneg_left ?_))); positivity
 obtain ⟨w,t,d,hG,u'⟩:= hZ.isSeqCompact hw; have hv(k:X): Tendsto (W k ∘ d) atTop (𝓝 (w k)):= Tendsto.congr' ((show (fun i=> g (d i) k) =ᶠ[atTop] W k ∘ d from (((Y.uv_grows.comp (u.pick.grow_k.comp p.growsB)).tendsto_atTop.comp hp |>.comp hG.tendsto_atTop).eventually_ge_atTop k.1).mono (fun _ h=> if_pos (show _ from h)))) (tendsto_pi_nhds.1 u' k)
 exact ⟨d,fun n i j=>w (n,some (i,j)),fun n=> w (n,none),hG,fun i=>hv (i,none),fun i p q=>hv (i,some (p,q))⟩
namespace Picker
variable {W0 βm} (H:Picker Y (per ∘ A ∘ v) (cut ∘ D ∘ v) W0 βm)
variable (s:ℕ){y:ℝ}
include H
lemma range : matchedX (ℶ s) (βm s):= by
 let V:= Set.Icc ((ℶ s)/2) (2*(ℶ s)); let f(i):=(gram Y s (U₀ i) (D₀ i)).beta; change βm s∈V; refine isClosed_Icc.mem_of_tendsto (f:=f) (H.mass s) ?_; filter_upwards [hp.eventually (p.finance s)] with n h; exact (prices_plot Y _ _ _ h.enters).2.2.2.1
-- for positivity all s need hat bound? Pose.E lemma look
lemma permit (u':1 ≤ ℶ s): |Real.sqrt (βm s)| ≤ fabric (ℶ s):= by
 let x:=ℶ s; have ht:= range Y u p hp H s; let b:= βm s; have hb:b≥0:= ((show 0 ≤ x/2 from (by unfold x; linarith only [u']))|>.trans ht.1); rw [abs_of_nonneg (Real.sqrt_nonneg _)]; unfold fabric; have h:0 ≤ x:=zero_le_one.trans u'; change Real.sqrt b ≤ 2*Real.sqrt x; nlinarith only [Real.sq_sqrt (x:=x) h,hb,Real.sqrt_nonneg x, Real.sq_sqrt hb, ht.2]
noncomputable def colorWage(w: HorizonLens→ HorizonLens→ℝ)(βm y:ℝ)(f:Horizon):ℂ:= (f.cabin.map (fun i=> Rail.cost 1 i.step)).prod * (↑(Lull.priceW (fun i j=> let z:= y*coupling βm; z*z*w i j) f.face):ℂ) * Loaves.zTariff f.song
-- choose ANY confirming flat Sea on actual late spins. spares. 
lemma kings : ∃ z: (i:ℕ)→ Wave (Single (count Y s (U₀ i))),∀ᶠ i:ℕ in atTop,IsStarProjection (FlatPaneP 4 (gram Y s (U₀ i) (D₀ i)).J.M (count Y s (U₀ i))) ∧ Sea (FlatPaneP 4 (gram Y s (U₀ i) (D₀ i)).J.M (count Y s (U₀ i))) (z i):=by
 let U(i:ℕ):= U₀ i; let M(i:ℕ):= (gram Y s (U i) (D₀ i)).J.M; let P(i:ℕ):= FlatPaneP 4 (M i) (count Y s (U i)); let z(i:ℕ):= if h:IsStarProjection (P i) then Classical.choose (phoz h) else 0; refine ⟨z,?_⟩; filter_upwards [((u.pick.grow_i.tendsto_atTop.comp p.growsA.tendsto_atTop).comp hp).eventually ((count_la Y s).eventually (ownsHalo (by decide:1≤(4:ℕ))))] with i h; have he: IsStarProjection (P i):= spar_fit (M:=M i) (h (Vale.val_e ..)).1; refine ⟨he,?_⟩; change Sea (P i) (z i); rw [show z i= _ from dif_pos he]; exact Classical.choose_spec (phoz he)
lemma kalon (h:1 ≤ ℶ s)(ψ: (i:ℕ)→ Wave (Single (count Y s (U₀ i))))(w:∀ᶠ i:ℕ in atTop,IsStarProjection (FlatPaneP 4 (gram Y s (U₀ i) (D₀ i)).J.M (count Y s (U₀ i))) ∧ Sea (FlatPaneP 4 (gram Y s (U₀ i) (D₀ i)).J.M (count Y s (U₀ i))) (ψ i)) (f:Horizon) (y':ℕ→ℝ) (k:Tendsto y' atTop (𝓝 y)) : Tendsto (fun i=>
    let N:=count Y s (U₀ i); let a':=D₀ i; let t:=Y.uv a'-s; wickedF (Glass N f) (y' i * coupling (gram Y s (U₀ i) a').beta) (P.V.L.mood t) (P.V.L.tied t) (ψ i)) atTop (𝓝 (colorWage (W0 s) (βm s) y f)):=by
 let ℓ(i):=(gram Y s (U₀ i) (D₀ i)).beta; let f':=f; let Z(i):=y' i*coupling (ℓ i); let z:=y*coupling (βm s); let N(i):= count Y s (U₀ i);
 have ht:0<βm s:= (half_pos (zero_lt_one.trans_le h)).trans_le (range Y u p hp H s).1; have he:Tendsto Z atTop (𝓝 z):= k.mul ((H.mass s).sqrt.inv₀ (Real.sqrt_pos.mpr ht).ne')
 simp only; simp_rw [wicked_unit]; refine Tendsto.mul (Tendsto.mul tendsto_const_nhds (Complex.continuous_ofReal.continuousAt.tendsto.comp (Lull.tending _ atTop (fun n i j => Z n* Z n * (_) ) (fun i j=>(he.mul he).mul (H.cost s i j)) _ _))) ?_
 refine Metric.tendsto_nhds.mpr fun z h'=>?_ ; obtain ⟨n,f⟩:=trueMean f.song (z/2) (half_pos h'); filter_upwards [w, (((u.pick.grow_i.comp p.growsA).tendsto_atTop.comp hp).eventually ((count_grows Y s).eventually_ge_atTop n)), (((u.pick.grow_k.comp p.growsB).tendsto_atTop.comp hp)|>.eventually (tide_joint Y s n))] with i p0 v0 h1
 rw [dist_eq_norm]; exact (f _ _ v0 (h1 _) (Vale.val_e ..) p0.1 _ p0.2).trans_lt (half_lt_self h')
#print axioms stripΘ
#print axioms permit
#print axioms kalon
end Picker
end
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
