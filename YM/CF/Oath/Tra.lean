import YM.CF.Oath.Rays
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
-- Exact resolve PH.Wick all shares.SupportX both senses. 
open PhysicalNext.JointLoad Heir Siete
variable {a:ℝ}
lemma aur (p:1 ≤ a) (R:Side) (k:ℕ) (b:ℝ→ℕ)(hp:sizeK R 0 (fun x=>(b x:ℝ))) : sizeK R 0 (fun x:ℝ=> a^(Nat.clog 2 (b x)+k)) :=by
 obtain ⟨z,g⟩:=exists_nat_pow_near (x:=a) p (by norm_num:(1:ℝ)<2); -- tune
 let Z(x:ℝ):= (b x:ℝ); let V(x:ℝ):= 2*Z x+1; have hx:sizeK R 0 (fun x=> a^k* (V x)^(z+1)):= (((hp.scale 2).accrue (sizeK.mild R 1)).powC _).scale _
 apply hx.cost_d; filter_upwards with x; have h':0≤a:=zero_le_one.trans p; have he:0 ≤ V x:=add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) zero_le_one
 let d:=b x; let y:= Nat.clog 2 (b x); have hu:(2:ℕ)^y ≤ 2*d+1:=by
    by_cases h:1<d
    · have hh:0<y:=Nat.clog_pos (by decide:1<2) h
      generalize he : y=u; cases u; · omega
      have hp:= Nat.pow_lt_of_lt_clog (show _ < y from (by rw [he]; exact Nat.lt_succ_self _)); rw [pow_succ]; -- goal
      omega
    rw [show y=0 from Nat.clog_of_right_le_one (le_of_not_gt h) 2]; omega
 rw [abs_of_nonneg (pow_nonneg h' _), abs_of_nonneg (by positivity :0 ≤ a^k * V x^(z+1)),pow_add,mul_comm]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg h' k); refine le_trans (pow_le_pow_left₀ h' g.2.le y) ?_; rw [←pow_mul,Nat.mul_comm, pow_mul]; refine pow_le_pow_left₀ (by positivity) (show (2:ℝ)^y≤ V x from ?_) _
 unfold V Z; exact_mod_cast hu
abbrev cirQ(x:ℝ):ℕ:= 9*(1+radiusB x)
abbrev lacQ(x:ℝ):= Nat.clog 2 (8*cirQ x)
-- buy path. scale clash $K order.Weak.H.Length Infinity Chart.T period. 
def TubeP (j kR:ℕ)(Q a t x:ℝ):Prop:=∀ {N B:Side} (U':Pane (Scree.mid N B))(P': BudgetPoint),P'.threshold=temp x →∀ E:Type,∀ [NormedAddCommGroup E][NormedSpace ℝ E] (L:E →L[ℝ] Directions SU.group (Domain N B)), ‖L‖ ≤ (stilK (radiusB x))^kR →∀ s t': Site (Domain N B),∀ o'':Site (Domain N B),separation o'' s ≤ cirQ x →separation o'' t' ≤ cirQ x → ∀ g':Seat (mid N B) → SU.E,Canvas P' o'' (Heir.reach x) U' g' j Q→ Allows j (fun y=> Haro.mater (travel (Lattice.gauge g' (Vmove x U' (L y))) s (shiftH s t'))-1) 0 a
variable {a v':ℝ}
open scoped Matrix.Norms.Frobenius in
lemma yShake {E H:Type}[NormedAddCommGroup E][NormedAddCommGroup H][NormedSpace ℝ E][NormedSpace ℝ H](F:E→L[ℝ] H)(V:H→SU.E)(u:Tender V 0 a k)(p:‖F‖ ≤ b)(h:1 ≤ b):Tender (V ∘ F) 0 (a*b^k) k:= Shake.dil F _ u p h
set_option maxHeartbeats 900000 in
lemma walksK (Q:ℝ)(hQ:0≤Q)(j kR:ℕ)(v':ℝ)(hp:0<v')(t:ℝ):∀ᶠ x:ℝ in atTop, TubeP j kR Q v' t x:=by
 -- uniform. evidence monies time.
 let P:Side:=⟨2,by omega⟩
 obtain ⟨D,m,hD,hm,H⟩:= moveC j; obtain ⟨L,hL,Z⟩:=lucent; obtain ⟨u,K,hu,hK,R',Ww,-⟩:= Rill.sailors j Chi.canonical (div_pos (first_pos SU.group) (by norm_num:(0:ℝ)<3)) (show 2*(firstRadius SU.group/3)<firstRadius SU.group from (by have h:=first_pos SU.group; linarith)); obtain ⟨s₀,C,p,p',g⟩:= brand_ask j
 let V(x:ℝ):=(stilK (radiusB x))^kR; let M(x:ℝ):ℝ:=↑(8*cirQ x); let R(x:ℝ):ℝ:=Q*temp x*(1+(Heir.reach x:ℝ))
 let T_:=(sizeK.tempo P); let K':= (sizeK.Bcash P); have hm':sizeK P 1 R:=by
    unfold R Heir.reach; push_cast; exact (T_.scale _).tint ((sizeK.mild P 1).accrue (((sizeK.mild P 1).accrue K').scale _))
 have hv:sizeK P 0 M:=by unfold M cirQ; push_cast; exact ((((sizeK.mild P _).accrue K').scale _).scale _)
 have he:= (hv.tint (hm'.scale L)).spine; have ht:= hm'.spine; let Kt(x):= (D*temp x)* V x^j; let W0(x):=Rill.Cash (lacQ x+5) (Kt x) K; have hz:sizeK P 1 W0:=by
    unfold W0 Rill.Cash; have hk:sizeK P 0 V:= (((K'.accrue (sizeK.mild P _)).scale _).powC kR); exact (aur hK P _ _ hv).tint ((T_.scale D).tint (hk.powC _))
 filter_upwards [T_.spine.eventually (ge_mem_nhds hm),eventually_gt_atTop (0:ℝ),ht.eventually (ge_mem_nhds zero_lt_one), he.eventually (ge_mem_nhds hp), hz.spine.eventually (ge_mem_nhds hu),hz.spine.eventually (ge_mem_nhds p),(hz.scale C).spine.eventually (ge_mem_nhds hp)] with x m v Ht Pv w z c N B U P' gT E _ _ L' vQ a b o hx hp A pK
 let W:= shiftH a b; let Ξ:= Vmove x U ∘ L'; have hf:W.length ≤8 *cirQ x:= (Font.short ..).trans (by have he :separation a b ≤ cirQ x+cirQ x:= (separation_triangle ..).trans (add_le_add ((separation_comm a o).trans_le hx) hp); omega)
 have hx':0<temp x:= Work.E09.temp_pos v; have hs:0 ≤ Kt x:=by unfold Kt V stilK; positivity
 have h:= Haro.matchL (v:=C) a W Ξ (0:E) Q L (lacQ x) j (Heir.reach x) K (8*cirQ x) A o P' (show Canvas P' o _ (Ξ 0) A _ Q from (by simp [Ξ,Vmove,pK])) hQ (hf.trans (Nat.le_pow_clog (by omega) _)) hf (show Haro.reelQ a W⊆ Lattice.halo (Heir.reach x) {o} from (by rw [show Heir.reach x= 5*cirQ x from (by unfold cirQ Heir.reach; omega)]; exact visit_p a b o _ hx hp)) (by rw [gT]; exact Ht) hL Z R' Ww hK hs w -- tune duplicate W
 have hy: max (C*W0 x) (M x*(L*R x)) ≤ v':=max_le c Pv

 exact (h (fun i _=> yShake L' _ (H U x hx' m i) vQ (one_le_pow₀ (by unfold stilK; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]))) (fun U p=>g 0 z U p true)).mono (by rw [gT]; exact hy)
end YM.CF.Oath
