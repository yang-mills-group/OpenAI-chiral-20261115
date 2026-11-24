import YM.CF.Wray.Grape
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
open Iva Eire Font
local notation "Nx"=> Domain N B
local notation "Fx"=> Domain P B
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ)
variable {U:Grasp V.U B d}{W:GivenX V U}{G:Ratio (mid N B) (mid P B)}{X: GramM (mid N B)}{Y: GramM (mid P B)}(M: Sheep V U W G Y.J X.J (k+2) n A)(P_:∀ X: Support (Domain P B),Lend P B d X)
local notation "T'"=> (l*radiusB x)
local notation "K'"=> Hos S T'
variable (D:Support (Domain N B))(i:Hos S (l*radiusB x)) (Y':Hos S (l*radiusB x)→Support (Domain P B)→ℝ)(Z':Hos S (l*radiusB x)→Sweep (mid P B))(T₁:Ids (mid P B))
variable (tB:Sheet.isle M=I) -- remove tail
local notation "Z₀"=> Yaw.χ
local notation "ζ"=> radiusB x
local notation "L_"=> L
open Trees
section
abbrev priced(H a:ℝ)(s k:ℕ)(z:ℝ):= Real.exp (a*Yaw.χ s)*Real.exp (I.band*z)*(Real.exp (a*Yaw.χ s)*Real.exp (I.tone*z))*(((k+1:ℝ)^2* Real.exp (I.hill*z))*Real.exp (I.lot*z*((Fintype.card Play:ℝ)*H)^2))
variable (w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*t) M.lot M.tone)
include tB w'
lemma keep_s(a:ℝ)(h:0 ≤ a) (s:ℕ)(p0: a*2*Yaw.χ s≤ radiusB x*I.band)(p2:a*2*Yaw.χ s≤ radiusB x*I.tone)(u:0<radiusB x)(v:0≤t)(η':Palette V (M_:=M) P_ T₁ Z' Y') : (∑ p:Support (Domain P B)×Support (Domain P B),Trees.currency (radiusB x) a (Jig (r:= (l*radiusB x)) S (s*radiusB x) (i,p)).val * Yaw.loadH (facesH (k+2) Z' Y' P_ (i,p)) t)≤ priced I t a s (k+2) ((danceL S i.val  (l*radiusB x)).card) :=by
 rw [←tB] at p0 p2 ⊢
 exact talc S P_ i (s*radiusB x) (Z' i) T₁ (M.light _ _ _) w' (Y' i) (η'.tune _) (η'.speed _) (fun j=>(η'.rope i j).pos) u h M.glow.le M.tempo.le le_rfl p0 p2 v
omit tB w'
lemma rent_v (p:0 ≤ I.band)(v:0 ≤ I.tone)(t:0 ≤ I.hill)(w:0 ≤ I.lot) (H TX:ℝ)(u y:ℝ)(g: u ≤ y)(k s:ℕ): priced I H TX s k u ≤ priced I H TX s k y:=by unfold priced; gcongr
-- exponent covers binder.All Hos anchors.Seeds.L stem aid purchase.W
abbrev areaL(P:Patch)(l:ℕ)(x:ℝ):ℕ:= 4*(2*P.L.val*(l*radiusB x+20)+1)^4
lemma booth_l (T a:ℝ)(p:0≤I.band)(h:0 ≤ I.tone)(v:0 ≤ I.hill)(u:0 ≤ I.lot):∀ᶠ x:ℝ in atTop,∀{N P B:Side} (S:StepData (Domain N B) (Domain P B)), S.patch=R→∀ i: Hos S (l*radiusB x), priced I T a j k (danceL S i.val (l*radiusB x)).card ≤Real.exp (eventB R F x*i.val.shares):=by
 let y:ℝ:= I.band+I.tone+I.hill+I.lot*((Fintype.card Play:ℝ)*T)^2; let X(x:ℝ):ℝ:=(areaL R l x); let q:ℝ:=(k+1:ℝ)^2*Real.exp (a*Yaw.χ j)^2; have hp:0≤q:= by unfold q; positivity
 have hf : BoreP (fun x=>y*X x):=by
    unfold X areaL; push_cast; exact (BoreP.still _).grip ((BoreP.still _).grip ((((BoreP.still _).grip (((BoreP.still _).grip BoreP.radius_c).join (BoreP.still _))).join (BoreP.still _)).self _))
 let U:= F.penalty/128; have hu:0<U:=div_pos F.earn (by norm_num)
 filter_upwards [loomH hf.lento_w U hu R.L, loomH (Lento.sun q) U hu R.L] with x hx hq N P B S p' i
 let f:= scaleM G5 R.L U x; have hn:0 ≤ f:= mul_nonneg hu.le (sq_nonneg _); let s:ℝ:=i.val.shares; have hc: 1 ≤ s:=by unfold s; exact_mod_cast (show 1 ≤ i.val.shares from vase_d S i.val ▸ card_pos.mpr i.property.1) -- tune nat. 
 have hh: y*X x ≤ f:= (le_abs_self _).trans (Real.exp_le_exp.mp ((le_abs_self _).trans hx)); have hp': q≤Real.exp f:= (le_abs_self _).trans hq
 have he: (danceL S i.val (l*radiusB x)).card ≤ areaL R l x*i.val.shares:=by rw [←p']; exact (floorX S i.val).trans (by unfold areaL; apply Eq.le; ring)
 have hy : ( (danceL S i.val (l*radiusB x)).card:ℝ) ≤ X x*s:=by unfold s X; exact_mod_cast he
 apply (rent_v I p h v u T a _ _ hy _ j).trans; have hg:priced I T a j k (X x*s)= q*Real.exp ((y*X x)*s):=by unfold priced q y; simp only [add_mul,mul_assoc,Real.exp_add]; ring_nf -- tune
 rw [hg]; apply (mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le).trans; rw [←Real.exp_add]; apply Real.exp_monotone; rw [show eventB R F x=2*f by unfold eventB f scaleM U; ring]; change _ ≤ 2*f*s; nlinarith only [mul_le_mul_of_nonneg_left hc hn,mul_le_mul_of_nonneg_right hh (zero_le_one.trans hc)]
end
-- combines Core anchored EACH T₁
lemma peakL (p: 0 ≤ I.band)(u:0 ≤ I.hill)(p2:0 ≤ I.lot)(h:0 ≤ I.tone)(hO:0 ≤ I.oath)(l s k j:ℕ)(v₀ H a:ℝ)(g:0 ≤ a)(x':0 ≤ H)(t_:0 ≤ v₀) :∀ᶠ x in atTop,∀{N P B:Side}{d:ℝ}(S:StepData (Domain N B) (Domain P B)),S.patch=R→∀{U:Grasp V.U B d}{W:GivenX V U}{G:Ratio (mid N B) (mid P B)}{X:GramM (mid N B)}{Y:GramM (mid P B)}{m:ℕ}{K:ℝ}(M:Sheep V U W G Y.J X.J (k+2) m K)(P_:∀ X: Support (Domain P B),Lend P B d X)(T₁:Ids (mid P B)),Sheet.isle M=I→Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*v₀) M.lot M.tone→a*2*Yaw.χ s ≤ radiusB x*I.band→a*2*Yaw.χ s≤radiusB x*I.tone→∀ Y' Z',Palette V (M_:=M) P_ (S:=S) (r:=l*radiusB x) T₁ Z' Y' →∀ (L:Hos S (l*radiusB x) → Site (Domain N B)), (∀ j,L j∈stem S j)→∀ o: Site (Domain N B),(∑ i:Kite S (l*radiusB x) with L i.1=o, loadH (facesH (k+2) Z' Y' P_ i) v₀*(Trees.currency (radiusB x) a (Jig S (s*radiusB x) i).val*joinV (stake H) (purpleP I (paidL I Q.K₁ Q.K₂ k x (F.hat R x)) i.1 k j Q.book x F Z)))≤ Real.exp (-eventB R F x/4):=by
 filter_upwards [booth_l (R:=R) F I (l:=l) (j:=s) (k:=k+2) v₀ a p h u p2,compass F I Z k j H x' Q hO,Work.E01.radiusB_tendsto.eventually_gt_atTop 0, seaT G5 R.L _ 0 (div_pos F.earn (by norm_num : 0<(64:ℝ))) le_rfl l] with x h1 h2 h3 h4 N P B d S v U W G X Y k' A M P_ T₁ e M' h0 hr Y' Z' P0 L pL o -- tune arguments
 let b:=radiusB x; let W':=eventB R F x; let X:= Support (Domain P B) ×Support (Domain P B); let K:= Hos S (l*b)
 have h':= budget_sum (h4 S (by rw [v]) o) (Finset.univ); apply le_trans _ h'; rw [sum_filter]; change (∑ i:K×X,_) ≤ _; rw [Fintype.sum_prod_type]; apply sum_le_sum; intro i _; by_cases hx:L i=o; swap; · simp only [if_neg hx,sum_const_zero]; exact (h4 S (by rw [v]) o).1 i
 simp only [if_pos hx,if_true]; -- tune
 let z:= i.val.shares; let f:= joinV (stake H) (purpleP I (paidL I Q.K₁ Q.K₂ k x (F.hat R x)) i k j Q.book x F Z); let F'(p:X):= loadH (facesH (k+2) Z' Y' P_ (i,p)) v₀; let Vc(p:X):= Trees.currency (radiusB x) a (Jig S (s*radiusB x) (i,p)).val
 have hv(x: X):0 ≤ F' x:= sum_nonneg (fun j _=>mul_nonneg (royalV V T₁ P_ M' Z' Y' P0 _ j) (pow_nonneg t_ _)); have hs := keep_s V I M P_ i Y' Z' T₁ e M' a g s h0 hr h3 t_ P0 -- tune
 have he := ((h2 S v _ i)); rw [if_pos (hx ▸ pL _),zero_mul,Real.exp_zero,mul_one]; change (∑ p:X, F' p*(Vc p*f))≤ Real.exp (-W'*z); simp_rw [mul_left_comm (F' _) (Vc _),←mul_assoc, ←sum_mul]; apply (mul_le_mul_of_nonneg_left he (show 0≤∑ p:X, Vc p * F' p from sum_nonneg fun i _=>mul_nonneg (Real.exp_pos _).le (hv i))).trans; apply (mul_le_mul_of_nonneg_right (hs.trans (h1 S v i)) (Real.exp_pos _).le).trans; rw [←Real.exp_add]; apply Real.exp_monotone; dsimp only [W',z]; ring_nf; first|exact le_rfl|done
end YM.CF.Wray
