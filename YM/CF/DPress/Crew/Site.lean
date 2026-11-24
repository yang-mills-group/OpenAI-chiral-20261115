import YM.CF.DPress.Crew.Flux
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open LinQ Cad Mercer Room Push.AbsoluteSums Larch Ione Trees Py Wray Kay Glyph Nacre Docket Tutor
variable {N:Side}{P:BudgetPoint}{h W a b c t M L u e:ℝ}{T S:BeatL N}{D:Docket P}{q:ℕ}{F:Scree.Loom N}(A:BondL T S (body_Q 1) b c a e)(v:Room F P e u h q)
variable {K:ℝ}{X Y:Cusp N}(G:RegBudget N)(τ:Ids N) (j:ℕ)(m:Male)(χ:Finset (Scree.Hub N))
open Flight -- ASCII
namespace Resident
local notation "rΩ"=> Tutor.RadP P W h K
local notation "Ld"=> StackL
variable (H:Tutor P h W a b c)(p:pureB A 1) (w0:0<K)(tK:Ride P h a b c M D)(hK:Tutor.RadP P W h K≤M)(hk:D.Tr≤K/32) (uK:1≤j)(hc0:liveB χ)(hz:∀ i:Scree.Hub N,coverNumber P.B i.val.2≤1 → i∈χ) (Q: Resident D X q h)
open scoped NNReal
variable {C:Type}[TopologicalSpace C]
lemma local_time {E:Type*}[MetricSpace E] (g:C→ E)(f:C→ E→ E) (p:∀ x:C, f x (g x)=g x)(t:∀ x, ContractingWith Υc (f x))(u:∀ y, Continuous (fun x=> f x y)): Continuous g:=by
 apply continuous_iff_continuousAt.2; intro i; apply tendsto_iff_dist_tendsto_zero.2; let t'(x:C):= dist (g i) (f x (g i)) / (1-(Υc:ℝ)); apply squeeze_zero (fun _=> dist_nonneg) (show ∀ k:C, dist (g k) (g i) ≤ t' k from fun k=>(dist_comm (g k) (g i)).trans_le ((t k).dist_le_of_fixedPoint _ (show IsFixedPt (f k) (g k) from p k))); rw [← show t' i=0 by simp [t',p]]; exact ((continuous_const.dist (u (g i))).div_const _).continuousAt -- check dist_{goal}
variable [Nonempty C] (G₀:C→ RegBudget N)(Xv:C→Cusp N)(Qι:∀ i,Resident D (Xv i) q h)(g:∀ i,IncX Utrue (G₀ i) P h K)
local notation "Yκ" i:max=> imageS A v (G₀ i) τ j m χ H p w0 tK hK hk uK hc0 (Qι i) (g i)
local notation "σΩ" i:max=> starH A v (G₀ i) τ j m χ H p w0 tK hK hk uK hc0 (Qι i) (g i)
variable (p_c:PointK Xv)(K₁: Beau.LampF G₀)
private lemma ℓs : wΨ ≤ wu P-wΨ*2:=by unfold wu wΨ; linarith [P.exponent_pos]
include p_c K₁
open BondL
lemma render_X (Y:C→ΘS rΩ)(u:Continuous Y): Continuous (fun i=> (Yκ i) (Y i))∧ Beau.LampF (fun i=> DE A v (G₀ i) τ (Xv i) (Y i).val+v.L_Q A ((Yκ i) (Y i)).val) ∧∀ x:Aura N,∀ D⊆x.val,∀ V':Orbit N,Continuous (fun i=> EV A v (Xv i) (Y i).val x D V'):=by
 let hρ:= (H.bright w0).le; letI : Nonempty (ΘS rΩ):= Cad.nonzero hρ; let P':=Room.rho A hρ; choose I w xκ using fun i=>(Qι i).tickets H.boot; let t := fun i => D.earnB _ _ (H.allowance A v hρ hK tK) (w i); let t' := fun i=> D.sustain _ _ (t i); have hu (i):= imageX A v (G₀ i) τ j m χ H p w0 tK hK hk uK hc0 (Qι i) (g i) (Y i); 
 have hx(i:C)(y): BondL.uDa P' v.proof v.pos _ v.heil (Xv i) v.Hope v.hue v.tone v.r1 v.r2 v.r3' y (G₀ i) τ= _ := (supply A v _ τ H p w0 tK hK (Qι i) y)
 have hz (i:C):riseV ((Yκ i) (Y i))= zeus j m (heroP (StackL (BondL.uDa P' v.proof v.pos _ v.heil (Xv i) v.Hope v.hue v.tone v.r1 v.r2 v.r3' (Y i) (G₀ i) τ) χ)):=by rw [hx]; exact hu i
 obtain ⟨F,V⟩:= P'.tune_QX (k:=v.Hope) v.proof v.pos _ v.heil v.hue v.tone v.r1 v.r2 v.r3' ℓZ uΨ ℓP wΨ D.Sh D.z D.γ uΨ le_rfl D.zpos D.gpos D.qlimit D.stint Y Xv p_c I u xκ t t' (fun z=>D.ℓtime _ (w z)) ℓs G₀ K₁ χ j m τ uK _ hz; refine ⟨F,fun x p=>?_,fun x D g F=>?_⟩
 · simp_rw [hx, show ∀ i, BondL.lineH (p:=P) P' v.proof v.pos i= _ from (LP v hρ · A)] at V; exact V x p -- supply missing
 · have he(k:C):= Resident.loft (X:=Xv k) A v hρ (Y k); conv => enter [1, i]; rw [←he i]
   exact P'.key_z (k:=v.Hope) v.proof v.pos _ v.heil F x v.hue v.tone v.r1 v.r2 v.r3' ℓZ uΨ ℓP Y Xv p_c I u xκ t t' ℓs D g -- order x vs κ big shadow
lemma one_curve : Continuous (fun i=>σΩ i) ∧ Beau.LampF (fun i=> flatK A v (G₀ i) τ (Xv i) (σΩ i).val) ∧∀ x:Aura N,∀ D⊆x.val,∀ V':Orbit N,Continuous (fun i=> EV A v (Xv i) (σΩ i).val x D V'):=by
 let S'(i:C):=(σΩ i); let Y'(i:C):= Yκ i; have hx(i): (Yκ i) (S' i)=S' i:= βs ..; have he: Continuous S':= local_time S' Y' hx (fun i=> constrained ..) (fun i=> (render_X A v τ j m χ H p w0 tK hK hk uK hc0 G₀ Xv Qι g p_c K₁ (fun _=>i) continuous_const).1); have hk:=(render_X A v τ j m χ H p w0 tK hK hk uK hc0 G₀ Xv Qι g p_c K₁ S' he).2; simp_rw [hx] at hk; exact ⟨he,hk⟩
end Resident
end YM.CF.Sour.Heath
