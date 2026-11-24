import YM.SU5.Thin.RG.TroughMark
import YM.CF.Vp929.Grant.River

/-! # The strengthened RiverWide. Adapted from `River`. -/
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade

variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Nor
variable (U:Grasp V.U B d)(W:GivenX V U)(s0:ℕ)(I:Stake.Isle)(v_:SheepP V U W I A k p s0)(e_:LocalRatio L) (t':1 < I.fine)
variable (q q':Chi)(u w' a h kL:ℝ)(h_:0 < A)(hw:0<a)(wS:scope_v a l R)(j_:l+100 ≤ j)(hL:6 ≤ k)(pL:2 ≤ p)(l0:5 ≤ l)(l1:l ≤18)
variable (hu:0 < kL)(wv:2*kL < firstRadius SU.group)(hx:h<d)(p0':0<u)(pv:u≤h)(M₀:ℕ)
variable (D_:Corset d q' kL (k+2) p)(Dμ m0 mC C C' wτ:ℝ)(Xc:SkyC k C)(hM:1 ≤ m0)(ha:1 ≤ mC)(Xp₀:SuitP k C')(Wol:0 ≤ wτ){κ0:ℝ}(Jp:PactH d kL (Xp₀.C*(R.L.val:ℝ)⁻¹^2) κ0 q' (k+2) p D_)
local notation "Sκ"=> a+2+2
local notation "Lφ"=> (a/4)
local notation "Zr"=> keyS (a+2+2) A 1 Xp₀.C l p k
local notation "Pδ"=> thermV (Sκ) m0 mC (a/4) Dμ Zr 2 Xc p l

structure RiverMark (F:Pilot)(Z:Pluck R)(q:Chi)(E₀:Tun I Z F ((tollE a)*100000))(k₀ M₀ n:ℕ)(vS dS u H PΨ ρ kC:ℝ)(Sc:BudgetPoint) :Prop where
 block(f g f' δ:ℝ→ℝ):sizeK R.L 2 f → sizeK R.L 2 g → sizeK R.L 2 f' → sizeK R.L 1 δ→ ∀ τ:ℝ→ℝ, sizeK R.L 1 τ → ∀ ag Cg:ℝ,0<ag → 0<Cg → ∀ J0:ℕ,∃ J₁:ℕ,J0≤ J₁ ∧ ∃ F' S' H' Qh Fκ Xr P₁:ℝ→ℝ,sizeK R.L 1 F' ∧ warmK H' ∧sizeK R.L k₀ S' ∧ sizeK R.L 1 H' ∧ Litt R 2 Qh ∧ sizeK R.L 3 Fκ ∧ sizeK R.L 1 Xr ∧ sizeK R.L 1 P₁ ∧∃ Dκ:ℝ→ℝ, Litt R 2 Dκ ∧ ∃ Qht hℓ:ℝ, ∃ oμ:ℝ→ℝ, 0<hℓ ∧ sizeK R.L (k₀+1) oμ ∧ ∀ᶠ x:ℝ in atTop, Neon.TimΞ R.L k p l x hℓ (oμ x) Sc ∧ Stake.PondP V F x vS kL j l (k+2) ∧ 0< F' x∧degreePrice (radiusB x) (F' x) 1 ≤ 1/2∧∀ {N P:Side}(S:StepData (Domain N B) (Domain P B))(G:Ratio (Scree.mid N B) (Scree.mid P B))(T:Tube SU.group S)(A0:Scree.Loom (Scree.mid N B))(E:Scree.Loom (Scree.mid P B))(X:GramM (Scree.mid N B))(Y: GramM (Scree.mid P B)), Roof _ vS dS M₀ A0→ Roof _ vS dS M₀ E →(∀ F' U' V', JointB G (seine G F' q' kL U' (A0 V'), A0 V') dS) →∀ P0:Girt.BaseL U G Y A0 E q' kL,∀ {Z' γ:ℝ}, StatV V G T U W X Y Z' γ a x p k → n*radiusB x ≤ (Domain N B).val → ∃ (M:Sheep V U W G Y.J X.J (k+2) p A)(Hm:Muster G S x d T)(PP:∀ D:Lattice.Support (Domain P B), Lend P B d D) (t':ℝ)(ht:Vista U Y.J.M Y.J.P PP (k+2) M.q ((Fintype.card Play:ℝ)*t') M.lot M.tone), ρ=M.r0 ∧ M.height=Qht ∧ Sheet.isle M=I ∧ 1≤ t' ∧ ∃ Jz:ℕ,∀ (s:ℝ)(F0 F1:RegBudget (Scree.mid P B))(Q:ForceBudget (Scree.mid P B))(Wu:ℂ), let X':= Oise.color_b X (s+(Hm.ang+Hm.fee)) 0 0 0 0; let Uv:= Oise.color_b Y s F0 F1 Q Wu; Hm.ang=Z' ∧ Hm.fee=γ∧(StatV V G T U W X' Uv Z' γ a x p k → ∀ P_:Girt.BaseL U G Uv A0 E q' kL, StageP V (tint_z Hm s) Uv X' U ∧ ∃ τ':Fend V (tint_z Hm s) M Z F q Uv.p X'.p γ Z' j l (coming Z j l*radiusB x), SiteCost (j:=j) (l:=l) (X:=X') (Y:=Uv) V U W I q' a kL F Z q (tint_z Hm s) E₀ vS t' H ag Cg (τ x) (P₁ x) J₁ M PP ∧ (Arc_r Uv H (f x) (g x) (f' x) → Oise.LookZ V (Xm:=X') (Xu:=Uv) M τ' P_ PP ht Jz (F' x) ((tolQ X.p).supportExponent+1) ∧ Corona_Q (zv:=F' x) V F Z M (X:=X') (Y:=Uv) τ' P_ PP t' ht D_ H C' (δ x) Xp₀ Jp (H' x) (PΨ*gritY R.L.val) (S' x) (Xr x) (Qh x) (Fκ x) ∧ Clover (zv:=F' x) V F Z (X:=X') (Y:=Uv) M τ' P_ PP t' ht D_ H C' (δ x) Xp₀ Jp (PΨ*gritY R.L.val) (S' x) (Dκ x) ∧ Neon.Blush_X V F Z (X:=X') (Y:=Uv) M τ' P_ PP t' ht H kC hℓ (oμ x) (S' x)))
variable (F:Pilot)(Z:Pluck R)(E₀:Tun I Z F ((tollE a)*100000))(n₀:ℕ)(Hp:ℝ)(tH:1≤Hp)(Kz:ℕ)(Pav ρ:ℝ)
variable (kC:ℝ)(Sc:BudgetPoint)(pR: TroughMark (j:=j) (l:=l) (A:=A) V U W I q' a kL D_ C' Xp₀ Jp F Z q E₀ Kz M₀ n₀ u h kL Hp Pav ρ kC Sc)
include pR hx p0' pv tH
lemma riverMark : RiverMark (j:=j) (l:=l) (A:=A) V U W I q' a kL D_ C' Xp₀ Jp F Z q E₀ Kz M₀ n₀ u h kL Hp Pav ρ kC Sc:=by
 refine ⟨fun f g f' δ hf hg hf' hδ τ hr a_g Cg hag hcG J0=>?_⟩; obtain ⟨J₁,vZ,E0,S',V',P₁,v,hP,vG,w₁,Qht,hℓ,oμ,hvℓ,uV,Γ⟩:= pR.block f g f' δ hf hg hf' hδ τ hr a_g Cg hag hcG J0
 have hγ: warmK E0:=Γ.mono fun v t=> ⟨t.2.2.1,t.2.2.2.1⟩
 obtain ⟨H0,hh,hu,hv,w,P⟩:= grow_f R k p E0 V' v vG hγ
 refine ⟨J₁,vZ,E0,S',_,_,_,_,P₁,v,hh,hP,H0,w,P,hv,w₁,V',vG,Qht,hℓ,oμ,hvℓ,uV,?_⟩
 filter_upwards [Γ,hh,hu,(year SU.group R.L).eventually_gt_atTop 0,(sizeK.main R.L).spine.eventually (gt_mem_nhds zero_lt_one), Work.E01.radiusB_tendsto.eventually_ge_atTop (M₀+M₀)] with x Uv U₁ Xv pZ gV H'
 obtain ⟨T_,φ,o,γ,wQ⟩:=Uv; refine ⟨T_,fun x=>φ x,o,γ,?_⟩
 intro N' P' S G T A0 E X Y ht hp z P0 a₁ γ b t
 obtain ⟨M,Hm,P_,t',hR,uK,hWn,Uw,te,Jn,B₁⟩:= wQ S G T A0 E X Y ht hp z P0 b t
 refine ⟨M,Hm,P_,t',hR,uK,hWn,Uw,te,Jn,?_⟩; intro s F0 F1 K₀ v X' Vu; obtain ⟨tz,tΦ,h0⟩:=B₁ s F0 F1 K₀ v; refine ⟨tz,tΦ,?_⟩
 intro b P0; obtain ⟨hA,τ,hCp,C0⟩:=h0 b P0; refine ⟨hA,τ,hCp,fun uB=>?_⟩; obtain ⟨C0,D,Colour⟩:=C0 uB
 have he:1 ≤ rainX R 1 x:= rain_one _ _ pZ (le_of_lt gV); have hZ:rainX R 1 x≤ rainX R 2 x:=by have hG:=gauge G5 R.L pZ; unfold rainX; exact inv_anti₀ (by positivity) (pow_le_pow_of_le_one hG.le gV.le (by omega))
 exact ⟨C0, moan_C V F Z b M τ hA P0 M₀ M₀ ht hp H' φ p0' pv hx P_ t' hR D_ Hp C' _ Xp₀ Jp tH he hZ _ _ D Xv U₁.1 U₁.2,D, Colour⟩
omit pR hx p0' pv tH
lemma RiverMark.forget (u': RiverMark (j:=j) (l:=l) (A:=A) V U W I q' a kL D_ C' Xp₀ Jp F Z q E₀ Kz M₀ n₀ u h kL Hp Pav ρ kC Sc) : RiverWide (j:=j) (l:=l) (A:=A) V U W I q' a kL D_ C' Xp₀ Jp F Z q E₀ Kz M₀ n₀ u h kL Hp Pav ρ:=by
 refine ⟨fun f g f' δ hf hg hf' hδ τ hr a_g Cg hag hcG J0=>?_⟩; obtain ⟨J₁,v,F',S',H',Qh,Fκ,Xr,P₁,h1,h2,h3,h4,h5,h6,h7,h8,Dκ,p,Qht,hℓ,oμ,t,p',E⟩:=u'.block f g f' δ hf hg hf' hδ τ hr a_g Cg hag hcG J0
 refine ⟨J₁,v,F',S',H',Qh,Fκ,Xr,P₁,h1,h2,h3,h4,h5,h6,h7,h8,Qht,?_⟩
 filter_upwards [E] with x Γ; obtain ⟨gt,Y,he,hf,Lq⟩:= Γ
 refine ⟨fun i=>Y i,he,hf,?_⟩; intro N' P' S G T A0 E X Y ht hp z P0 a₁ γ b t
 obtain ⟨M,Hm,P_,t',hR,uK,hWn,Uw,te,Jn,B₁⟩:= Lq S G T A0 E X Y ht hp z P0 b t
 refine ⟨M,Hm,P_,t',hR,uK,hWn,Uw,te,Jn,?_⟩; intro s F0 F1 K₀ v X' Vu; obtain ⟨tz,tΦ,h0⟩:=B₁ s F0 F1 K₀ v; refine ⟨tz,tΦ,?_⟩
 intro b P0; obtain ⟨hA,τ,hCp,C0⟩:=h0 b P0; exact ⟨hA,τ,hCp,fun uB=>⟨(C0 uB).1,(C0 uB).2.1⟩⟩
end YM.CF.Py
