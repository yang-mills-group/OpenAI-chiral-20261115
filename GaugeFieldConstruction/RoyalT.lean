import GaugeFieldConstruction.Enmity
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 120000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
section
open Py.Riant
open CoeffArc
variable {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}{d kL x:ℝ}
 {r:ℕ}{X:GramM (mid N B)} {Y:GramM (mid P B)}
 (V:Grace K R L){U:Grasp V.U B d} {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} {q:Chi}
variable {J:Type}[LinearOrder J][Fintype J] (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ForceBudget (mid P B))(X_R: RegBudget (mid N B))(Kν:ForceBudget (mid N B)) (Lt:ℝ)(eW:ℂ)
-- Y(z), p.W
variable (σ:J→ Site (Domain P B))(F0:Key J→ Troupe S (r*radiusB x) (Words S)→ Aura (mid N B)→ Copy (mid N B)) (W:Vow.Cusp (mid N B)) -- tune qualification
 (W₀:Key J→ Cusp (mid N B))(Yb:Key J→ Vow.Pax (mid N B))(Xp:Op SU.Slot)
 {h v1 kF dP Z b:ℝ}(B_:BornW (X:=X) (Y:=Y) (G₀:=G₀) (G₁:=G₁) (U:=U) (G:=G) (q':=q) (kL:=kL) (x:=x) V h Xo Yo Zo σ X_R Kν Lt eW W W₀ F0 Yb Xp v1 kF dP Z)(Wκ:WakeS (X:=X) (Y:=Y) (G₀:=G₀) (G₁:=G₁) (U:=U) (G:=G) (q':=q) (kL:=kL) (x:=x) V h Xo Yo Zo σ X_R Kν Lt eW F0 Yb Xp v1 kF dP Z)
 {pC K₀ K₁ K₂:ℝ}
 (C:Call_H (Y:=Y) h Xo Yo Zo σ K₀ K₁ K₂) (u:Girt.BaseL U G Y G₀ G₁ q kL)
 (Tp:Ids (mid N B)) (A0:J→Oath.Zone (mid N B))
 (hw:∀ i:J,∀ x':Orbit (mid N B), Rue.FleetS X.p.threshold x'.1 → Oath.Intent X.p (A0 i) x'=coldE X.p (debit Yb i) x')
 (hx:∀ (j:J) (i:Scree.Hub (mid N B)),S.ratio.parent (σ j)∉ i.val.2→(A0 j).1 i=0)
 {k t:ℕ} (hk:∀ i:J,HasCopper (k+1) (S.ratio.parent (σ i)) X.p h (G_K A0 i) b)
 (hs:X.p.supportExponent=1)(hp:0≤b) (hv:lamp_B (cape_B X.p.B) X.p.B t (S.ratio.parent ∘ σ)) (ht:(k+1)*(4*X.p.B+2)+2*X.p.B≤X.p.B+cape_B X.p.B)(hz:t*b ≤ v1)
-- W notation Qualify.Increment Q linear. K includes Kν. 
abbrev N_P (Yb:Key J→ Vow.Pax (mid N B))(Tp:Ids (mid N B))(A:J→Oath.Zone (mid N B)):= FacetE Yb (G_P A) Tp
abbrev N_K (p:BudgetPoint)(W: Cusp (mid N B))(W₀:Key J→ Cusp (mid N B))(A:J→Oath.Zone (mid N B)):= fun i:Key J=>budgetR (roomV p (nixV (W₀ i)) (W₀ i) (W+Φstack (G_K A) i))
local notation "Λr"=> (S.ratio.parent ∘ σ)
local notation "F©"=> (N_P Yb Tp A0)
local notation "Hβ"=> (N_K X.p W W₀ A0)
local notation "Xr"=> Jade.spark_B X X_R Kν Lt eW
include hw hx hk hs hp hv ht hz B_ Wκ
structure RillK (σ:J→ Site (Domain P B))(D0: Key J→ RegBudget (mid N B))(V0: Key J→ ForceBudget (mid N B))(τ:J→ℂ) (F such:ℝ): Prop where
    root: D0 0=0 ∧ V0 0=Kν
    ax(x:Scree.Hub (mid N B)): Hush (S.ratio.parent∘σ) x.val.2 (fun z=>D0 z x) ∧∀ v:Pane (mid N B), River (fun z=>D0 z x v)
    force(i:Force (mid N B)):Hush (S.ratio.parent∘σ) i.val.1.val.2 (fun z=>V0 z i)∧∀ v:Orbit (mid N B),River fun z=> V0 z i v
    net(i:Key J)(p:i∈hill J): let Y':=color_b Y Y.beta (Xo i) (Yo i) (Zo i) Y.v; let t:=α_ξ τ i; let U':=Jade.spark_B X (X_R +D0 i) (V0 i) Lt (eW+t); SanB (V0 i) (giftK X.p such) X.p h (fun _=>F)∧∀ v:Orbit (mid N B),Rue.FleetS X.p.threshold v.1→ Scree.stove U G₀ Y' G₁ G S q kL Xp v=Scree.denZ U' U G₀ v
lemma RillK.stage :RillK (h:=h) (X:=X) (Y:=Y) (U:=U) (G₀:=G₀) (G₁:=G₁) (G:=G) (S:=S) (q:=q) (kL:=kL) (V:=V) Xo Yo Zo X_R Kν Lt eW Xp σ F© Hβ (G_s A0) kF (X.p.supportExponent+1/2):=by
 obtain ⟨K,P⟩:= HasCopper.sales X.p A0 Λr b hp hk hs hv ht
 obtain ⟨Kf,V0⟩:= FrameS X.p A0 Λr b hk
 obtain ⟨hX,hY,FQ,H⟩:= B_.born _ K (fun i t=>(P i t).1) (fun i t j=>((P i t).2 j).trans hz) Kf V0 (by unfold Φstack; simp) F© (α_ξ (G_s A0)) (presentations X.p Yb Tp A0 Wκ.spur hw)
 exact ⟨⟨punk Yb (G_P A0) Tp Wκ.crop Wκ.root,FQ⟩,fun i=>⟨FrameP Yb Tp A0 Λr Wκ.span Wκ.crop hx i,growth_P Yb (G_P A0) Tp Wκ.crop i⟩,fun i=>⟨hX _, hY _⟩,H⟩ -- tune
omit hx hw hk hs hp hv ht hz B_ Wκ
-- version (24); e^(-s)*Fine, BEFORE integral. Rather than assert going outside domain of s1 z. All polynomial. Ink_F works. Law_W
variable (s:J→ℂ)(C₁:J→ J→ℂ)(Q:Key J→ RegBudget (mid N B))(Z': Key J→ForceBudget (mid N B))
-- param order. check
variable (τ0:ℝ) (hxS: RillK (h:=h) (X:=X) (Y:=Y) (U:=U) (G₀:=G₀) (G₁:=G₁) (G:=G) (S:=S) (q:=q) (kL:=kL) (V:=V) Xo Yo Zo X_R Kν Lt eW Xp σ Q Z' s kF τ0)
local notation "Hq" z:max=> sum univ (fun i:J=> (z:Key J) i*s i)

local notation "Yq" z:max=> color_b Y Y.beta (Xo z) (Yo z) (Zo z) (Y.v+-α_ξ s z)
local notation "Yz" z:max=> color_b Y Y.beta (Xo z) (Yo z) (Zo z) Y.v
local notation "Xq" z:max=> color_b Xr (Xr).beta ((Xr).F+ Q z) (Xr).slip (Z' z) (Xr).v
local notation "Tκ" x:max y:max=> lynx K S G G₁ G₁ G₀ Y q kL Xp x y
variable (l:List J)(hl:Roots.ψS (S.ratio.parent ∘ σ) l) (v:Orbit (mid N B))(he:Rue.FleetS X.p.threshold v.1)
variable (hT:S.ratio=ratio G)(H:S.patch.Branches S.kernel SU.group)(hX:1 ≤ h)
include hxS he hl
lemma RillK.link : Storm_C Λr C₁ l (fun z=> Scree.stove U G₀ (Yq z) G₁ G S q kL Xp v) (fun z=> denZ (color_b Xr (Xr).beta ((Xr).F+WritV Λr (Bus1 Q Λr C₁) z) (Xr).slip (WritV Λr (Bus2 Z' Λr C₁) z) (Xr).v) U G₀ v) :=by
 let F(z):=denZ (Xq z) U G₀ v
 have hz:Set.EqOn (fun z:Key J=>stove U G₀ (Yq z) G₁ G S q kL Xp v) F (hill J):=by
    intro z h; let Yv:= hxS.net z h; let u:=-α_ξ s z; have hf:= vision_U (S:=S) (kL:=kL) (G₁:=G₁) (G₀:=G₀) (U:=U) (G:=G) (Y:=Y) (q:=q) V Xo Yo Zo (fun _=>Y.v) v Xp z u; change _ = Complex.exp u • stove U G₀ (Yz z) G₁ G S q kL Xp v at hf; refine hf.trans (Eq.trans (congrArg (Complex.exp u • ·) (Yv.2 v he)) ?_)
    have he':= (vig_v (X:=Xr) (U:=U) (G₀:=G₀) V v ((Xr).F+Q z) (Xr).slip (Z' z) (eW+α_ξ s z) u); rw [show eW+α_ξ s z+u=eW from add_neg_cancel_right ..] at he'; exact he'.symm -- defeq spark?
 have ht:Storm_C Λr C₁ l F (fun z=>denZ (color_b Xr (Xr).beta ((Xr).F+WritV Λr (Bus1 Q Λr C₁) z) (Xr).slip (WritV Λr (Bus2 Z' Λr C₁) z) (Xr).v) U G₀ v):=by
    apply (pulse_H V Λr C₁ l hl Xr G₀ (fun z=>(Xr).F+Q z) (fun z=>(Xr).F+WritV Λr (Bus1 Q Λr C₁) z) (fun _=> (Xr).slip) (fun _=>(Xr).slip) Z' _ (fun _=>(Xr).v) (fun _=>(Xr).v) v ?_ (fun x y=>σtag_l ..) ?_ (σtag_l ..)).2.2
    · intro x y; have ht': (fun z=> (WritV Λr (Bus1 Q Λr C₁) z) x y) =Fluid Λr (streamArc (fun z=>Q z x y) Λr C₁):=funext fun i=> bus_P ..
      have he: Law_C Λr C₁ l (fun z=> Q z x y) (fun z=> WritV Λr (Bus1 Q Λr C₁) z x y):= ht'.symm ▸ stream_C _ _ _ ((hxS.ax x).2 y) hl
      obtain ⟨A,B,h⟩:=he; exact ⟨dub_V (zeroR _) A,dub_V (zeroR _) B,Aζ _ _ (zeroR _) A (zeroR _) B (constant_C _ _ _) h⟩
    intro i u; have he: (fun z=> WritV Λr (Bus2 Z' Λr C₁) z i u)=Fluid Λr (streamArc (fun z=>Z' z i u) Λr C₁):=funext fun x=>bus_K ..
    exact he.symm ▸ stream_C _ _ _ ((hxS.force i).2 u) hl
 intro i p; exact (ht i p).trans (rer _ _ _ fun _ _=>lace_C _ hz.symm roots)
include hX hT H u C
lemma RillK.pass : let Y0(y):= fun z:Key J=> denZ (Yq z) U G₁ y; let γ(t:List J)(y):= (Tκ v y) (tipI (Y0 y) t); (∀ i:List J, Integrable (γ i) (city _)) ∧ tipI (fun z=>denZ (color_b Xr (Xr).beta ((Xr).F+WritV Λr (Bus1 Q Λr C₁) z) (Xr).slip (WritV Λr (Bus2 Z' Λr C₁) z) (Xr).v) U G₀ v) l = Roots.snow Λr C₁ (fun i=>∫ y,γ i y∂city _) l:=by
 intro Y0 γ
 let F(z:Key J):ℂ:=Y.v+- α_ξ s z; have hR : River F:=by
    have hk(i:J): River (fun z:Key J=>z i*s i):= by simp_rw [mul_comm _ (s i)]; exact River.scale (north_r _) _
    let s0:=α_ξ s; have hk: River s0:= (tip_bank _ _ fun i _=>hk i).1; refine dub_V (zeroR _) ?_; exact (hk.scale (-1)).cong (fun z h=> (neg_one_smul ℂ _).symm) -- tune
 have hf(t: List J):= ink_F V Xo Yo Zo F v u Xp hX (D1:=K₀) (D2:=K₁) (D3:=K₂) (fun z _=>⟨(C.power z).1,(C.power z).2,(C.power z).3⟩) hR hT H (fun i z=>(C.stem i|>.2.2 z).1) (fun i z=>(C.stem i|>.2.2 z).2) (fun i z=>(C.ear i).2 z) t
 refine ⟨fun i=> (hf i).2.1,?_⟩
 have hb:= RillK.link V Xo Yo Zo X_R Kν Lt eW σ Xp s C₁ Q Z' τ0 hxS l hl v he l (List.Sublist.refl l)
 exact hb.trans (rer _ _ _ fun j _=>(hf j).2.2)
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
