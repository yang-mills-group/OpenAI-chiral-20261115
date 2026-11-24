import YM.CF.Milo.Hue
import YM.CF.Milo.Table
import YM.CF.Milo.Foil
import YM.CF.Milo.Sucre
import YM.CF.Milo.Leg
import YM.CF.Sour.Rate
import YM.CF.Sour.Millet
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
namespace Glyph
variable {δ a b u e W:ℝ}{μ:Toll (Single n)}{S:Support (More n)}
variable (F:Raw (Openc (More n) δ) (Single n)){q:ℕ}{K:Scree.Loom n}(p:Roof n a δ q K)(g:0<δ)(t: Suite (badge _) (bail n δ) (bail n δ) S μ F)
variable {H:Op (Single n)→FC (Dwell n)}{Z':Single n→ Single n→ FC (Dwell n)}{h:ℝ}(f: Glyph H Z' h)
variable (T:Scree.Hub n)(z:T.val.1∈ S)(x:S∈αW P.B (Bake.lagE T))
open Ione Bake Nor Larch Levier Salt
local notation "Hz"=>Scree.Hub n
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable (w:Sweep n)(M:Elm n κ δ e u)
local notation "R"=> Salt.actY w
local notation "W'"=> moveHub w
local notation "GZ"=> panel P
local notation "Λ"=> Ione.suit_Y w
local notation "Δ"=> sauce w.charge (detX w.s) (Sour.γS w)
variable (i:κ)
lemma rot_u(j:SO): R j∈ GZ (W' T)↔ j∈GZ T:=by
 have he(k:Hz)(x:SO):x∈panel P k↔_:= (mem_filter:x∈panel P k↔x∈αW P.B (lagE k) ∧ k.val.1∈x); rw [he,he T,show lagE (W' T)= _ from (Subtype.ext rfl : lagE (W' T)=moldA w (Bake.lagE T)), BondL.recoil w]; exact and_congr Iff.rfl (by simp [actY,moveHub])
variable {e' a' b' :ℝ}(v:P.threshold≤ a)(bq:q+10 ≤ P.B)(hk:cipherK q≤ 5*P.B)(uB:3≤ P.B)(p0:HopeT δ e' a' P.order)(t0:P.threshold ≤ a')(h0:1≤ h)
include p g v bq hk uB p0 t0 h0 f
local notation "F0"=> fun S=> M.F S i
lemma runT (j:Scree.Hub n)(D: SO)(y:D∈panel P j):picture (M.F D i) p g P H j (vote (M.F D i) p g P H j):= (express _ p g (M.coat D|>.1 i) f j (mem_filter.mp y).2 (mem_filter.mp y).1 bq v p0 t0 hk uB h0).1
variable {b₀:Bool}(hT:leafJ w b₀ M M)(c:∀ x: Op (Single n), sauce w.charge (detX w.s) (Sour.γS w) (H x)=H (realR w b₀ x))
include hT c
lemma stem_t (x: SO)(hv:x∈ panel P T)(V:Pane n):vote (M.F (R x) i) p g P H (W' T) (flashA w V)=Λ (vote (M.F x i) p g P H T V):=by
 obtain ⟨X,p'⟩:= (sepT (n:=n)).exists; let Z: Orbit n:=(V,X); let U:=lagE T; let L:=(moldA w U); have hp: lagE (W' T)= L:=Subtype.ext rfl
 have he:=runT p g f M i v bq hk uB p0 t0 h0 T x hv Z; -- tune apply params
 have hx:=runT p g f M i v bq hk uB p0 t0 h0 (W' T) (R x) ((rot_u T w x).mpr hv) (yellA w Z)
 let G:= Glyph.cure H p g (M.F x i); let G':=Glyph.cure H p g (M.F (R x) i); apply Subtype.ext; change (vote _ _ _ _ _ _ (yellA w Z).1).val=Δ (vote _ _ _ _ _ _ Z.1).val; rw [he,hx,hp,Sault.plower]; apply congrArg
 have hR(T: Scree.Hub n)(X:SO)(u:X∈panel P T):let Q:= lagE T; Crate P Q ∅ Q (Glyph.cure H p g (M.F X i)):=by
    intro Q; have hv:= (mem_filter.mp (mem_filter.mp u).1).2; exact Glyph.horn f p g (M.coat X|>.1 i) v (by simp [Lattice.halo]) (hv ▸ Corona.halo_mono bq le_rfl) (subset_refl _)
 let O:=hR _ _ hv; have hb:=rot_u T w x|>.mpr hv; have hd:Crate P L (R ∅) L G':=by rw [show R ∅=∅ from map_empty _]; exact hp ▸ hR _ _ hb
 change coll_T _ _ _ G' _= Δ (coll_T _ _ _ G _); nth_rw 1 [←show R ∅=∅ from map_empty _]; by_cases q:Gates (σX P U ∅) U.val V; swap
 · unfold coll_T; rw [if_neg q,if_neg  (show ¬Gates (σX P L (R ∅)) L.val (yellA w Z).1 from (lights_V P.threshold U.val ∅ w V).mp.mt q),sauce,singT,win_z,map_zero]
 obtain ⟨x₁,y,b⟩:=q; let Y:Orbit n:=(x₁,X); let S:=yellA w Y; have hz:= yellow w Z Y U.val b (show Set.EqOn Z.2 Y.2 _ from fun i _=>rfl)
 rw [O.latch Z Y b (fun _ _=>rfl),O.pointV Y y,hd.latch _ S hz.1 hz.2,hd.pointV S ((lights_C ..).mpr y)]
 have ht: roller g p S=Sour.fog w δ (roller g p Y):=Subtype.ext ((congrArg Tulip.profile (p.move x₁ X w p')).trans (real_box w _ _ _ (show (roller g p Y).val=Tulip.profile (K Y) from rfl)).symm)
 unfold G' Glyph.cure; rw [ht, hT _ _ (K Y) _ rfl,c]
lemma vein(V:Pane n):doveK p g F0 P H (W' T) (flashA w V)=Λ (doveK p g F0 P H T V):=by
 unfold doveK; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; symm; refine sum_bij (fun j _=>R j) (fun j h=> (rot_u T w j).mpr h) (fun x _ y _ p=> map_injective _ p) ?_ ?_
 · intro x p; have hv: R (actY w⁻¹ x)=x:=by ext; simp [actY,sitU]
   exact ⟨actY w⁻¹ x,(rot_u T w _).mp (hv.symm ▸ p),hv⟩
 intro j p'; have he:(R j).card=j.card:=card_map _; rw [Pi.smul_apply,Pi.smul_apply,map_smul,he]; congr 1; exact (stem_t p g f T w M i v bq hk uB p0 t0 h0 hT c j p' V).symm -- tune rw
end Glyph
end YM.CF.Sour
