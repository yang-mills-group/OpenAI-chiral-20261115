import YM.CF.Milo.Rune
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Weigh
import YM.CF.Milo.Hand
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
variable {e' a' b' :ℝ}(v:P.threshold ≤ a)(bq:q+10 ≤ P.B)(hk:cipherK q ≤ 5*P.B)(uB:3≤P.B)(p0:HopeT δ e' a' P.order)(t0:P.threshold ≤ a')(h0:1≤h)
local notation "Xq"=> fondC p g M H P i
local notation "A0"=> (fun A:Op JS=> Matrix.trace A • (1:FC (Dwell n)))
local notation "Lx"=> (Glyph.fondC p g M A0 P i)
open Haro
lemma wireH(i j x y:JS): crumb (wire true i*wire false j) (tray x y)= if (x,y)=(i,j) then parity (n:=Dwell n) (true,i) {(false,j)} else 0:=by
 have he:(true,i)∉ ({(false,j)}:Finset (LeanV (Single n))):=by simp
 rw [show wire true i*wire false j=_ from (show wire true i*wire false j= parity (n:=Dwell n) (true,i) {(false,j)} • poke (tray i j) from ?_),crumb_scale,Pastry.chip]; simp only [show (Haro.tray x y=Haro.tray i j) ↔(x,y)=(i,j) from (by exact Haro.tray_in.eq_iff (a:=(x,y)) (b:=(i,j)))]; split<;>simp
 unfold Haro.tray poke; rw [Poly.tag_any _ _ _ he,Poly.tag_once,smul_smul,parity_sq,one_smul]; rfl
lemma hit_u(F:Op (Single n))(v:Cipher n)(t:v.val=faceD true false F):orbitPH v=F:=by
 ext i j; unfold orbitPH; rw [Matrix.of_apply,Prism.port_eq,if_neg (show (true,i)≠(false,j) by simp),t,faceD,twinD]; change parity _ _ * crumb (∑ i,∑ j,_ ) (tray i j)= _
 simp_rw [crumb_sum,crumb_scale,wireH]; simp only [Prod.mk_inj,mul_ite, mul_zero]; -- tune
 rw [sum_eq_single i,sum_eq_single j]; simp only [ite_true, true_and]; rw [mul_left_comm, parity_sq,mul_one]
 · intro b p h; rw [if_neg]; simp; exact h.symm
 · simp
 · intro b _ h; refine sum_eq_zero fun v c=> if_neg (not_and_of_not_left _ h.symm)
 simp
lemma ps_k {ι:Type*}(S:Finset ι)(F:ι→ Cipher n):orbitPH (∑ i∈S,F i)=∑ i∈S,orbitPH (F i):=by
 ext i j; unfold orbitPH; rw [Matrix.sum_apply]; simp_rw [Matrix.of_apply,Prism.port_eq, show (true,i)=(false,j)↔False from (by simp),ite_false,Cadre.handle,crumb_sum,mul_sum]
local notation "Xb"=> Glyph.fondC p g M (faceD true false) P i
local notation "Ck"=>Pastry.cane (Dwell n)
variable (Wκ:∀ S:Support (More n),S.card≠1→ M.W S=0)
include v p g bq hk uB p0 t0 h0
lemma matrix_f (A:Vow.Aura n)(V:Orbit n)(t:pingS P.threshold A.val V.1):∑ T∈ web0 A, Haro.orbitPH (Xb T V.1)= ∑ S∈αW P.B A, M.F S i (roller g p V):=by
 rw [←ps_k]; apply hit_u
 rw [pact_Y p g (pal_v h h0) M i v bq hk uB p0 t0 h0 A] -- tune proof rw uses V not V.1 matching?
 have hv:(coll_T P A ∅ (M.into.vik (faceD true false) p g P i A) V)= M.into.vik (faceD true false) p g P i A V:=by
    exact Crate.pointV ((M.into.turnX (pal_v h h0) p g p0 t0 v bq hk uB i).scope A A ∅ (subset_refl _) (empty_subset _) (by simp [Lattice.halo])).toCrate V (show V.1∈σX P A ∅ from ⟨by rw [sdiff_empty]; exact t,empty_subset _⟩)
 rw [hv, Sault.rind]; let Z:=∑ S∈αW P.B A,M.F S i (roller g p V); have he: M.into.vik (faceD true false) p g P i A V=faceD true false Z:=by
    unfold Lawn.vik actsF; rw [Finset.sum_apply]; let G(X:SO):=(Hest.boat (M.F X i (roller g p V))); have he:=Cadre.handle (αW P.B A) G -- tune
    change (∑ S∈αW P.B A,(G S).val)= (Hest.boat Z).val; rw [←he]; exact congrArg Subtype.val (Hest.boats ..)
 rw [he]; exact (show (Pastry.cane (Dwell n)).eval (faceD true false Z)= _ from (face_flour true false Z|>.allP).symm)
include Wκ
lemma cheapV (S:SO)(z:S∈ panel P T)(V:Orbit n)(g':1<coverNumber P.B T.val.2): Glyph.vote (M.F S i) p g P (faceD true false) T V.1=0:=by
 have hc:S.card≠1:=by
    intro h; obtain ⟨x,q⟩:=Finset.card_eq_one.mp h; have hv:T.val.2= Lattice.halo P.B S:= (mem_filter.mp (mem_filter.mp z).1).2; exact (not_lt_of_ge (by rw [hv,q]; exact AnalyticBridge.CouplingShape.ballPaid _ x)) g'
 have he(x:Openc (More n) δ):M.F S i x=0:=by
    ext i' j; apply norm_le_zero_iff.mp; have ht:=(M.coat S|>.1 i|>.expo i' j).bounded x; rw [Wκ S hc] at ht; exact ht
 apply Subtype.ext; rw [(runT p g (pal_v h h0) M i v bq hk uB p0 t0 h0 T S z) V]; unfold coll_T; split; next t=>rw [cure,he]; unfold Sault.rind; simp only [faceD,twinD,Matrix.zero_apply,zero_smul,sum_const_zero,map_zero]; rfl
 exact map_zero (Pastry.cane (Dwell n)).eval
end Glyph
end YM.CF.Sour
