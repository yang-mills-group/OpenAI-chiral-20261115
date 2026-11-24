import YM.CF.BProof.Axial.Orchard
import YM.CF.BProof.Floral.Baker
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Axial
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
open Exa Tap Dial
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
open Mew Floral
open scoped YM.CF.Mew
variable {T S:BeatL n}{U:Scree.Loom n}{R t d a b c W z₀ z₁:ℝ}{q:ℕ}
structure Arbor (p:BudgetPoint)(U:Scree.Loom n)(q:ℕ)(t d W z₀ z₁:ℝ):Prop where
 tile:Roof n t d q U
 pos:0<d
 hw:1≤W
 paid:HopeT d z₀ z₁ p.order
 hv:p.threshold≤z₁
 y:p.threshold≤t
 hx:q+10≤p.B
 v:cipherK q≤5*p.B
 w:3≤p.B
variable (k:Arbor P U q t d W z₀ z₁) (F:Elm n (ΘS 1) d a b){H:Op (Single n)→FC (Dwell n)}{Z:Single n→ Single n→ FC (Dwell n)}(h: Glyph H Z W)
def font {H:Op (Single n)→FC (Dwell n)}{Z:Single n→ Single n→ FC (Dwell n)}(h:Glyph H Z W) : Op (Single n)→ₗ[ℂ]FC (Dwell n) where
 toFun:=H
 map_add' x y:=by rw [h.whirl,h.whirl x,h.whirl y]; simp_rw [Matrix.add_apply,add_smul,sum_add_distrib]
 map_smul' s x:=by change H (_ • x)=s • H x; rw [h.whirl,h.whirl x]; simp_rw [smul_sum, Matrix.smul_apply,smul_smul,smul_eq_mul]
lemma gloss_sum (f:Tiles→Firing n)(r:Tiles→ℝ)(x:Aura n)(i:Orbit n)(D): coll_T P x D (∑ j,r j • f j) i=∑ j,r j • coll_T P x D (f j) i:=by
 unfold coll_T; split
 · simp only [Finset.sum_apply,Pi.smul_apply]
 · simp only [smul_zero,sum_const_zero]
variable (H)
def leafR : SpaceM→ₗ[ℝ]RegBudget n:= stitch fun i=> Glyph.fondC k.tile k.pos F H P (pole i)
def vine : SpaceM→ₗ[ℝ]Bag n := stitch fun i=> F.into.vik H k.tile k.pos P (pole i)
variable {H}
variable (s:0≤R)[Nonempty (ΘS R)](x: ΘS R)
include h
local notation "u"=> k.tile
local notation "hD"=> k.pos
local notation "l"=> (grow F R s)
lemma parcel (X:SO) : Glyph.cure H u hD ((l).F X x)=∑ i:Tiles,cloth i x.val •Glyph.cure H u hD (F.F X (pole i)):=by
 funext V; let v:=roller hD u V; change (font h).restrictScalars ℝ (grows F X v x.val)= _; rw [grows,sit,map_sum]; simp_rw [map_smul,Finset.sum_apply]; rfl
lemma disc (T:Scree.Hub n)(D)(s':D∈Glyph.panel P T) : Glyph.vote ((l).F D x) u hD P H T=∑ i:Tiles,cloth i x.val • Glyph.vote (F.F D (pole i)) u hD P H T:=by
 have e:= Glyph.runT u hD h l x k.y k.hx k.v k.w k.paid k.hv k.hw T D s'
 apply Glyph.picture_I _ _ _ _ e; intro i; have z:=(fun j:Tiles=>Glyph.runT u hD h F (pole j) k.y k.hx k.v k.w k.paid k.hv k.hw T D s' i)
 rw [parcel k F h,gloss_sum]; rw [Finset.sum_apply]; change eat_c.restrictScalars ℝ _ = (Pastry.cane (Dwell n)).eval.restrictScalars ℝ _; rw [map_sum,map_sum]; exact sum_congr rfl fun j _=>by simp_rw [Pi.smul_apply,map_smul]; exact congrArg ((cloth j x.val) • ·) (z j) -- eat_c from Baker; tune namespace
lemma bill : Glyph.fondC u hD l H P x = leafR k F H x.val:=by
 funext i; rw [leafR,sit,Finset.sum_apply]; unfold Glyph.fondC Glyph.doveK; simp_rw [Pi.smul_apply,smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro j hv; rw [disc k F h s x i j hv,smul_sum]; exact sum_congr rfl fun t _=> smul_comm ..
lemma plant : (l).into.vik H u hD P x= vine k F H x.val:=by
 funext i; rw [vine,sit,Finset.sum_apply]; unfold Lawn.vik actsF; simp_rw [Pi.smul_apply,smul_sum]; rw [sum_comm]; exact sum_congr rfl fun j _=> parcel k F h s x j
end YM.CF.Sour.Axial
