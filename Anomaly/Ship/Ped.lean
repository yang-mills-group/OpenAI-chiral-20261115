import Anomaly.Ship.Flow
import Anomaly.Ship.Salary
import Anomaly.Ship.Tines
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew

variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}

open QuadClock Bake Rive Swell Prism Leaf -- tune
local notation "Πe"=>Seat n
variable {P:BudgetPoint}{D:Finset I}{U:Key I→Pax n}{W:Key I→Cusp n}{E:Key I→RegBudget n}{K:Key I→ForceBudget n}{X Y:Key I→Bag n}{Z:Key I→ℂ}{σ:I→Seat n}
variable {a b c d t:ℝ}
variable (V:Diesel P σ h d t U W E Z)
local notation "T_X" x:max=> grainT P (U x) (W x)
structure Rears (σ:I→Seat n)(F:Key I→Bag n) : Prop where
 hus:Rive.Hush σ ∅ (fun _=>Unit.unit) -- dummy tune
 heads: ∀ X:Aura n,Hush σ X.val (fun z=> F z X)
 dollars: ∀ (X:Aura n)(v:Orbit n),River (fun z=> F z X v)
include V
lemma backs : Rears σ (fun x=> T_X x):=by
 refine ⟨fun _ _ _ _ _=>rfl,fun X x u y v k=>?_,fun X q=>?_⟩
 · change grainT _ _ _ _= _; funext R_; unfold grainT; simp only [Pi.sub_apply]; apply congrArg₂ (·-·)
   · unfold frostC capR; rw [show U x X=U y X from V.span X x u y v k]
   unfold toastC; split_ifs; · exact congrArg Subtype.val (congrFun (show W x X (_ ∩ X.val)= W y X (flags P.threshold R_.1 ∩ X.val) from V.cup X _ inter_subset_right x u y v k) R_)
   rfl
 unfold grainT; simp only [Pi.sub_apply]; simp_rw [sub_eq_add_neg]; refine dub_V ?_ (yorkB _ ?_)
 · by_cases u:q∈ pingMask P X.val; swap; · refine (zeroR (0:FC (Dwell n))).cong ?_; intro z _; apply Set.indicator_of_notMem u
   exact (sc_V (V.crop X q) sheen).cong fun x _=> Set.indicator_of_mem u (fun z=>(U x X z).val)
 unfold toastC; split; exact sc_V (V.heat X _ inter_subset_right q) sheen; exact zeroR _
omit V
lemma rear_add (p:Rears σ X)(q:Rears σ Y) : Rears σ (X+Y):=by
 refine ⟨p.hus,fun i a t b u h=> congrArg₂ (· + ·) (p.heads i a t b u h) (q.heads i a t b u h),fun i v=>dub_V (p.dollars i v) (q.dollars i v)⟩
lemma rear_sc(p:Rears σ X)(w:ℂ): Rears σ (w • X):=⟨p.hus,(fun i a t b u h=> congrArg (w • ·) (p.heads i a t b u h)),fun i v=>(p.dollars i v).scale _⟩
-- RIVER at ordinary coordinates
lemma rear_arc(p:Rears σ X)(r:Rears σ Y) : Rears σ (fun i=> regionW (X i) (Y i)):=by
 refine ⟨p.hus,fun X' a t b u h=> ?_,fun X' v=>?_⟩
 · unfold regionW Ktw; apply sum_congr rfl; intro V _; apply sum_congr rfl; intro Z _; split; next z=>
       dsimp only [cBump]; have hv: V.val⊆ X'.val:=z ▸ subset_union_left; have hz:Z.val⊆ X'.val:= z ▸subset_union_right; rw [show X a V=X b V from p.heads _ a t b u (fun i w=> h i (hv w)), show Y a Z= Y b Z from r.heads _ a t b u (fun i w=> h i (hz w))]
   rfl
 unfold regionW Ktw; simp_rw [Finset.sum_apply]; refine tick_sum _ _ (fun i _=> tick_sum _ _ (fun w v'=> ?_)); split; swap; exact zeroR _
 unfold cBump; simp_rw [sub_eq_add_neg]; exact dub_V (buoy_mult (p.dollars i v) (r.dollars w v)) (yorkB _ (buoy_mult (r.dollars w v) (p.dollars i v)))
lemma rear_up(p:Rears σ X)(q:Rears σ Y) : Rears σ (fun i=> weaveOut (X i) (Y i)):= rear_add (rear_add p (rear_arc p q)) (rear_sc (rear_arc (rear_arc p q) q) ((2:ℂ)⁻¹)) -- tune _
lemma series_R {F:Key I→I→Bag n}(T:∀ i:I, Rears σ fun v=>F v i)(p:∀ (v:Key I),v∈hill I→∀ (i:I)(x:Aura n),σ i∉x.val → F v i x=0):Rears σ fun x=>pinSeries (F x) x:=by
 refine ⟨fun _ _ _ _ _=>rfl,fun i z s j t h=> ?_,fun i v=>?_⟩
 · unfold pinSeries; refine sum_congr rfl fun k _=>?_ ; by_cases u:σ k∈i.val
   · rw [h k u,show F z k i=F j k i from (T k).heads _ z s j t h]
   rw [p _ s k i u,p _ t k i u]; simp
 unfold pinSeries; simp_rw [Finset.sum_apply, Pi.smul_apply]; refine tick_sum _ _ fun k _=>?_
 let K:= (T k).dollars i v; let Q:= Roots.north_r k
 exact ⟨Q.shore.smul K.shore,fun a t b x u=>(Q.slope a t b x u).smul (K.slope a t b x u)⟩
lemma grain_to_zero : grainT P (0:Pax n) (0:Cusp n)=0:=by
 funext X x; unfold grainT; simp only [Pi.sub_apply,Pi.zero_apply]; apply sub_eq_zero.mpr; unfold frostC toastC capR; simp only [Pi.zero_apply,ZeroMemClass.coe_zero,Set.indicator_zero]; split<;> rfl
lemma noon_G (A:Bag n) : weaveOut A 0=A:=by
 have hz(F:Bag n): regionW F 0=0:=by funext x; simp [regionW,Ktw,cBump]
 unfold weaveOut; rw [hz,hz]; simp
lemma roll_none (A:Bag n):weaveOut 0 A=0:=by
 have he:regionW 0 A=0:=by funext x; simp [regionW,Ktw,cBump];
 unfold weaveOut; rw [he,he]; simp
end YM.CF.Vow.TreasuryFog
