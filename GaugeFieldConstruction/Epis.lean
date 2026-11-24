import GaugeFieldConstruction.Euboea
import YM.CF.Yaw.Viv
import GaugeFieldConstruction.Plaid
import GaugeFieldConstruction.Corbie
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
variable {P:BudgetPoint}{K J B I:Type}[LinearOrder I][Fintype I]
variable (σ:I→ Seat n)
abbrev RankU(n:Side):= Option (FinV n×FinV n)
abbrev Vulcan (I:Type)(n:Side):= LoreM n I (RankU n)
local notation "S_"=> Seat n
abbrev PinInk (x:Vulcan I n):InkD n:=fun V=> x.amt V • upperW x.val
variable (e: Vulcan I n)
lemma wickDst (x:S_)(Y:Support (More n))(k:ℕ)(s:∀ i∈e.seat,separation x i≤k):e.seat⊆halo k {x}:=by intro i t; exact halo_spec.mpr ⟨_,mem_singleton_self _,s i t⟩
abbrev ThermalH (L:ℕ) :ℕ:=10*(L+2)
abbrev TiltI:= Option (Bool×Axis)
def line_Y (k:ℕ)(t:TiltI):Lattice.Cover:= t.elim 0 fun p j => if j=p.2 then if p.1 then ↑k else -(k:ℤ) else 0
def Atlas_Y(L:ℕ)(x:S_)(p:BudgetPoint)(d:TiltI):= x-wrap (More n) (line_Y (ThermalH L*p.B) d) -- tune subtype notation x d etc
abbrev coy_Y(L:ℕ)(y:Seat n)(p:BudgetPoint)(d:TiltI):= y+ wrap (More n) (line_Y (ThermalH L*p.B) d)
def Halo_Plus (L:ℕ)(x:S_)(p:BudgetPoint):= Finset.univ.image (Atlas_Y L x p)
def SpacePad (L:ℕ)(p: BudgetPoint)(ι:I→S_)(e:Vulcan I n):Finset S_:= e.seat ∪ (if e.pure then ∅ else (match e.keys with| [i]=>Halo_Plus L (ι i) p | _ => ∅))
lemma ηspace (k:ℕ)(x:S_)(t:TiltI)(h: 2*k < (More n).val):separation x (x-wrap (More n) (line_Y k t))= t.elim 0 (fun _=>k):=by
 let V:= wrap (More n) (line_Y k t); have hx : Lattice.lift V = line_Y k t:=by
    apply Lattice.lift_eq_iff.mpr; refine ⟨rfl,fun i=>?_⟩; rcases t with _|w; · change -(↑(More n).val:ℤ)<2*0 ∧ 2*(0:ℤ)≤ (More n).val; omega
    · unfold line_Y; simp only [Option.elim_some]; split_ifs<;>omega
 unfold separation; rw [sub_sub_cancel]; unfold pdist; change univ.sup (fun i=> (Lattice.lift V i).natAbs)=_; rw [hx]; cases t with
 | none=>simp [line_Y]
 | some t=>
    refine le_antisymm (Finset.sup_le fun i _=>?_) ?_; unfold line_Y; simp only [Option.elim_some]; split_ifs <;> simp
    refine (le_trans ?_ (Finset.le_sup (f:=fun i=> (line_Y k (some t) i).natAbs) (mem_univ t.2))); unfold line_Y; simp only [↓reduceIte, Option.elim_some]; split<;>simp
lemma ThickP (L:ℕ)(p:BudgetPoint)(z:S_)(h:2*(ThermalH L*p.B)<(More n).val): L< coverNumber p.B (Halo_Plus L z p):=by
 by_contra V; let X:=ThermalH L*p.B; let Y:=Halo_Plus L z p;
 let t:TiltI:= some (true,0); let x:= Atlas_Y L z p t; have v: separation z x=X:= ηspace X z t h
 have ht:x∈ Y:=mem_image_of_mem _ (mem_univ _); have he:Atlas_Y L z p none=z:=by simp [Atlas_Y,line_Y]
 have hu:z∈Y:= Finset.mem_image.mpr ⟨none,mem_univ _,he⟩; have hs:=Corona.extent _ p.B hu ht; rw [v] at hs; unfold X ThermalH at hs; have hg:= Nat.mul_le_mul_right (4*p.B+2) (Nat.le_of_not_gt V); change coverNumber _ Y * _ ≤_ at hg; have hp:=p.B_pos; nlinarith
lemma spaces_P (L:ℕ)(P:BudgetPoint)(h:2*(ThermalH L*P.B)<(More n).val)(v:Kingf P σ e): SpacePad L P σ e⊆ halo (ThermalH L * P.B) e.seat:=by
 intro i u; cases Finset.mem_union.mp u with
 | inl w=>exact halo_subset _ _ w
 | inr w=>
    split at w; · exact False.elim (Finset.notMem_empty _ w)
    next k=>
      generalize hv:e.keys=l at w
      split at w
      next j =>
         obtain ⟨t,s,rfl⟩:=Finset.mem_image.mp w
         refine halo_spec.mpr ⟨_,v.port j (by simp [hv]), (ηspace _ (σ j) t h).le.trans ?_⟩; cases t <;> first| exact Nat.zero_le _| exact le_rfl
      exact False.elim (Finset.notMem_empty _ w)
private lemma aid_D {e:Support n}{a d:ℝ}(m B:ℕ)(v:0≤a)(b:0<B)(t:0≤d)(u:a*2*Yaw.χ m≤ B*d)(p:Grove (terr _) e): currency B a (halo (m*B) e) ≤ Real.exp (a*Yaw.χ m)* rent d e:=by
 let T:= Dial.idrat n; have he(x):T.parent x=x:=by nth_rw 1 [← show T.embed x=x from Dial.glass ..]; exact Ratio.embed_parent ..
 have h0:= Yaw.aidV T p (le_refl (m*B)) b v u t; rw [show e.image T.parent=e from (by ext; simp [he])] at h0; exact h0
lemma planet_Z {a d:ℝ} (p:BudgetPoint)(u:0≤a)(t:0≤d)(h:Linca p σ e)(L:ℕ)(hU:2*(ThermalH L*p.B)<(More n).val)(v:a*2*Yaw.χ (ThermalH L) ≤ (p.B:ℝ)*d): currency p.B a (SpacePad L p σ e)≤ Real.exp (a*Yaw.χ (ThermalH L))* Branch.rent d e.seat:=by -- tune n defeq
 refine le_trans ?_ (aid_D (ThermalH L) p.B u p.B_pos t v h.grave); exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Corona.cover_mono (spaces_P _ _ _ _ hU h.stamp) _)) u)
end MastTin
end YM.CF.XGarden
end
