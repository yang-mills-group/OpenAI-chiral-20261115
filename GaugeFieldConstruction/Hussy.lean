import GaugeFieldConstruction.Herve
import GaugeFieldConstruction.Synod
import YM.UVNext.PRICED_KERNELS.Basin
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
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
variable (I:Type)[LinearOrder I][Fintype I]
variable {e a d b c f l:ℝ}(F:Elm n Unit e a c)(R:Loom n)(k u:ℝ)(p:BudgetPoint)(m:ℕ)(b0:ℝ)(T:Ids n)
local notation "Y"=> Single n
local notation "eV"=>eBook I F R u m b0 T
local notation "Kern"=> street I F R u m b0 T
variable (v: Roof n u k m R)(h:k<e)(hp:0<e)(v0:0≤b0)(tK:coinH f b0)(z:hud_T 7 f)(t:1 ≤f)(w:p.threshold≤u)(s:p.order≤6)
variable (Z:Finset (Seat n))(A: Pane n)(L:Tulip.Male)(r:ℕ)(uF: NearL F (fun _=>hemi_L n r L))(g:groupShape F)(pw:pure_Rim F)
namespace SeasonH
open Thera
open Sault
lemma half_H (Z:Hubber n): star (halfP Z)=halfP Z:=by unfold halfP; change Matrix.conjTranspose _ = _; rw [Matrix.diagonal_conjTranspose]; simp only [Pi.star_def]; congr 1; funext i; split<;>simp
lemma half_w (Z:Hubber n)(b:Bool): windX b (halfP Z)=halfP Z:=by cases b; rfl; unfold halfP windX cc; simp; simpa [halfP] using half_H Z -- tune
lemma Pivot_half (U: UNI Y)(W:Hubber n)(F: ∀ i j,U.val i j≠0 → (Ekm n (true,i)∈W ↔ Ekm n (true,j)∈ Z)): twist U (halfP Z)=halfP W:=by
 apply Mir.twist_comm; ext i j; unfold halfP; rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; by_cases h:U.val i j=0; rw [h,zero_mul,mul_zero]; simp only [F i j h]; rw [mul_comm] -- tune use `simp_rw [F]`
include h v hp t v0 tK
lemma Lab_τ (T':Ids n)(X:Hubber n): Lar_M F R u m T' A X=Lar_M F R u m T A X:=by ext i j:1; let G:= (LArmor0 Unit F R k u m b0 T v h hp v0 tK i j X).1; exact arm_inv _ _ v T h G A T' -- n arguments
include g pw
lemma κMood (V:Sweep n) (X:Hubber n):Lar_M F R u m T (flashA V A) (actY V X)= if detX V.s then - (ech V (Lar_M F R u m T A X)) else ech V (Lar_M F R u m T A X):=by -- positive sign!
 obtain ⟨i,p'⟩:= (Skye.sepT (n:=n)).exists
 let L:= R (A,i); have he:releaseQ F (actY V X) (R (flashA V A,bun V i))=(if detX V.s then -ech V (releaseQ F X L) else ech V (releaseQ F X L)):=by rw [v.move _ _ _ p']; exact subtractWind pw L X ((v.paid _).shrink (le_of_lt h)) hp g V -- implicit rhs unresolved
 rw [←Lab_τ F R k u m b0 T v h hp v0 tK t (flashA V A) (bun V i),←Lab_τ F R k u m b0 T v h hp v0 tK t A i,lar_C,lar_C]; simp only [show flag_H _ _ _ (flashA V A)↔ flag_H X m u A from by unfold flag_H; rw [walkA,flagsA]; exact Finset.disjoint_map _]; split
 exact he
 unfold ech; split <;> simp [singT,win_z]
lemma Moon_stamp(V:Sweep n): Moon_M F R u m T (actY V Z) (flashA V A)= if detX V.s then -ech V (Moon_M F R u m T Z A) else ech V (Moon_M F R u m T Z A):=by
 let M(X:Hubber n):= if Sect X m⊆ actY V Z then Lar_M F R u m T (flashA V A) X else 0
 have he:Moon_M F R u m T (actY V Z) (flashA V A)=∑ X,M (actY V X):=by
    symm; exact sum_bij (fun x _=>actY V x) (fun _ _=>mem_univ _) (fun _ _ _ _ h=>map_injective _ h) (fun i _=>⟨actY V⁻¹ i,mem_univ _,by ext; simp [actY,sitU]⟩) (fun _ _=>rfl)
 let N(X:Hubber n):= if Sect X m ⊆ Z then Lar_M F R u m T A X else 0
 have hv(X:Hubber n): M (actY V X)= if detX V.s then -ech V (N X) else ech V (N X):=by
    unfold M N Sect; simp only [walkA,show actY V (halo _ _) ⊆ actY V Z ↔ (halo (m+8) X)⊆ Z from Finset.map_subset_map]; split; exact κMood F R k u m b0 T v h hp v0 tK t A g pw V X; unfold ech; split <;> simp [singT,win_z]
 rw [he]; simp_rw [hv]; split_ifs with H; rw [sum_neg_distrib]; unfold ech Moon_M; simp [singT,win_sum,N]; unfold ech Moon_M; simp [singT,win_sum,N] -- likely simp failure
omit g pw
lemma film_L (G:Agora n)(X:Hubber n): Lar_M F R u m T (GA G A) X=twist (tradew n G) (Lar_M F R u m T A X):=by
 rw [←Lab_τ F R k u m b0 T v h hp v0 tK t (GA G A) (threadG G T),lar_C,lar_C]; unfold GA flag_H; rw [RG.gauge_flags]; split; rw [v.rev]; exact norm_enter X (R (A,T)) ((v.paid _).shrink h.le) hp G; rw [map_zero] -- tune norm_enter args
lemma Moon_Part(G:Agora n): Moon_M F R u m T Z (GA G A)=twist (tradew n G) (Moon_M F R u m T Z A):=by unfold Moon_M; rw [map_sum]; apply sum_congr rfl; intro i _; split; exact film_L F R k u m b0 T v h hp v0 tK t A G i; exact (map_zero _).symm
omit v0 tK t
include pw
lemma moon_herm : star (Moon_M F R u m T Z A)=Moon_M F R u m T Z A:=by
 unfold Moon_M; rw [star_sum]; apply sum_congr rfl; intro i _; split; next a=> rw [lar_C]; split; exact releaseHerm pw _ i ((v.paid _).shrink h.le) hp; exact star_zero _
 exact star_zero _
omit pw h v hp
lemma half_star : star (halfP Z)=halfP Z:=half_H Z
lemma half_motion (V:Sweep n):twist (launchZ V) (halfP Z)=halfP (actY V Z):=by
 refine Pivot_half Z _ _ fun i j z=>?_
 have hh:boxA V (node i.1.1)= node j.1.1:= Tye.birth_l i j (castX V) (spinU V.charge V.s) V.charge z
 change node i.1.1∈actY V Z↔ node j.1.1 ∈ Z; simp [actY,hh] -- tune
lemma half_frame(G:Agora n): twist (tradew n G) (halfP Z)=halfP Z:=by
 apply Pivot_half Z _ _; intro i j z; change node i.1.1∈Z ↔ node j.1.1∈Z; rw [show i.1=j.1 from ?_]; by_contra p; apply z; simp [tradew,jump_apply,p]
-- abstract H wall in half/core
structure Altaz (U:UNI Y)(b l:Bool)(B C B' C':Op Y):Prop where
 shine0 :star B=B
 shine1 : star C=C
 auth: twist U (windX b B)= if l then C' else B'
 endo: twist U (windX b C)=if l then B' else C'
include h v hp v0 tK t pw
local notation "Λ0" x:max y:max=> blade0 F R u m T x y
local notation "Λ1" x:max y:max=> blade1 F R u m T x y
lemma Beef_P (G:Agora n): Altaz (tradew n G) false false (Λ0 Z A) (Λ1 Z A) (Λ0 Z (GA G A)) (Λ1 Z (GA G A)):=by
 have hh:=moon_herm F R k u m T v h hp Z A pw; have hv:=Moon_Part F R k u m b0 T v h hp v0 tK t Z A G
 constructor <;> simp only [blade0,blade1,hv,windX,star_add,star_sub,half_star,hh,map_add,map_sub,half_frame,ite_false, Bool.false_eq_true]
include g
lemma Beef_R (V:Sweep n):Altaz (launchZ V) V.charge (detX V.s) (Λ0 Z A) (Λ1 Z A) (Λ0 (actY V Z) (flashA V A)) (Λ1 (actY V Z) (flashA V A)):=by
 have hh:=moon_herm F R k u m T v h hp Z A pw; have hv:=Moon_stamp F R k u m b0 T v h hp v0 tK t Z A g pw V
 constructor <;> simp only [blade0,blade1,hv,star_add,star_sub,hh,half_star]
 · rw [show windX _ (_+_) = halfP Z + windX V.charge (Moon_M F R u m T Z A) from ?_,map_add,half_motion]; unfold ech; simp only [singT]; split_ifs<;> simp only [sub_neg_eq_add] <;> rfl
   let b:=V.charge; rw [win_a,half_w] -- tune name
 · rw [win_l,half_w,map_sub,half_motion]; unfold ech; simp only [singT]; split_ifs <;>simp only [←sub_eq_add_neg] <;> rfl
#print axioms Beef_P
#print axioms Beef_R
end SeasonH
end MastTin
end YM.CF.XGarden
end
