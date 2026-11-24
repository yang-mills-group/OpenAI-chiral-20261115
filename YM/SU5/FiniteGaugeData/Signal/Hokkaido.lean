import YM.SU5.FiniteGaugeData.Signal.Dreamy
import YM.SU5.FiniteGaugeData.Reliance.Chest
/-!
 Cover and widths. Urban estimate price absorbing book thickness from approximation grants
 chosen at H as long as number of insertions selected sufficiently large. -/
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper
namespace IgnoreFog
variable (v:Cover) (d r k:ℕ) {n:Side}

def browse (T:Finset Cover): Finset Cover:= univ.image (fun i:Satin.Tag T=> (who T i).1)
def apart (W:Finset Cover) := browse (castle v d)\W
lemma inside_b(T:Finset Cover)(i:Cover) : i∈browse T ↔ nodeC i∈T := by
 refine ⟨fun v=>?_, fun v=>?_⟩
 · obtain ⟨⟨⟨i,v,t⟩,p⟩,u,rfl⟩:= mem_image.mp v; exact p
 exact mem_image.mpr ⟨(⟨(i,0,Classical.arbitrary SU.Slot),v⟩:Satin.Tag T),mem_univ _,rfl⟩
lemma sole {T:Finset Cover}(p: Hosp T n): Set.InjOn (wrap n) (↑(browse T)):=by
 intro x v y u h; exact Satin.nodeC_inj (p.seat_ ((inside_b ..).mp v) ((inside_b ..).mp u) (by rw [←node_of,←node_of,h]))

lemma appear (W:Finset Cover)(p:∀ i∈W,nodeC i∈ castle v d)(h: Hosp (castle v d) n): floors (wrap (More n) v) (W.image (wrap n)) d = (apart v d W).image (wrap n):=by
 ext x; let t:=(wrap (More n) v); let T:=castle v d; let X:=W.image (wrap n); simp_rw [flo]; change node x∈planar n v d ∧ x∉X ↔ _
 rw [←castle_plan v d n]; constructor
 · intro u; let l:Single n:=((x,0),Classical.arbitrary SU.Slot); obtain ⟨y,q⟩:= occupy_fills h l ((modes_at (region T n) l).2 u.1)
   let z:=(Satin.who T y).1; have he: wrap n z=x:= congrArg (fun v:Single n=>v.1.1) q; have hk:z∈browse T:=mem_image_of_mem _ (mem_univ y)
   exact mem_image.mpr ⟨z,mem_sdiff.mpr ⟨hk,fun V=> u.2 (mem_image.mpr ⟨z,V,he⟩)⟩,he⟩
 intro u; obtain ⟨x,y,rfl⟩:=mem_image.mp u; obtain ⟨hx,e⟩:=mem_sdiff.mp y; have he:= (inside_b (castle v d) _).1 hx
 constructor; · rw [node_of]; exact mem_image_of_mem (wrap _) he
 intro t; obtain ⟨t,l,u⟩:=mem_image.mp t; exact e ((sole h ((inside_b T _).2 (p t l)) hx u) ▸ l)

open Buffered.Reliance
lemma occupants:Buffered.Reliance.occupy (castle v d) (2*d):= by
 intro i; refine ⟨v i-d,fun x p=>?_⟩; obtain ⟨a,b,rfl⟩:=mem_image.mp p; obtain ⟨m,n⟩:= box_test.mp b; have x:=m i; have y:=n i; change _≤a i+ v i ∧ a i+ v i ≤ _; omega

def centre (ℓ q:ℕ) : Cover:=(ℓ+q) • step 3
lemma patch_sits {ℓ:ℕ}: starboard 3 0 ℓ (castle (nodeC (centre ℓ d)) d):= by
 intro i t; obtain ⟨a,b,rfl⟩:=mem_image.mp t; have he:= (box_test.mp b).1 3; change _≤ a 3+ nodeC _ 3; unfold nodeC; simp [centre]; omega

-- broadcast numeric election target (given actual price C per tenant).
def dose (C:ℝ) (k:ℕ) : ℝ := - (C * (16*(k+1:ℝ))^4)-8
lemma fee(k:ℕ){C:ℝ}(p:0 ≤ C) : 0 < Real.exp (dose C k):= Real.exp_pos _
-- choose d ceiling support D = squareWidth Q gap + K0tail etc; enough Q.
lemma absorb (K:Calibration){C:ℝ} {k r d:ℕ} (p:0≤C)(e:0<r)(f:d+addgap K ≤ r):
    let d':=squareWidth r k+d; Real.exp (dose C k)^ (r^4)* magnified K C (2*d') ≤ 1/8:=by
 intro q; unfold magnified; rw [←Real.exp_nat_mul, ←Real.exp_add]; apply (Real.exp_monotone (a:=(↑(r^4))* _ + _) (b:= -(8:ℝ)) ?_).trans; · rw [Real.exp_neg,inv_eq_one_div]; apply one_div_le_one_div_of_le (by norm_num); linarith [Real.add_one_le_exp (8:ℝ)]
 have he : 2*(2*q+addgap K) ≤ r*(16*(k+1)) :=by
    let t:=addgap K; change 2*(2*((2*(k+1)*r)+d)+ _ ) ≤ _; have hb: r≤(k+1)*r:=Nat.le_mul_of_pos_left _ (by omega); nlinarith
 have hg: ((↑(2*(2*q+addgap K)):ℝ))^4 ≤ (r*(16*(k+1:ℝ)))^4:=by exact_mod_cast (pow_le_pow_left₀ (Nat.zero_le _) he 4)
 unfold dose; have hh:(1:ℝ)≤ r^4:=by exact_mod_cast(one_le_pow₀ e (n:=4)) -- tune
 push_cast; push_cast at hg; nlinarith only [mul_le_mul_of_nonneg_left hg p,hh]
end IgnoreFog
end YM.CF.Signal
