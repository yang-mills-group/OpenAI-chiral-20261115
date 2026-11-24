import GaugeFieldConstruction.Verdant
import GaugeFieldConstruction.Ventana
import GaugeFieldConstruction.Viridian
import GaugeFieldConstruction.Valle
import GaugeFieldConstruction.Canone
import GaugeFieldConstruction.Tropic
import GaugeFieldConstruction.Pliant
import GaugeFieldConstruction.Ethos
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section
open Fock
variable (P:Spine)
open MeasureTheory
open Afterglow -- tune
local notation "Ω"=>P.floorVec
-- Alternative Porch gives linear itself for all tests fit BEntry.B.Q. Thus prove for any p.H3 and shift stamp.
variable {P}
open Papal Papal.FrameP
open CF.XGarden CF.XGarden.MastTin ArtCart
open RG Fock CF.Rush Vale Branch Fock.Flux Tapestry
open YM.Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open RG CF.Skye
open CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open scoped YM.CF.Mew
open CF.TableF TableF.Lenten TableF.Lenten.Layout Py
variable {P:Spine}{S:Finset Cover}{f:P.Test}{F:ℕ→Buffered.Family P.calibration}

open Py.Rate Py.Rate.LocalLimit.Papal Fock.Flux Zpress
open Violets BluffV BluffV.Lave
namespace Heritor
variable (R:P.Heritor)
-- Phys budget for scaled patterns. sequences on Cover.Actors varying roots/times. finite integer.A. margin

open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick
open YM.GaugeFieldConstruction.Cauchy -- tune
open YM.GaugeFieldConstruction -- tune
open SpaΘ
lemma strict_EP {N:Side}{a b:E4}{u:ℕ→ℝ}{A B:ℕ→ AdmitA}(p:a≠b)(v:Tendsto (fun i=> mount (u i) (A i).1) atTop (𝓝 a))(q:Tendsto (fun i=> mount (u i) (B i).1) atTop (𝓝 b))(t:Tendsto u atTop (𝓝 0)):
 ∀ᶠ i:ℕ in atTop, SpaΘ.StrictP N (A i).2.1 (B i).2.1 (A i).1 (B i).1:=by
 obtain ⟨i,h⟩ : ∃ (i:Axis), a i≠ b i:= Classical.byContradiction fun h=>p (PiLp.ext fun i=> Classical.byContradiction (fun h'=>h ⟨i,h'⟩)) -- tune
 let δ:=|a i-b i|
 have ha:0<δ:=abs_pos.mpr (sub_ne_zero.mpr h)
 let v₁(n:ℕ):= (mount (u n) (A n).1) i; let b₁(n:ℕ):= (mount (u n) (B n).1) i
 have hu:∀ᶠ n:ℕ in atTop, 150 * |u n| < |v₁ n-b₁ n|:= by
   have p: Tendsto (fun n=> |v₁ n-b₁ n|) atTop (𝓝 δ):= (((show Continuous (fun y:E4=>y i) by fun_prop).continuousAt.tendsto.comp v).sub ((show Continuous (fun y:E4=>y i) by fun_prop).continuousAt.tendsto.comp q)).abs -- maybe unknown
   refine (tendsto_const_nhds (x:=(150:ℝ))|>.mul t.abs).eventually_lt p ?_; simpa
 filter_upwards [hu] with n v
 let X:= (A n).1; let Y:= (B n).1
 have he(x:StampSet N X)(y:StampSet N Y): Gutter (Wasp N X x).1 (Wasp N Y y).1:=by
   let S:Cover:= LiftSeat (cT:=N) X x; let W:Cover:= LiftSeat (cT:=N) Y y; have hT:= (cart_spec ..).1 ((prospect_R ..).2 (seat_e X x)) i; have ht:= (cart_spec ..).1 ((prospect_R ..).2 (seat_e Y y)) i
   change (S i-X i).natAbs≤24 at hT; change (W i-Y i).natAbs≤24 at ht
   change 42<Signal.Interval.separationCost S W
   apply lt_of_lt_of_le _ (Finset.le_sup (f:=fun k:Axis=> ((S-W) k).natAbs) (Finset.mem_univ i))
   change 42<(S i-W i).natAbs
   by_contra! a
   have e:(X i-Y i).natAbs≤90:=by omega
   have D: |(X i:ℝ)-(Y i:ℝ)|≤90:=by exact_mod_cast (abs_le.mpr (show -(90:ℤ)≤ X i-Y i∧ X i-Y i≤90 from by omega))
   have p: |v₁ n-b₁ n| ≤ |u n| * 90:=by
      change |(u n)*(X i:ℝ)-(u n)*(Y i:ℝ)|≤_
      rw [←mul_sub,abs_mul]; exact mul_le_mul_of_nonneg_left D (abs_nonneg _)
   linarith [abs_nonneg (u n)]
 change SpaΘ.StrictP N _ _ X Y
 cases (A n).2.1<;> cases (B n).2.1 <;> intro u v <;> unfold ChipUp
 all_goals (first | trivial | exact he _ _ | exact ⟨he _ _,he _ _⟩ | exact ⟨he _ _,he _ _,he _ _,he _ _⟩)

-- supply houses for apertures via only any budget E for `1/scale`. E^4 buys. cart house centered near actual chart omega.
lemma mastHaus (P:Spine)(k:ℕ)(b:Axis):
 let a:= k+P.calibration.ℓ +1
 let W:= cartO 0 k
 House P.calibration (2*(a:ℤ)) (fun i=>if i=b then 0 else -(a:ℤ)) 0 (plow P.calibration b a W):=by
 intro a W i x h
 obtain ⟨m,y,g⟩:= plow_stays P.calibration b a W h
 have he:= (cart_spec ..).1 y i; simp only [Pi.zero_apply,sub_zero] at he
 let r:=ruler P.calibration.B; have hr:1≤r:= ruler_gene _; have ht:(a:ℤ)= k+P.calibration.ℓ+1:=by unfold a; simp
 have hz:(a:ℤ) ≤ r*a:=by exact le_mul_of_one_le_left (by positivity) hr
 unfold runnel; change r* _ +_ ≤ _ ∧ _ ≤ _; rw [g]; by_cases q:i=b
 · subst i; unfold r at *; simp [mul_left_comm (ruler _) (2:ℤ)]; omega
 unfold r at *; simp [q, two_mul]; omega
variable (P) {C:ℝ→ℝ} {f:ℝ}{s:ℕ→ℕ}{u:ℕ→ℝ}
lemma PoseUp {a:E4}{A:ℕ→ AdmitA}(h:Tendsto (fun i=> mount (u i) (A i).1) atTop (𝓝 a)): ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop,∀ j:Axis, |u i*((A i).1 j:ℝ)|≤C:=by
 let c:=‖a‖+1; let Z(i:ℕ):= mount (u i) (A i).1; have he:∀ᶠ i:ℕ in atTop, ‖Z i‖≤c:= h.norm.eventually (ge_mem_nhds (lt_add_of_pos_right ‖a‖ one_pos)); -- tune
 refine ⟨c,add_pos_of_nonneg_of_pos (norm_nonneg _) one_pos,he.mono fun i h j=> (show |u i*((A i).1 j:ℝ)| ≤ ‖Z i‖ from PiLp.norm_apply_le (Z i) j).trans h⟩
lemma chartline (p:RunRate 0 f C)(S:Tendsto s atTop atTop)(L:Tendsto u atTop (𝓝 0))(W:∀ᶠ i:ℕ in atTop, 0<u i∧ 1/u i≤ C (P.urnMark (s i)))(b:ℕ)(r:ℝ)(A:ℕ→List AdmitA)
 (v₁:∀ᶠ i in atTop,(A i).length≤b)(v:∀ᶠ i in atTop,∀ a∈ A i,issueA r a)(f':∃ K>0,∀ᶠ i:ℕ in atTop,∀ a∈ A i,∀ j:Axis, |u i*(a.1 j:ℝ)|≤K):
 ∃ V:ℝ→ℝ,∃ q:ℝ,RunRate 0 q V ∧∀ᶠ i in atTop,∀ k:Axis, HouseAudit P b r V k (s i) (A i):=by
 obtain ⟨K,h,t⟩:=f'; let R(x:ℝ):= K*C x+1+temper; let D(x:ℝ):=2*(R x+P.calibration.ℓ+1); let H(x:ℝ):= 128*(16*P.calibration.B.val*D x)^4
 let f':=max 0 f; have hp:∀ (c:ℝ),RunRate 0 f' (fun _=>c):= fun c=> (RunRate.const _).weaker (Or.inr ⟨rfl,le_max_left _ _⟩)
 have hV: RunRate 0 f' R:= (((p.weaker (Or.inr ⟨rfl,le_max_right ..⟩)).cmul K|>.add (hp _)).add (hp _))
 let T:=RunRate.cmul ((((hV.add (hp (P.calibration.ℓ:ℝ))).add (hp (1:ℝ))).cmul 2|>.cmul (16*(P.calibration.B.val:ℝ))).pow 4) 128
 refine ⟨H,f'*(↑(4:ℕ):ℝ),?_,?_⟩
 · simpa only [mul_zero,zero_mul] using T
 filter_upwards [W,t,v,v₁] with i g v V l k
 have hg:0<u i:=g.1; let c:= C (P.urnMark (s i)); have hx:0≤K*c:=mul_nonneg h.le ((div_pos one_pos hg).le.trans g.2)
 let t:= (⌈K*c⌉₊+temper:ℕ); let w:= t+P.calibration.ℓ +1; let σ(j:Axis):ℤ:= if j=k then 0 else -(w:ℤ)
 have u':(t:ℝ) ≤ R (P.urnMark (s i)):=by unfold R t; rw [Nat.cast_add]; exact add_le_add_left (Nat.ceil_lt_add_one hx|>.le) _ -- left
 refine ⟨2*w,σ,cartO 0 t,w,Nat.mul_pos (by decide) (Nat.succ_pos _),by push_cast; exact mastHaus P t k,by simp [σ],?_,l,?_⟩
 · have hv: ((2*w:ℕ):ℝ) ≤ D (P.urnMark (s i)):=by unfold w D; push_cast; gcongr
   unfold Etch.ratio Etch.pitch H; rw [Nat.cast_mul, Nat.cast_pow,Nat.cast_mul]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by push_cast at *; gcongr) _) (by positivity)
 intro a hA; refine ⟨?_,V a hA⟩; intro j z; apply (cart_spec _ _ _).2; intro b
 have ht: |(a.1 b:ℝ)| ≤ ((⌈K*c⌉₊:ℕ):ℝ):=by
    apply le_trans _ (Nat.le_ceil _); have e:= v a hA b; rw [abs_mul,abs_of_pos hg] at e
    apply le_trans _ (mul_le_mul_of_nonneg_left g.2 h.le); field_simp
    rw[mul_comm]; exact e
 have hp:(a.1 b).natAbs ≤ ⌈K*c⌉₊:= by
    have hk: |a.1 b| ≤ ((⌈K*c⌉₊:ℕ):ℤ):=by exact_mod_cast ht
    have hp:= abs_le.mp hk; omega
 have hh:= (cart_spec _ _ _).mp z b; unfold t; simp only [Pi.zero_apply,sub_zero]; omega

lemma chartSat {P:Spine}{b d:ℕ}{k:Axis}{r:ℝ}{p q:List AdmitA}(h:HouseAudit P b r C k d p)(w:q ⊆ p)(v:q.length≤ b):HouseAudit P b r C k d q:=by
 obtain ⟨v',σ,t,b',a,h,r,l,w₂,g⟩:=h; exact ⟨v',σ,t,b',a,h,r,l,v,fun i y=>g _ (w y)⟩
#print axioms chartline
end Heritor
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
