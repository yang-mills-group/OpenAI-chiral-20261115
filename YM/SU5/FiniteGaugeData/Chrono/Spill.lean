import YM.SU5.FiniteGaugeData.Chrono.Scaler
import Mathlib.Analysis.InnerProductSpace.Positive
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
namespace Chrono
open Nacre Heat Charm Playlist Show
variable (R:Universal Y h u v I E)(L:Rolled Y h u v J P)(a j:Axis)
local notation "η"=> reserve Λ l
variable (A:Repertory Y h R L a) (x:Decko Y h a)(w:Vect Y h a 0)
local notation "G" i:max=> store Y h i R L a A
local notation "V"=> Vect Y h a 0
local notation "H"=> A.space
variable (z:ℤ)(p:j=a→0≤z)
@[simp] lemma scalaZero : scaleR Λ s i 0=0:=mul_zero _
lemma scale_same : scaleR Λ s s z=z:=by unfold scaleR; rw [Nat.sub_self,pow_zero,one_mul]
lemma scale_trans (u:s ≤ i)(t:i ≤ k) : scaleR Λ s k z=scaleR Λ i k (scaleR Λ s i z):=by unfold scaleR; rw [show k-s=k-i+(i-s) from by omega,pow_add,mul_assoc]
local notation "ρ" i:max=> scaleR Λ s i z
local notation "T"=> tock Y h s R L a j A
local notation "P'"=> tock Y h i R L a j A
local notation "U"=> (T) z p
lemma cohere_clock (p0:s ≤ i)(t':j=a→0≤ scaleR Λ s i z): tock Y h s R L a j A z p = (P') (scaleR Λ s i z) t':=by
 apply lens_ext Y h i R L a A; intro k t w; rw [earn_seed Y h s k R L a j A w z p (p0.trans t),earn_seed Y h i k R L a j A w (ρ i) t' t]; apply congrArg ((G k)); apply Subtype.ext; rw [hoist_val,hoist_val,scale_trans _ _ _ _ p0 t]
lemma clock_own : (U) ((G s) x)=(G s) (hoist Y h a j z p x):=by
 rw [earn_seed _ _ _ _ R L a j A x z p le_rfl]; apply congrArg ((G s)); apply Subtype.ext; rw [hoist_val,hoist_val,scale_same]
lemma tock_zero : (T) 0 (fun _=>le_rfl)=1:=by
 apply lens_ext Y h s R L a A; intro k t x; rw [earn_seed _ _ _ _ R L a j A _ _ _ t]; have hx (p:j=a→0≤ scaleR Λ s k 0) : hoist Y h a j (scaleR Λ s k 0) p x=x:= Subtype.ext (by rw [hoist_val,scalaZero, tic_zero]); rw [hx]; rfl
lemma tock_plus (z' zp:ℤ)(e:j=a→0≤z')(q:j=a→0≤zp)(b:z+z'=zp): (U)*(T) z' e=(T) zp q:=by
 apply lens_ext Y h s R L a A; intro k t y; change (U) (((T) z' e) ((G k) y))=_; rw [earn_seed _ _ _ k R L a j A _ z' e t, earn_seed _ _ _ _ R L a j A _ z p t,earn_seed _ _ _ _ R L a j A _ zp q t,hoist_sum _ _ a j y _ _ _ (scaleR Λ s k zp) _ _ (show _ = scaleR Λ s k zp from by unfold scaleR; rw [← mul_add,b])]
lemma tock_free (a':Axis)(t:ℤ)(e:a'=a→0≤t): Commute (U) (tock Y h i R L a a' A t e):=by
 apply lens_ext Y h (max s i) R L a A; intro k p' v; obtain ⟨l,r⟩:= max_le_iff.mp p'; simp_rw [ContinuousLinearMap.mul_apply]; rw [earn_seed _ _ i k R L a a' A _ t e r, earn_seed _ _ s _ R L a j A _ z p l, earn_seed _ _ s k R L a j A _ z p l, earn_seed _ _ i _ R L a a' A _ t e r, hoist_cross]
lemma tock_preserve (q:j≠a)(v:A.space): ‖(U) v‖= ‖v‖:=by
 refine A.issued.induction ?_ (isClosed_eq ((U).continuous.norm) continuous_norm) v; rintro v ⟨w,rfl⟩; obtain ⟨k,t,u⟩:= ((eventually_ge_atTop s).and (eventual_table Y h R L a A w)).exists
 dsimp only at u; rw [←u,earn_seed _ _ _ k R L a j A _ z p t]; exact space_safe Y h k R L a j A _ (scaleR Λ s k z) _ q
-- Positive. Proof right = via plane halfway. price becomes PC selfadj. Complex.
lemma disperses (b:0≤z): 0 ≤ inner ℂ ((G s) x) ((G s) (hoist Y h a a z (fun _=> b) x)):=by
 rw [lawStore]; let y:= clockW Kₜ a z x.val; let g:= Heat.gaugeShift (Kₜ).B z
 have ht: fire Kₜ a g y=fire Kₜ a 0 x.val:= burning_ice ..
 rw [helve,hoist_val, ← ht]
 have hv: Canaan Y h a y g:= Canaan.subh Y h a _ (show g≤_ from ?_) (Canaan.flight Y h a x.val z x.property)
 swap
 · rw [← tick_tock]; have he:0 ≤ g:= by unfold g gaugeShift; positivity
   change g≤ 0+2*g; linarith
 obtain ⟨S,t,V₀⟩:=hv; exact ahead_positive Y h S s R a z y.val V₀ t
section
variable {T':Hilbert} {F : T'.Op}
lemma paidpositive (p:∀ x:T',0≤ inner ℂ x (F x)): ContinuousLinearMap.IsPositive F:= by
 apply (ContinuousLinearMap.isPositive_iff_complex F).mpr; intro x; have ht: 0 ≤ inner ℂ (F x) x:= by rw [← inner_conj_symm]; exact star_nonneg_iff.mpr (p x)
 exact ⟨Complex.ext rfl (Complex.le_def.mp ht).2, (Complex.le_def.mp ht).1⟩
end
lemma tock_positive (q:0≤z): ContinuousLinearMap.IsPositive (tock Y h s R L a a A z (fun _=> q)):=by
 let U':= tock Y h s R L a a A z (fun _=> q); apply paidpositive; intro v; refine A.issued.induction ?_ (isClosed_le (g:=fun x:A.space=>inner ℂ x (U' x)) continuous_const (continuous_id.inner U'.continuous)) v
 rintro v ⟨w,rfl⟩; obtain ⟨k,g,v⟩:= ((eventual_table Y h R L a A w).and (eventually_ge_atTop s)).exists
 dsimp only at g; rw [←g,earn_seed _ _ _ k R L a a A _ z _ v]; exact disperses Y h k R L a A _ (scaleR Λ s k z) (mul_nonneg (by positivity) q)

lemma nectar_beyond {z:ℤ}(p:0≤z)(V₀:Canaan Y h a x.val z): Canaan Y h a (nectar Y h s R L a x).val (z+1) := Canaan.next Y h s R L a x.val p V₀
-- Dense images from positive delays. Actually each store rep belongs.
lemma already (n:ℕ): ∃ y:Decko Y h a, Canaan Y h a y.val n ∧ (G (s+n)) y=(G s) x:=by
 induction n with
 | zero=> exact ⟨x, by rw [Nat.cast_zero]; exact x.property, rfl⟩
 | succ n ih=>
    obtain ⟨y,u,b⟩:=ih; exact ⟨nectar Y h (s+n) R L a y,by rw [Nat.cast_succ]; exact nectar_beyond Y h _ R L a y (Nat.cast_nonneg' _) u,(for_next Y h (s+n) R L a A y).trans b⟩
lemma anticipates : ∃ y:A.space, (tock Y h (s+tic Kₜ) R L a a A 1 (fun _=>zero_le_one)) y=(G s) x:=by
 let n:=tic Kₜ; obtain ⟨y,p,q⟩:=already Y h s R L a A x n; let g:=clockW Kₜ a (-1) y.val
 have he:Canaan Y h a g 0:= by have hv:= Canaan.flight Y h a _ (-1) p; change Canaan Y h a g ((n:ℤ)+n*(-1:ℤ)) at hv; simp_all
 let v:Decko Y h a:= ⟨g,he⟩; refine ⟨(G (s+n)) v, ?_⟩; rw [clock_own,show hoist Y h a a 1 (fun _=> (zero_le_one : (0:ℤ) ≤ 1)) v = y from Subtype.ext (by rw [hoist_val, show v.val = clockW Kₜ a (-1) y.val from rfl, clock_add, add_neg_cancel,tic_zero]) ]; exact q -- replace

#print axioms tock_plus
#print axioms anticipates
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
