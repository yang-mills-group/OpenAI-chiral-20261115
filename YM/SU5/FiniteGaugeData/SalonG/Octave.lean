import YM.SU5.FiniteGaugeData.SalonG.Operator
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
namespace SalonG
open Nacre Heat Charm Chrono Journey
variable (a:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
local notation "D"=> Decko Y h a
local notation "X"=> (A.space:Type)
local notation "M" t:max=> store Y h t W' R a A
local notation "π"=>nectar Y h s W' R a
local notation "N" n:max=> energyS Λ d n
variable {f x:W (tent Y h)}(z:Plan Y h a d f)(y:Decko Y h a)(q:0<d)
local notation "Θ"=> appointed Y h s a d
local notation "Ω" z:max n:max => appointed Y h s a d n W' R z
local notation "H" n:max=> warmV Y h a (energyS Λ d n)
-- warmed lifts prescribed at a domain independent of phase.Section names.Pay θX positive. Tangle transl.Analyt efforts
lemma warmer : tock Y h s W' R a a A (d*(0+2):ℕ) (fun _=>Nat.cast_nonneg' _) ((M (s+n)) y)= store Y h (s+n) W' R a A (warmV Y h a (energyS Λ d n) y):= by
 have he:= earn_seed Y h s (s+n) W' R a a A y (d*(0+2):ℕ) (fun _=>Nat.cast_nonneg' _) (by omega); rw [he]; apply congrArg ((M (s+n))); apply Subtype.ext; unfold warmV; rw [hoist_val,hoist_val]; unfold energyS Chrono.scaleR; push_cast; simp; ring_nf -- tune
local notation "F"=> tock Y h s W' R a a A (d*(0+2):ℕ) (fun _=>Nat.cast_nonneg' _)
lemma warmed_dense : DenseRange (fun w:Playlist.Show.Vect Y h a 0=>tock Y h s W' R a a A (d*(0+2):ℕ) (fun _=>Nat.cast_nonneg' _) (A.paid w)):=by
 have hx:F=rail Y h W' R a A (thetaX Λ s (d*(0+2))):=(rail_actual ..).symm; have t:DenseRange (F):= hx.symm ▸ denseRail Y h W' R a A _; exact t.comp A.issued ((F).continuous)
lemma warm_lift (P₁:X→ Prop)(p:IsClosed {x|P₁ x})(h:∀ i:ℕ,n ≤ i → ∀ y:Decko Y _ a,P₁ (store Y _ (s+i) W' R a A (warmV Y _ a (energyS Λ d i) y))) : ∀ (x:X),P₁ x:=by
 intro x; refine (warmed_dense Y _ s a d W' R A).induction (P:=P₁) ?_ p x; rintro x ⟨w,rfl⟩; obtain ⟨t',v,q⟩:= ((eventual_table Y _ W' R a A w).and (eventually_ge_atTop (s+n))).exists; obtain ⟨i,t,rfl⟩: ∃ i, n ≤ i ∧ t'=s+i:=⟨t'-s,by omega,by omega⟩; dsimp only at v ⊢; rw [←v]; -- q shadow, unfold
 rw [warmer]; exact h i t _

-- export auxiliary comparable bound criterion from gallery of mate
include A z q
lemma weight (p:Gallery Y h s a d u v (mateW Kₜ a d f)): ‖store Y h (s+n) W' R a A (appointed Y h s a d n W' R z y)‖ ≤ ‖store Y h (s+n) W' R a A y‖:= by
 let z':= Plan.other Y h z
 let x:= (M (s+n)) (appointed Y h s a d n W' R z y); let b:= ‖(M (s+n)) y‖
 -- enough that mate satisfies warm bound. by invariance.
  -- valued for ANY positive.A.No argument
 have he(i:ℕ)(v:n ≤ i):∃ u:D, (M (s+i)) u=(M (s+n)) y∧ (M (s+i)) ((Ω z i) u)= x:=by
    induction i,v using Nat.le_induction with
    | base=> exact ⟨y,rfl,rfl⟩
    | succ i _ ih=> obtain ⟨u,v,t⟩:=ih; refine ⟨nectar Y h (s+i) W' R a u,(for_next Y h (s+i) W' R a A u).trans v,?_⟩; rw [← appoint_next]; exact (for_next Y h (s+i) W' R a A _).trans t
 have hv(i:X):‖inner ℂ i x‖ ≤ ‖i‖*b:=by
    apply warm_lift Y h s a d n W' R A (fun i:X=>‖inner ℂ i x‖ ≤ ‖i‖*b) (isClosed_le (by fun_prop) (by fun_prop)) _ i
    intro i e' t; obtain ⟨u,v,V'⟩:= he i e'; rw [← V',ice_bend Y h s a d i W' R A (warmV Y h a (energyS Λ d i) t) u z]; unfold b; rw [←v]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right (valued Y h s a d i W' R A t z' q p) (norm_nonneg _))
 have ht:= hv x; rcases (norm_nonneg x).eq_or_lt with r|r; · change ‖x‖ ≤ _; rw [←r]; exact norm_nonneg _
 rw [inner_self_eq_norm_sq_to_K] at ht; change ‖(↑‖x‖:ℂ)^2‖ ≤ ‖x‖ * _ at ht; rw [←Complex.ofReal_pow,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _),sq] at ht; exact le_of_mul_le_mul_left ht r

#print axioms weight
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
