import YM.SU5.Registration.Affine.Borrow
/-!
# Learn a common field price from multiple stamp allocations

`Scoria` buys a convex mantle on top of a thermally-bounded approximation.
Can compute portraits even with height-dependent ballots (not claiming any
parameter recovered from the ballots themselves). Use this for all the γ
at the moment orientation and sensor. Pay epsilon at fixed positive pad,
then thickness limit. Keeps the SAME field correspondence on the main character.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinRegistration
open Filter Function Topology SatinNucleus Finset
open scoped Classical InnerProductSpace NNReal ENNReal Matrix.Norms.L2Operator
section voters
variable (A:Coalition) {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
noncomputable def offer (X:ℕ→E): E:= ∑ i∈ A.voters,(↑(A.w i):ℂ) • X i
lemma offer_budget (X:ℕ→E)(ε:ℝ)(h:∀ i∈ A.voters,‖X i‖≤ε) : ‖offer A X‖≤ε:=by
 unfold offer; apply (norm_sum_le ..).trans
 refine (sum_le_sum (g:=fun i=>A.w i*ε) ?_).trans_eq ?_
 · intro i p; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (A.signed i p)]; exact mul_le_mul_of_nonneg_left (h i p) (A.signed i p)
 rw [←sum_mul,A.pledges,one_mul]
lemma offer_one (x:E) : offer A (fun _=>x)=x:=by unfold offer; rw [←sum_smul,←Complex.ofReal_sum,A.pledges,Complex.ofReal_one,one_smul]
lemma offer_difference (X Y:ℕ→E): offer A (X-Y)= offer A X-offer A Y:=by unfold offer; simp only [Pi.sub_apply,smul_sub,sum_sub_distrib]
lemma offer_hears (X:ℕ→E)(x:E)(ε:ℝ)(h:∀ i∈ A.voters,dist (X i) x≤ ε) : dist (offer A X) x≤ ε:=by
 let Y:=fun _ :ℕ=>x; rw [dist_eq_norm, show offer A X - x=offer A (X-Y) from (by rw [offer_difference,offer_one])]; exact offer_budget A _ _ fun i v=> ((dist_eq_norm (X i) x).symm.trans_le (h i v))
variable (v:ℕ→ Coalition)
omit A
lemma offer_learns (X:ℕ→E)(x:E)(p:Tendsto X atTop (𝓝 x)): Tendsto (fun i=>offer (v i) fun k=> X (i+k)) atTop (𝓝 x):=by
 apply Metric.tendsto_nhds.mpr; intro e h
 obtain ⟨n,h'⟩:= eventually_atTop.mp (Metric.tendsto_nhds.mp p _ (half_pos h)); -- ⟩' invalid
 filter_upwards [eventually_ge_atTop n] with i hp; exact (offer_hears (v i) _ _ _ (fun j v=> (h' (i+j) (by omega)).le)).trans_lt (half_lt_self h)
lemma Flying.offer_learns (H:Hilbert)(X:ℕ→ H.Op)(B:H.Op)(p:Flying X B): Flying (fun i=>offer (v i) fun k=> X (i+k)) B:=by
 intro x; refine ⟨(_root_.YM.SatinRegistration.offer_learns v _ _ (p x).1).congr ?_, (_root_.YM.SatinRegistration.offer_learns v _ _ (p x).2).congr ?_⟩ <;> intro i <;> unfold offer
 · rw [_root_.sum_apply]; rfl
 rw [map_sum,_root_.sum_apply]; refine sum_congr rfl fun k h=>?_ ; rw [ContinuousLinearMap.adjoint.map_smulₛₗ]; simp
variable (V: Type*) [NormedRing V][NormedAlgebra ℂ V] {I:Type*}[DecidableEq I](L:List I)(q:L.Nodup)
-- product of independent convex ballots. test optional custom price and outer factor C. List.Nodup on labels. Assume *all* indices valid. cone. proof parameter.
include q
lemma taught (K:I→ Coalition)(Q:I→ ℕ→ V)(ψ: V →ₗ[ℂ] E)(x:E)(r:ℝ)(p:∀ σ:I→ℕ,dist (ψ (L.map fun i=> Q i (σ i)).prod) x≤r) : dist (ψ (L.map fun i=>offer (K i) (Q i)).prod) x ≤ r:=by
 induction L generalizing ψ with
 | nil=> exact p fun _=>0
 | cons i l ih=>
    let Y(i:I):V:= offer (K i) (Q i); let B:=(l.map Y).prod; have he: ψ (Y i*B)=offer (K i) (fun k=> ψ (Q i k*B)):=by unfold Y offer; rw [sum_mul,map_sum]; exact sum_congr rfl fun k h=>by rw [Algebra.smul_mul_assoc,map_smul]
    obtain ⟨u,k⟩:= List.nodup_cons.mp q
    change dist (ψ (Y i *B)) x ≤ r; rw [he]; apply offer_hears; intro k' y
    let M:=Q i k'; let A':= ψ.comp (Algebra.lmul ℂ V M)
    refine ih k A' fun σ=>?_ ; let σ':= Function.update σ i k'; have hh(i':I)(t:i'∈l):σ' i'=σ i':=Function.update_of_ne (fun (h:i'=i)=> u (h ▸ t)) ..; have ht:σ' i=k':= Function.update_self ..
    have hv:(l.map fun i'=> Q i' (σ i'))=(l.map fun i'=> Q i' (σ' i')):=List.map_congr_left (fun i p=> congrArg _ (hh i p).symm) -- name
    change dist (ψ (Q i k' * ((l.map fun j=>Q j (σ j)).prod))) x ≤ r; have h':= p σ'; simp only [List.map_cons,List.prod_cons,←hv,ht] at h'; exact h'
end voters
end YM.SatinRegistration
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
/- ## Over our phase
 Assuming symmetric price all spectra (after that same height selection with `P`).
 Then any $γ$ moment computed, with real projection. Use `Mantled` and ask
 only from underlying all-γ thermal entries of that one program.
-/
variable {I:Type*}
variable (A B:P.Swatch)(v:ℕ→ Coalition)
local notation "Z" s:max t:max k:max x:max=> offer (v k) fun u=> B.Wstage x a s t (k+u) -- notation parser maybe `Z` collides Stage. Use.
structure Mantle : Prop where
 finishes : A.Finishes
 goes : ∀ t:ℝ≥0,0<t→∀ᶠ k in atTop,∀ x:P.Spectrum0 3, A.Wstage x a t t k=Z t t k x
variable (m:Mantle P a A B v)
include m
lemma mantle_threshold (u:P.ThresholdPrice a B) : P.ThresholdPrice a A:=by
 intro t z; obtain ⟨C,h,U⟩:= u t z; obtain ⟨n,h'⟩:=eventually_atTop.mp U
 refine ⟨C,h,?_⟩; filter_upwards [m.goes t z,eventually_ge_atTop n] with k p t' x; rw [p x]; exact offer_budget _ _ _ fun i _=> h' (k+i) (by omega) x
lemma Mantle.card (t:B.WPermit x a) : A.WPermit x a:= by
 refine ⟨m.finishes,?_,fun s u=>?_⟩
 · obtain ⟨k,C',h,s⟩:= t.budget; refine ⟨k,C',h,fun t' e f=>?_⟩
   let d:=(t':ℝ)^k; have hd:0<d:= pow_pos (show 0<(t':ℝ) from e) _
   obtain ⟨n,z⟩:= eventually_atTop.mp (s t' e f)
   filter_upwards [m.goes t' e,eventually_ge_atTop n] with i p h; rw [p x,mul_comm,←le_div_iff₀ hd]; exact offer_budget _ _ _ (fun i' h'=> (le_div_iff₀ hd).2 ((mul_comm _ d).le.trans (z (i+i') (by omega))))
 exact (Flying.late (Flying.offer_learns v (P.ManyF a (P.advocate 3 x a)) _ _ (t.arriving _ u)) ((m.goes _ u).mono fun i t=> (t x).symm)).Cauchy -- name dot? 
lemma mantle_keeps (t:B.WPermit x a) (p:A.WPermit x a): p.atHeat=t.atHeat:=by
 funext s; by_cases u:0<s; refine (p.arriving s u).unique (Flying.late (Flying.offer_learns v (P.ManyF a (P.advocate 3 x a)) _ _ (t.arriving _ u)) ((m.goes s u).mono fun i p=> (p x).symm)); simp [WPermit.atHeat, Delivery.accepts, u]
lemma heat_offer (t:ℝ≥0) (h:0<t)(p₀:B.Finishes): ∀ᶠ k in atTop,∀ x:P.Spectrum0 3,∀ b q:ℝ≥0,t ≤ b → t ≤ q → A.Wstage x a b q k= Z b q k x := by
 obtain ⟨n,hN⟩:= eventually_atTop.mp ((p₀ a).eventually (ge_mem_nhds h)); filter_upwards [eventually_ge_atTop n,(m.finishes a).eventually (ge_mem_nhds h),m.goes t h] with i p h w x b q f g
 rw [A.Wstage_more x a i h f h g,w x]; unfold SatinRegistration.offer; rw [Finset.mul_sum,Finset.sum_mul]; refine sum_congr rfl fun i' o=>?_ ; have hx:(B.fieldA (i+i')).allowance P a ≤ t:= hN (i+i') (by omega)
 dsimp only; rw [B.Wstage_more x a (i+i') hx f hx g, Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma mantle_scope {p:Vantage}(r s:ℝ)(b:r<p a)(c:p a<s)(q:ℕ→Vantage)(h:Tendsto q atTop (𝓝 p))(σ:ℕ→ℕ)(u:Tendsto σ atTop atTop) (p₀:B.Finishes): ∀ᶠ i in atTop,∀ x:P.Spectrum0 3, A.scoop P x a r s (q i) (σ i) = offer (v (σ i)) (fun k=>B.scoop P x a r s (q i) (σ i+k)):=by
 obtain ⟨t,h',u',v'⟩:=clock_enough r s (p a) b c
 have hp:=tendsto_pi_nhds.mp h a
 filter_upwards [u.eventually (P.heat_offer a A B v m t h' p₀), (hp.sub_const r).eventually (le_mem_nhds u'), ((tendsto_const_nhds (x:=s)).sub hp).eventually (le_mem_nhds v')] with i x a₀ b₀ X₀
 let D:=Real.toNNReal (q i a-r); let U:=Real.toNNReal (s-q i a); have hl:r≤ q i a:=sub_nonneg.mp (t.prop.trans (show (t:ℝ) ≤ q i a-r from a₀)); have hv:q i a ≤ s:= sub_nonneg.mp (t.prop.trans (show (t:ℝ)≤ s- q i a from b₀))
 rw [A.scoop_reads P X₀ a r s (q i) (σ i) hl hv]; unfold SatinRegistration.offer; simp_rw [B.scoop_reads P X₀ a r s (q i) _ hl hv]; rw [x X₀ D U (NNReal.le_toNNReal_of_coe_le a₀) (NNReal.le_toNNReal_of_coe_le b₀)]; unfold SatinRegistration.offer cane; rw [Finset.mul_sum,Finset.sum_mul]; exact sum_congr rfl fun k h=>by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc] -- rw x may syntactic match D U stuck.
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
