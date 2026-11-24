import YM.SU5.Relativistic.Nickel
/-! # Nonfactor witnesses in aperture arbitrarily small, and cofinal X on one propagation problem.

Here: fixed compact buffered regions, followed ONWARD. Not scaled stochastic UV assumption.
Large observing scale allowed to select different small footprint. Representative
stencils `A,V` then FIXED for all refinements. Uplift need not stay single-link-only.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
open CF.Pannier.Chancel.ScreeV Crest.Sleet Crest.Sleet.UpStart FermionSlab
variable (Λ:Preparation)(l:ℕ)
lemma gaugeFunds : Tendsto (gaugeMesh Λ) atTop (𝓝 0) := by
 let g(s:ℕ):= ((Λ.R.L.val:ℝ)⁻¹)^s; have he:1 < (Λ.R.L.val:ℝ):=by exact_mod_cast (show 1 < Λ.R.L.val from Nat.le_trans (by norm_num) Λ.R.coarse)
 have hp:Tendsto g atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (Λ.R.L.val:ℝ)⁻¹ by positivity) ((inv_lt_one₀ (by positivity)).2 he)
 rw [show gaugeMesh Λ=fun x=>g x/2 from (funext (fun s=> by unfold gaugeMesh g; rw [inv_pow]; ring))]; simpa using (hp.div_const (2:ℝ))
lemma thinning_aperture (V:Finset Cover) (u:ℝ)(p:0<u): ∀ᶠ s:ℕ in atTop, ∀ S⊆ V, footprint Λ l s S⊆ Metric.ball 0 u:=by
 have hv:Tendsto (fun s:ℕ=> (reserve Λ l:ℝ)* gaugeMesh Λ s) atTop (𝓝 0) := by simpa using ((gaugeFunds Λ).const_mul (reserve Λ l:ℝ))
 have hp (x:Cover)(a:Axis):∀ᶠ s in atTop, -u<collarLower Λ l s x a ∧ collarUpper Λ l s x a <u:=by
    have he:Tendsto (fun s=> gaugePosition Λ s x a) atTop (𝓝 0):=by simpa [gaugePosition] using ((gaugeFunds Λ).const_mul (x a:ℝ))
    simp_rw [lower_gauge,upper_gauge]; exact ((he.sub hv).eventually (lt_mem_nhds (by linarith : -u < 0-0))).and ((he.add hv).eventually (gt_mem_nhds (by linarith : (0:ℝ)+0 < u))) -- tune naming
 filter_upwards [(eventually_all_finset V).mpr fun i _=>eventually_all.mpr (hp i)] with s hp S h i g
 obtain ⟨y,o⟩:=Set.mem_iUnion.mp g; obtain ⟨q,v⟩:=Set.mem_iUnion.mp o
 rw [Metric.mem_ball, dist_zero_right,pi_norm_lt_iff p]; intro j; rw [Real.norm_eq_abs,abs_lt]; exact ⟨(hp y (h q) j|>.1).trans_le ((show i ∈ collar Λ l s y from v).1 j), lt_of_le_of_lt ((show i ∈ collar Λ l s y from v).2 j) (hp y (h q) j|>.2)⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction

namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function Set Filter MeasureTheory
open Lattice SU Buffered Afterglow Journey Preparation CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Satin Tapestry Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice
open scoped Topology BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel.ScreeV Tower.Reconstruction Tower.Reconstruction.FermionSlab Crest.Sleet Crest.Sleet.UpStart

-- raw evidence persists to all level marks in CP6 GradesAll. Price remains exactly. keeps common G.
lemma opening (ε η:ℝ)(p:0<η)(D:ℕ)(e:0<D)(U:Supplier):
    ∃ P l Z H Y q d w C a b I E L B T t X G c pan s ζ f f' sample,
     Election ε η U P l Z H Y q d w C a b I E L B T t X G c pan s ζ f f' sample ∧
     ∃ (u:ℕ→ℕ)(K:ℕ→Bool→Buffered.Family (tent Y H)→Buffered.Family (tent Y H)), GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u K∧
      ∃ (d' M i:ℕ) (V:Waxy)(W:Finset ℤ),
       ∀ x> (0:ℝ), ∀ᶠ n:ℕ in atTop,∀ J:Fin 3,∃ (T W':List (XGr M)) (S:Finset Cover)(j:Axis)(Q':Buffered.Family (tent Y H))(z:ℤ),
         T≠[]∧ W'≠[]∧ IsBay (tent Y H) M d' i V J W W' Q' S ∧ FundX Y H X.toExhibition G 0 j c (pan.character sample) n (T:=K) (floorline M i d' T) S (CF.Pannier.Chancel.ScreeV.rolls (Toes M d' i (tent Y H) J) T) Q' (stripeP T.length) z D ∧ footprint P l n (floorline M i d' T) ⊆ Metric.ball 0 x ∧ footprint P l n S ⊆ Metric.ball 0 x :=by
 obtain ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,X,G,c,pan,s,ζ,f,f',sample,h,d',z,Vk,M,D0,F,S,hK,hV⟩:= hopeful U ε η p D
 obtain ⟨u,K,tP⟩:= grades_at Y H X.univ_ G.history
 refine ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,X,G,c,pan,s,ζ,f,f',sample,h,u,K,tP,d',M,Vk,F,S,fun x p=>?_⟩
 let D₀:=loftH M d' Vk D0 F
 filter_upwards [hV, thinning_aperture P l D₀ x p] with n F' q J
 obtain ⟨A,V',S',j,Q',z,p₀,p₁,U,r⟩:=at_this_character Y H X.toExhibition G u tP 0 c (pan.character sample) n J M d' Vk F S hK.front D e (F' 0 (pan.character sample) J) -- c implicit? tune tP order
 have hu (L:List (XGr M)):floorline M Vk d' L⊆D₀:=by intro x h; obtain ⟨i,t,rfl⟩:= Finset.mem_image.mp h; exact (base_stay M d' Vk D0 F i).2
 refine ⟨A,V',S',j,Q',z,p₀,p₁,U,r,q _ (hu A),q _ ?_⟩; cases U with| foot h p=> rw [p]; exact hu _|out h p=>rw [p]; exact via_fur M d' Vk D0 F S hK.capB
end YM.CF.Py.Rate.LocalLimit.Papal
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.opening
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.hopeful
#check YM.CF.Py.Rate.LocalLimit.Papal.opening
#check YM.CF.Buffered.Afterglow.Tower.Reconstruction.at_this_character
#print YM.CF.Buffered.Afterglow.Tower.Reconstruction.FundX
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Staved.shoulders
#check YM.CF.Py.Rate.LocalLimit.Papal.substance
#print axioms YM.CF.Pannier.Chancel.ScreeV.via_lim
