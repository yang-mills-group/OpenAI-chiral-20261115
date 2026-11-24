import YM.SU5.Selected.Rail.Plain
/-! # commute Male & AP AFTER cost choice. synth test coefficients BEFORE law. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder NNReal ENNReal
local notation "I"=>Complex.I
local notation "φ" => 2*π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
open Finset Lat
variable (W:FaceL)(n:ℕ){k:ℕ}
def hood(k:ℕ)(M:Maj)(v:Cover)(x:Bin):ℂ:= prefixG v (harbor x)*carillon k M x 2 0
def hoodF(k:ℕ)(v:Cover)(x:Bin):ℂ:= prefixG v (harbor x)*beat k x 2 0
local notation "w"=> Ε W (n:ℤ)
variable (h:3≤k)
include h
lemma shelter (v:Cover): ∃ f: Coast→ℂ, Continuous f∧∀ x,f (harbor x)= hoodF k v x:=by
 obtain ⟨F,g,p⟩:= keep_F k h; refine ⟨fun x=> prefixG v x*F x 2 0,(prefix_c _).mul (g.matrix_elem _ _), fun x=>?_⟩; apply congrArg (fun t:Op SpinIdx=> prefixG v (harbor x)*t 2 0) (p _)
lemma twist_a: view (hoodF k (w))=keystone k W n:=by
 obtain ⟨f,p,he⟩:= shelter h (w); have h(t: Facet3×ℝ): hoodF k (w) (joinBin t)= f (harbor (joinBin t)):= (he _).symm; have hp: Integrable (hoodF k (w) ∘ joinBin) ferry4:=by
    rw [show (hoodF k (w) ∘ joinBin)= _ from funext h]; exact cp_c f p -- name shelter params tune
 have ht(t:Facet3)(x:ℝ): hoodF k (w) (joinBin (t,x))=grappa W t*aroma k n t x:= by unfold grappa aroma hoodF joinBin; rw [harbor_join,tintMono,soldier,Int.cast_natCast]; ring
 change (∫ x,(hoodF k (w) ∘ joinBin) x ∂ferry4)=_; rw [ferry4,integral_prod (hoodF k (w) ∘ joinBin) hp]; unfold keystone hammer; simp_rw [Function.comp,ht,integral_const_mul,econ] -- rw orientation trouble
abbrev mounts:= mtn ×ˢ (atTop: Filter Side)
theorem limit_song: Tendsto (fun i: Maj×Side=> packA i.2 (hood k i.1 (w) ∘ pm)) mounts (𝓝 ((↑rent':ℂ)⁻¹ * keystone k W n)):=by
 apply Metric.tendsto_nhds.mpr; intro ε p; obtain ⟨F,z,e⟩:=shelter h (w); have hg:0<ε/3:=by positivity
 have hF: perch F=(↑rent':ℂ)⁻¹ * keystone k W n:=by unfold perch; rw [show F ∘ harbor= hoodF k (w) from funext e,twist_a W n h]
 have he:= Metric.tendstoUniformlyOn_iff.mp (beating_compact h) (ε/3) hg; rw [← hF]; filter_upwards [(show Tendsto Prod.fst mounts mtn from tendsto_fst).eventually he,(show Tendsto Prod.snd mounts atTop from tendsto_snd).eventually (Metric.tendsto_nhds.mp (cost_grid z) _ hg)] with i h v; apply lt_of_le_of_lt (dist_triangle _ (AP i.2 F) _); apply lt_of_le_of_lt (add_le_add ?_ (show dist (AP i.2 F) (perch F)<_ from v).le) (by linarith : ε/3+ε/3<ε)
 rw [dist_eq_norm,AP, ←pack_sub]; apply pack_cost; intro j; rw [Pi.sub_apply,Function.comp_apply,Function.comp_apply, ←cargo_coe,e, hood, hoodF,←mul_sub,norm_mul,prefix_norm,one_mul,←Matrix.sub_apply]; apply (norm_entry ..).trans; rw [norm_sub_rev,←dist_eq_norm]; exact (h _ (stem_one j)).le -- orientation tune
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms limit_song
#print axioms twist_a
#check @shelter
