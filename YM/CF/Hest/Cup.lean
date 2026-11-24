import YM.CF.Hest.Poet
import YM.CF.Hest.Vera
import YM.CF.Hest.Gust
import YM.CF.Hest.Foy
import YM.CF.Hest.Hull
import YM.CF.Facet.Prima
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 25000
noncomputable section
namespace YM.CF.Hest
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory Urn Levier Cour Facet
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N P m X B L:Side}{n k j:ℕ}{e d t x u C A:ℝ}
open Newt Hors Souk
open RG Pressure Push AnalyticBridge.LocalGaussianLaws
local notation "GG"=>group
variable{T:Roam m X B}{c b a r w σ:ℝ}
variable{G:Ratio (CSide m B) (CSide X B)}{A:Haze m X B G e}{n:ℕ}{k':T.Choices}{U:nomA m X B→ Op (Single (CSide m B))}
section
open Arena
lemma snick (f:Ind G A a b C n U)(t:0<e)(P:Forest T.ratio)(h:Fleck G t P r C n)(M: Finset (mSeal X B))(j:ℕ)(x y:Single (CSide m B))(hv:0 < a)(hq:∀ i∈M,j ≤ i.card)(i: Snap P)(he:‖i‖<r): Jet.Allows n (fun k=> ∑ u∈M,A u (frameT G t P k) x y) i (Real.exp (-a*j)*b):=by
 obtain ⟨W,Z,p⟩:=f.port; apply Jet.Allows.mono; refine Jet.allows_sum (s:=M) (f:=fun u k=> A u (frameT G t P k) x y) (fun u F=> (Z u).folk x y _ (ball 0 r) isOpen_ball _ h.mark _ (mem_ball_zero_iff.mpr he))
 let c:=Real.exp (-a*j); have ht:0 ≤ c:=(Real.exp_pos _).le; have hw:saleM a W x y ≤ b:=(single_le_sum (fun i (_:i∈(univ:Finset _))=> sale_nn (fun i=>(Z i).pos) a x i) (mem_univ y)).trans (p.rows x)
 apply le_trans _ (mul_le_mul_of_nonneg_left hw ht); unfold saleM; rw [Finset.mul_sum]; apply le_trans (b:=∑ u∈M, Real.exp (-a*j)*(Branch.rent a u*W u x y)) _ (sum_le_sum_of_subset_of_nonneg (subset_univ M) (fun i _ _=>mul_nonneg ht (mul_nonneg (rent_pos ..|>.le) ((Z i).pos ..))))
 apply sum_le_sum; intro u z; rw [←mul_assoc]; exact le_mul_of_one_le_left ((Z u).pos ..) (by unfold Branch.rent; rw [← Real.exp_add]; apply Real.one_le_exp; push_cast; have hp: (j:ℝ) ≤ u.card:=by exact_mod_cast hq _ z
                                                                                              linarith only [mul_le_mul_of_nonneg_left hp hv.le]) -- tune
variable{F':Forest T.ratio}{H:Tube GG T}{w' : Odd L.val}{P': Aim (CSide m B)}{J':Aim (CSide X B)}{D:Male}{Q:Pricing j L w' (Thread j)}{t': Vox m B→ AxisChart GG F'}
lemma voss (d:ℝ)(h:0<e)(I:Ind G A a b C n (Budget L w' J'.den P'.den G D j))(he: ContDiffAt ℝ (↑(2:ℕ)) (fun u=> ∑ S,A S (frameT G h F' (flute F' (Uniform.station t') d u))) 0)
 (hq:Fleck G h F' r C n)(hw: ∀ᶠ u in 𝓝 0, ‖flute F' (Uniform.station t') d u‖<r)(ht:0<d)(hp:cFoot 3 (emergence L j w' G F' t' D J'.den-flareP L j w' D P'.den)) : cFoot 3 (fun u=>∑ S,A S (frameT G h F' (flute F' (Uniform.station t') d u))):=by
 let V:= emergence L j w' G F' t' D J'.den-flareP L j w' D P'.den; let f(u):=∑ S,A S (frameT G h F' (flute F' (Uniform.station t') d u)); let Lx: Mast GG (More (CSide m B)) ≃L[ℝ] Vox m B:= (ContinuousLinearEquiv.smulLeft (Units.mk0 d ht.ne')).trans (Uniform.tint group _)
 have hV : f=ᶠ[𝓝 0] V∘ Lx:=by
    filter_upwards [hw] with i hi; unfold f; rw [I.meet]; unfold frameT; rw [Pec.pear_even G h (hq.onP _ hi)]; dsimp only; unfold flute; rw [wellPath]; rfl
 have ht:ContDiffAt ℝ (↑(2:ℕ)) V (Lx 0):=by
    have hh' := he.congr_of_eventuallyEq (f:=f) hV.symm; let H:=V∘ Lx; rw [map_zero,show V= H ∘ Lx.symm from funext fun i=>(congrArg V (Lx.apply_symm_apply i)).symm]; apply ContDiffAt.comp; rw [show Lx.symm 0=0 from map_zero _]; exact hh'; exact Lx.symm.contDiff.contDiffAt
 intro k hk; unfold V at *; change iteratedFDeriv ℝ k f 0=0; rw [(hV.iteratedFDeriv ℝ k).eq_of_nhds]; change iteratedFDeriv ℝ k ((_ - _) ∘ Lx.toContinuousLinearMap) _= _; rw [Uniform.iter_lin_at (L:= Lx.toContinuousLinearMap) (ht.of_le (by exact_mod_cast (show k ≤2 by omega) : (↑k:ℕ∞ω) ≤ ↑(2:ℕ))),map_zero,hp k hk]; ext; rfl -- tune
end
end YM.CF.Hest
