import YM.SU5.FiniteGaugeData.CodaT.Sentire
import YM.SU5.FiniteGaugeData.CodaT.SummitB
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Hills
variable (h:Real.exp 1≤Λ.x) (s i k:ℕ) {S:Finset Cover}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ} (K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
local notation "Kₜ"=> tent Y h
variable (D:Desire (tent Y h) S)
local notation "Ψ" s:max i:max => side Y i s   -- swapped!
local notation "Φx" s:max i:max k:max=> ((Y.voyage i).X (Y.uv k)).gram s
local notation "Θx"=> tickA (Ψ s i)
local notation "Φψ" s:max i:max k:max=> D.slope (tent Y h) Λ.K.j (Ψ s i) (((Y.voyage i).X (Y.uv k)).gram s).J.M
local notation "ΦH"=> 45 * Real.sqrt (MajorH Λ)
local notation "N"=> Ψ s i
variable {n m d:ℕ}{p C Y0 r t b u' e E':ℝ}{U:Op (Single (side Y i s))}
variable (S':RadioCity.Hypothesis Λ l g Y)
set_option maxHeartbeats 730000
open Niagara Chisel Stationary
open PolarF
abbrev positionZ(Z:Finset Cover)(k:ℕ):ℝ:= (radiusN Z:ℝ)/(tic (tent Y h):ℝ)/((tassel Λ k):ℝ)
private lemma beaming (Z:Finset Cover):Tendsto (positionZ Y h Z) atTop (𝓝 0):= by
 apply Tendsto.const_div_atTop; let L:=Λ.R.L; apply Tendsto.comp (g:=fun x:ℕ=>(x:ℝ)) tendsto_natCast_atTop_atTop; apply StrictMono.tendsto_atTop; apply strictMono_nat_of_lt_succ; intro i; change L.val^i < L.val^(i+1); have hp:=pow_pos L.property i; have hQ:L.val≥4:=Λ.V.tallX; rw [pow_succ]; exact (Nat.mul_one (L.val^i)).symm.trans_lt (Nat.mul_lt_mul_of_pos_left (show 1<L.val by omega) hp)
private lemma scaleE (p:0<r) (β:ℝ) (z w:ℂ)(H:‖z-w‖ ≤ 1/ (r*r^3)): ‖(r:ℂ)^3*z-(r:ℂ)^3*w‖≤1/r:=by
 rw [←mul_sub,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg p.le]; exact (mul_le_mul_of_nonneg_left H (pow_nonneg p.le _)).trans_eq (by field_simp)
local notation "ΨR"=>ℕ→ W (tent Y h)→ₗ[ℂ]ℂ
local notation "pays" Φ:max=>Hills.Sphere Y h K R A Φ
include S' K R A
private lemma guideB (x:ℝ)(p:0<x)(A':Chisel):∃ i:ℕ,∀ k:ℕ,i≤k → positionZ Y h A'.town k ≤1/x ∧ ∀ Φ:ΨR, Hills.Sphere Y h K R A Φ → ‖(x:ℂ)^3*Φ k ((A'.DesireB Kₜ).paid)-(x:ℂ)^3*yD A'‖ ≤1/x:=by
 let k:=1/(x*x^3); have he:= invocation Y h K R A S' A' (show 0 < k from one_div_pos.mpr (by positivity))
 refine eventually_atTop.mp (((beaming Y h A'.town).eventually (ge_mem_nhds (one_div_pos.mpr p))).and (he.mono fun i t Φ V=> scaleE p 0 _ _ (t Φ V)))
variable (X:ℕ→ Niagara.Chisel){U V:SpinIdx}{f_:Window.Family}{tN:ℕ→ℝ}{o:Gaia}
-- ψ size continuity not assumed. Q Y on actual Course. Scaling BOUGHT after rod schedule, not uniform in such. use deadline.Per.Function.Exists uniform in state even varying by level as shown.
theorem whirr (p:o≠0)(h0:Tendsto tN atTop atTop)(e:∀ i:ℕ, 0<tN i)(ω: Tendsto (fun i=>Onyx.riseX (tN i) (spanD (X i))) atTop (𝓝 o))(hU:∀ i:ℕ,(X i).u=U)(hV:∀ i:ℕ,(X i).d=V)(hX:∀ i:ℕ,(X i).σ=f_): ∃ z:ℕ→ℕ,Tendsto z atTop atTop ∧ ∀ y: ℕ→ℕ, z≤y →
     Tendsto (fun i=>positionZ Y h (X i).town (y i)) atTop (𝓝 0) ∧
     ∀ (Φ:ℕ→ ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), (∀ i:ℕ, Hills.Sphere Y h K R A (Φ i))→ Tendsto (fun i:ℕ => ((tN i:ℝ):ℂ)^3*(Φ i (y i) (((X i).DesireB (tent Y h)).paid))) atTop (𝓝 ((Window.dimf f_:ℂ)*(Onyx.pencil o) V U)):=by
 choose i v using fun i:ℕ=>guideB Y h K R A S' (tN i) (e i) (X i)
 let z(j:ℕ):=max j (i j); refine ⟨z,tendsto_atTop_mono (fun i=>le_max_left i _) tendsto_id, fun y t=>?_⟩
 let V'k:ℕ→ℂ:= fun i=> ((tN i:ℝ):ℂ)^3*yD (X i)
 let ℓ:= (dimf f_:ℂ)*(Onyx.pencil o) V U; have hp:Tendsto V'k atTop (𝓝 ℓ):=by
    have hp:= (accolade o p ω hU hV h0 e).const_mul ((Window.dimf f_):ℂ); apply hp.congr'; apply Eventually.of_forall; intro i; unfold V'k yD; rw [hX i]; ring
 let C:= Tendsto.const_div_atTop h0 1; refine ⟨squeeze_zero (fun i=>by unfold positionZ; positivity) (fun k=>(v k (y k) ((le_max_right ..).trans (t k))).1) C,fun Φ H=>?_⟩; apply hp.congr_dist; refine squeeze_zero (fun _=>dist_nonneg) (fun k=>( (show dist _ (V'k k) ≤ 1/tN k from ?_)).trans_eq rfl |>.trans' (dist_comm ..).le) C; rw [dist_eq_norm]; exact (v k (y k) ((le_max_right ..).trans (t k))).2 (Φ k) (H k) -- tune
#print axioms whirr
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
