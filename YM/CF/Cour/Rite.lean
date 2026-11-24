import YM.CF.Cour.Route
import YM.CF.Pec.Ora
import YM.CF.Souk.Rayon
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort
open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Hors Newt Souk RG Push Pressure
open Next.SectorChange AnalyticBridge.MarginalMultiplier3b1d Next.SectorChange.Wisps
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {ι:Type}[Fintype ι]{B L:Side}{n k j:ℕ}{e t x u C A:ℝ}
variable {p:Clip}{q: Gauge}{c f:Side}
section pale
open scoped Matrix.Norms.Frobenius
lemma riseP{R:PathData q}(D:ℝ)(h:Uniform.PaintSupply q 2 D)(j:ℕ)(t:ℝ){Λ k' a:ℝ}(hw:R.Bounds p k' A a)(hz:2 ≤ c.val)(i: Fin 2 → Primary c q):
 let B(u:Mast q c):ℝ:= secondTerm p R (represent (tint q _ u))- secondTerm p (safeD R j) (represent (tint q _ u))
 let X:=stip q 1 2 D k'; ContDiffAt ℝ 2 B 0 ∧ |Uniform.entry B 0 i| ≤ tollE k' j *(Stationary.gramCost q A*X):=by
 intro B X; let Z(s:Signed)(u:Mast q c):=uncut (rod R j) (pull s 0 (represent (tint q _ u)))
 have ht s : ContDiffAt ℝ (2:ℕ) (Z s) 0 ∧|Uniform.entry (Z s) 0 i| ≤ tollE k' j*(Stationary.gramCost q A*X):=by
    obtain ⟨p,q⟩:=Hors.lead (i:=j) (G:=q) (rod R j) (hurry hw j) hw.width hz h s i; exact ⟨p.of_le le_top,q⟩ -- tune
 rw [show B=(fun y=>Patch.average fun t:Signed=>Z t y) from funext fun y=>lamplighter hw _ t _]; refine ⟨?_,Hors.winds_C _ _ (fun i=>(ht i).1) _ (fun i=>(ht i).2)⟩
 exact (ContDiffAt.sum (s:=Finset.univ) (n:=2) (f:=Z) fun i _=> ((ht i).1).of_le (by norm_num)).const_smul ((Fintype.card Signed:ℝ)⁻¹)
end pale
variable{m X:Side}{T:Roam m X B}{H: Tube group T}{F: Forest T.ratio}{G: Ratio (CSide m B) (CSide X B)}
variable {p:L.val=G.count.val}{h:Odd L.val}{Y:Pricing j L h (Thread j)}{P:Grasp Y B e}
variable {z:Vox m B→ AxisChart group F}
open Pec
-- chiral scalar score, inflation stationary
abbrev shipA(G:Ratio (CSide m B) (CSide X B))(P:Grasp Y B e) (M:Male)(U:Dress (CSide X B))(I:Pride (CSide X B))(K:Pride (CSide m B))(x:nomA m X B):ℂ:= pigment I x.1+ lush G P M U x - pigment K x.2
lemma sightU(G:Ratio (CSide m B) (CSide X B))(F:Forest T.ratio)(z:Vox m B→ AxisChart group F)(p:0<e)(R:PathData group)(q:Clip)(P:Grasp Y B e)(M:Male)(U:Dress (CSide X B))(I:Pride (CSide X B))(K:Pride (CSide m B))(α:ℝ) (t:ℝ) (y:Mast group (More (CSide m B))): shipA G P M U I K (hats F (flute F (Uniform.station z) t y))- α • secondM q R (tint group _ (t•y))= myth G F z q R P M U I K α (tint group _ (t•y))+(lush G P M U (ears F z 0)):=by
 unfold flute; rw [wellPath]; unfold shipA myth deflate; change pigment _ _+lush _ _ _ _ _-pigment _ _-_=pigment _ _+(lush _ _ _ _ _-lush _ _ _ _ _)-_-pigment K _+_
 let A:=tint group _ (t•y); let f:=pigment I (baby F z A); let Z:=lush G P M U; let X:=pigment K (represent A); change f+Z (ears F z A)-X-_ = f+(Z _-Z _)-_-X+Z _; abel
lemma draw_s(G:Ratio (CSide m B) (CSide X B))(F:Forest T.ratio)(z:Vox m B→ AxisChart group F)(p:0<e)(R:PathData group)(q:Clip)(P:Grasp Y B e)(M:Male)(U:Dress (CSide X B))(I:Pride (CSide X B))(K:Pride (CSide m B))(α t:ℝ) (h:cFoot 3 (myth G F z q R P M U I K α)) (ht:0<t) (i:Fin 2→Uniform.Primary (More (CSide m B)) group):
 let f:= fun y=> shipA G P M U I K (hats F (flute F (Uniform.station z) t y))- α • secondM q R (tint group _ (t•y))
 ContDiffAt ℝ 2 f 0 → Uniform.entry f 0 i=0:=by
 intro f g; let H:=myth G F z q R P M U I K α; let L:Mast group (More (CSide m B)) ≃L[ℝ] Vox m B:= (ContinuousLinearEquiv.smulLeft  (Units.mk0 t ht.ne')).trans (tint group _); let A:ℂ:=lush G P M U (ears F z 0)
 have hz f': L f'=tint group _ (t•f'):=rfl
 have he:f=(fun y=>H (L y)+A):=funext fun y=> sightU G F z p R q P M U I K α t _
 let Y'(i):= f i-A; have hY: Y' ∘ L.symm=H:=by funext i; unfold Y'; simp only [he,Function.comp_apply,L.apply_symm_apply,add_sub_cancel_right]; -- tune
 have hf: ContDiffAt ℝ (2:ℕ) H (L 0):=by
    rw [map_zero,← hY]; apply ContDiffAt.comp; · rw [map_zero]; exact (g.of_le (by norm_num)).sub contDiffAt_const
    exact L.symm.contDiff.contDiffAt
 unfold Uniform.entry; rw [he,show (fun y=>H (L y)+A)=H ∘ L+(fun _=> A) from rfl,iteratedFDeriv_add_apply (hf.comp _ L.contDiff.contDiffAt) contDiffAt_const,iteratedFDeriv_const_of_ne (by decide:(2:ℕ) ≠ 0),Pi.zero_apply, add_zero]; change iteratedFDeriv _ _ (H ∘ L) _ _= _; rw [show iteratedFDeriv ℝ 2 (H ∘ L) 0=_ from Uniform.iter_lin_at hf (L:= L.toContinuousLinearMap), show L.toContinuousLinearMap (0:Mast _ _)=_ from (map_zero _), show iteratedFDeriv ℝ 2 H 0= _ from h 2 (by omega)]; rfl -- tune
end YM.CF.Cour
