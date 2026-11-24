import YM.CF.Corne.Hol
import YM.CF.Rill.Fair
import YM.CF.Corne.Falls
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Corne
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reine
local notation "G₅"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r j:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G₅}{P': Tab S}
open Lat Rush Cour Scroll Laic Kennel Paige Spire Branch Broc Pec Facet Peaks
variable {n' B Mx X: Side}{T: Roam Mx X B}(G: Ratio (CSide Mx B) (CSide X B))(F:Tube G₅ T)
variable {C V R Z η e:ℝ}(Q: Msca Mx X B G e){Φ:nomA Mx X B→ ℂ}
local notation "pG"=> CSide Mx B
local notation "pF"=> CSide X B
local notation "D₀"=> More pG
local notation "D₁"=> More pF
variable (x d u:ℝ)(q:Chi)(l:ℕ)(S: Monk G₅ T)(A:Rent0 G e)(β:ℝ)(t:0 < e)
section
local notation "Y"=> mSeal X B
open Atala Skye Ac Rill Girt
section around
variable{E:Type}[TopologicalSpace E](w:E→Monk G₅ T)(x₀:E)
lemma seeX (u b c t:ℝ) (Z:ℝ)(V:Scree.Loom (CSide Mx B))(v:Roof (CSide Mx B) c Z j V)(U:Scree.Loom (CSide X B))(p:Roof (CSide X B) c Z n U)(hu:T.ratio=ratio G)(s:Chi)(I:Ids (CSide Mx B))(D:Ids (CSide X B))(F': E→Rent0 G e) (ht':∀ i,(F' i).val=YF G V U s t (hu ▸ (w i).park) ((w i).V,I) ((w i).sent x F q d l β,D))
 (hK:0<b)(hp:u < c)(hz:b<t)(hv:t< firstRadius G₅)(hk:j+n≤ radiusB x)(hR:Ready F x)(hr:1000≤radiusB x)(hv':ContinuousAt (fun i=>(w i).V) x₀)(hp':ContinuousAt (fun i=>(w i).sent x F q d l β) x₀)(hq:∀ᶠ i in 𝓝 x₀,(w i).key=(w x₀).key) (hB:Bell T (w x₀) x F q d l β u b)(i:Site D₀)(hs:i∉ (w x₀).key.dome (25*radiusB x)):∀ᶠ i' in 𝓝 x₀,Bride G F x d q l (w i') (F' i') β (radiusB x+1) i:=by
 let X':= w x₀; let L0:Support D₀:= univ; have hh :PaneL X' L0 x c t (X'.sent x F q d l β):=by -- L0
    apply uplift (F:=L0) (V:=X'.V) _ hR _ _ hB hp hz hK hr (subset_univ _); exact ⟨fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩; exact fun _ _ _=> rfl; exact fun i p=> hB.height ((mem_inter.mp p).2)
 let L:= X'.key
 let g(i:E):=(w i).V; let W(i:E):=(w i).sent x F q d l β -- remove
 have hy(i:Bond D₁):∀ᶠ y in 𝓝 x₀,T.ratio.parent i.1∈L0→ T.ratio.parent i.1∉ L.dome (20*radiusB x)→ (W y) i* (replica T.ratio (g y) i)⁻¹∈ SU.group.lieExp '' ball 0 t:=by
    let G(y:E):=W y i*(Precision.replica T.ratio (g y) i)⁻¹; have hv:ContinuousAt G x₀:= ((continuous_apply i).continuousAt.comp hp').mul ((show ContinuousAt (fun y:E=> Precision.replica T.ratio (g y) i) x₀ from by unfold Precision.replica; split; exact continuousAt_const; exact (continuous_apply _).continuousAt.comp hv').inv)
    by_cases hg:T.ratio.parent i.1∈L.dome (20*radiusB x); · exact Eventually.of_forall fun _ _ p=> (p hg).elim
    exact (hv.eventually (((LocalH.geom_patch G₅).choose_spec.2 t (by assumption:t<firstRadius G₅).le).1.mem_nhds (hh.farF i (mem_univ _) hg))).mono fun i p _ _=>p
 filter_upwards [cotton g (fun i _=>(continuous_apply _).continuousAt.comp hv') hh.stampK, cotton W (fun i _=>(continuous_apply _).continuousAt.comp hp') hh.mindF,hq,eventually_all.mpr hy] with y t₁ t₂ hX hy; let M':=w y; have hY:M'.key=L:=hX; have hh: PaneL M' L0 x c t (M'.sent x F q d l β):=⟨by rw [hY]; exact t₁,by rw [hY]; exact t₂,fun i u t=> hy i u (hY ▸ t)⟩
 constructor
 · intro k u; rw [ht']; refine v.lamp _ _ k (disjoint_left.mpr fun z g t=>?_); have hv':z∈ M'.key.flags:=sav _ _ _ _ hh.stampK (mem_inter.mpr ⟨mem_univ _,g⟩); rw [hY] at hv'; apply hs (halo_spec.mpr ⟨z,mem_union_right _ hv',(separation_triangle z k.1 i).trans (by rw [separation_comm _ i]; have ht:= Atala.win_r t; omega)⟩)
 intro k u; have he: T.ratio.parent k.1 ∉ M'.key.dome (20*radiusB x):= fun h=> hs (dome_u (hY ▸ h : _∈ (w x₀).key.dome (20*radiusB x)) (by rw [separation_comm _ i]; omega)); rw [ht']; exact (beam_l G hu _ hh p v (by omega) hr (hK.trans hz) hv k he (subset_univ _) _ _).trans (partR hh p (fun u=> he (farther (Nat.mul_le_mul_right _ (by omega)) u)) (subset_univ _) (by omega) hr D)
end around
end
end YM.CF.Corne
