import YM.Primitives.HAAR_LOG_JETS.Guard
import YM.CF.Tarn.Swan
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
section
open Stationary Push.Loops
variable {T:Pressure.Tube SU.group S}{K:Pressure.Teller G}
variable (T:Pressure.Tube G S)(x u:ℝ)(P:Tab S)(q:Chi)(R:ChartRatio G)(t d α:ℝ)(l:ℕ)
def Coin (P:Tab S):FileM c G:= rugG T x q d α l P-MossZ T x q d l R t P-neatQ T x u q d l P
lemma salt (h:K.Funds S T)(hp:Ready T x)(hx:1000 ≤radiusB x)(hm:0 < m)(hP:∀ V:Tab S,∀ y:Mast G c, ‖y‖<1→ FreeResolvent.Gap (baseX T x (bareStores S) V.1 V.2 (satU G u y)) m)(ht: LocalRatio R)(hr:4*t < R.radius)(hv:0<t) : let U: FileM c G:=fun i=> Arena.aria fun v=>Coin T x u q R t d α l v i; ∀ i b:Site c,U (i+b)=U i ∘ Lattice.translate b:=by
 intro U i b; let V(P:Tab S):=Coin T x u q R t d α l P; let p:= Arena.spun S 1 b; have he(Z:Config G c)(g:Tab S): V (p g) i (Lattice.translate b Z)= V g (i+b) Z:=by
    let f:= (p g); have ha: f=dial S 1 b g:=rfl; have hb:affine 1 b i=i+b:=by simp [affine]
    unfold V Coin; simp only [Pi.sub_apply]; rw [neck T x u q d l K h hp hm hx hP i b Z,←hb,← pull_one]; rw [show p g=dial S 1 b g from rfl,rug_o T x q d α l K h, halo_p T x q d l R t hv hr ht h]
 ext1 w; unfold U Arena.aria; simp only [Pi.smul_apply,Finset.sum_apply,Function.comp_apply]; apply congrArg ((Fintype.card (Tab S):ℂ)⁻¹ • ·)
 rw [← Equiv.sum_comp p (fun y=>V y i (Lattice.translate b w))]; exact Finset.sum_congr rfl fun i _=> (he w i).symm -- tune
lemma scopeR {Z:Tab S}(i:Site c)(p:Kind S P Z (pavilion (Cay.horn x l) i))(hp:Ready T x)(ht:1000 ≤radiusB x): Coin T x u q R t d α l P i=Coin T x u q R t d α l Z i:=by
 unfold Coin; simp only [Pi.sub_apply]; rw [rug_k T x q d α l i P Z p hp ht,show MossZ T x q d l R t P i=MossZ T x q d l R t Z i from ?_,knit T x u q d l P Z (kind_m p ?_) hp ht]; swap
 · exact funext fun i=> paidz T x q d l R t _ p i i (fun _ _=> rfl) hp ht
 intro j hj; exact (theatre ..).mpr (((theatre ..).mp hj).trans (Nat.mul_le_mul_right _ (by omega)))
lemma gleam (ξ:ℂ→ℂ)(V:Config G c)(i:Site c): star (Coin T x u q R t d α l P i V)=Coin T x u q R t d α l P i V:=by
 let X:= (Fintype.card Signed:ℂ)⁻¹; have hz:star X=X:=by simp [X]
 have he: star (neatQ T x u q d l P i V)=neatQ T x u q d l P i V:=by unfold neatQ salsa; split<;> simp
 unfold Coin; simp only [Pi.sub_apply,star_sub]; rw [he]; unfold MossZ rugG Arena.aria; simp only [Pi.smul_apply, Finset.sum_apply,smul_eq_mul,HWork, star_sub,Complex.star_def,Complex.conj_ofReal, map_mul,map_sum,tilT, map_sub, map_natCast,map_inv₀] -- tune
private def barG (s:Signed) : InputZ G c →L[ℝ] InputZ G c:= LinearMap.toContinuousLinearMap
  { toFun:=fun a=>Bid.pulled a s, map_add':=by intro x y; funext b; simp only [Bid.pulled,Pi.add_apply]; split <;> abel
    map_smul':=by intro x y; funext b; simp only [Bid.pulled,Pi.smul_apply]; split <;> simp }
lemma hem(i:Signed)(V:InputZ G c): pull i 0 (represent V)=represent (barG i V):=(Rel.barG_p ..).symm
lemma often(T:Pressure.Tube G S)(P:Tab S)(i: Signed)(hs:0<u):∀ᶠ y:InputZ G c in 𝓝 0,represent y∈pines G c u∧ pull i 0 (represent y)∈pines G c u:=by
 let L:=chair T P.1; let X:=u⁻¹ • L; have he :∀ᶠ y:InputZ G c in 𝓝 0,represent y∈pines G c u:=by
    filter_upwards [X.continuous.continuousAt.eventually (isOpen_ball.mem_nhds (show X 0∈ball (0:Mast G c) 1 by simp))] with y hy; have hh:satU G u (X y)=represent y:=by unfold satU; rw [show u • X y=L y from smul_inv_smul₀ hs.ne' (L y)]; exact chap T P.1 _
    exact hh ▸ pine_p _ _ (mem_ball_zero_iff.mp hy)
 have hp: Tendsto (barG i (c:=c)) (𝓝 0) (𝓝 0):=by simpa using (barG i (c:=c)).continuous.tendsto 0
 filter_upwards [he,hp.eventually he] with i hi hp; rw [hem]; exact ⟨hi,hp⟩
lemma sage(i:Site c)(k:Signed)(P:Tab S)(U:Config G c)(h:K.Funds S T)(hp:Ready T x)(hx:1000 ≤radiusB x)(hm:0 < m)(hP:∀ V:Tab S,∀ y:Mast G c, ‖y‖<1→ FreeResolvent.Gap (baseX T x (bareStores S) V.1 V.2 (satU G u y)) m)(ht: LocalRatio R)(hr:4*t < R.radius)(hv:0<t)(hc:U∈pines G c u)(hg:pull k 0 U∈pines G c u): Coin T x u q R t d α l (dial S k 0 P) i (pull k 0 U)=Coin T x u q R t d α l P (k.act i) U:=by
 have he(i)(V:Tab S)(y:Config G c)(v:y∈pines G c u): neatQ T x u q d l V i y=(zestQ T x q d l V i y:ℂ):=by obtain ⟨p,u,rfl⟩:=v; exact fruitZ T x _ q d l _ (mem_ball_zero_iff.mp u) (hP V) h hm hp hx
 unfold Coin; simp only [Pi.sub_apply]; rw [show k.act i=affine k 0 i by simp [affine], rug_o T x q d α l _ h,halo_p T x q d l R t hv hr ht h, he _ _ _ hg, he _ _ _ hc, pest T x u q d l _ h hm hx hP P U i 0 k hc]
lemma selfD(i:Site c)(h:K.Funds S T)(hp:Ready T x)(hx:1000 ≤radiusB x)(hm:0 < m)(hP:∀ V:Tab S,∀ y:Mast G c, ‖y‖<1→ FreeResolvent.Gap (baseX T x (bareStores S) V.1 V.2 (satU G u y)) m)(ht: LocalRatio R)(hr:4*t < R.radius)(hv:0<t)(hu:0<u): let V: FileM c G:=fun i=>aria (fun v=>Coin T x u q R t d α l v i); Head c ((LinearIsometryEquiv.refl ℝ SU.group.Color).toLinearIsometry) V:=by
 intro V; have he(i:Site c)(x':Config G c): star (V i x')= V i x':=by
    unfold V Arena.aria; simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul,star_mul,map_inv₀,star_inv₀,star_natCast,star_sum,gleam (ξ:=id)]; ring -- tune
 constructor
 · exact fun i=> Eventually.of_forall fun x=> (he i (represent x)).symm -- Vsail refl defeq
 intro j k; let v:= Signed.mirror k; let g:= Arena.spun S v 0; let SQ:= Coin T x u q R t d α l
 filter_upwards [often u T (Classical.choice ⟨((Classical.choice (Tree.select _ S.patch.odd_side)),Classical.ofNonempty)⟩) v hu] with y hy; change _ = star (V (v.act j) (represent y)); rw [show star _= _ from he (v.act j) (represent y)]; unfold V Arena.aria; simp only [Pi.smul_apply,Finset.sum_apply]; apply congrArg ((Fintype.card (Tab S):ℂ)⁻¹ • ·);
 let U:=pull v 0 (represent y); rw [← Equiv.sum_comp g (fun t=> SQ t j U)]; exact Finset.sum_congr rfl fun i _=>sage T x u q R t d α l j _ i _ h hp hx hm hP ht hr hv hy.1 hy.2
end
end YM.CF.Tarn
