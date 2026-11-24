import YM.CF.Tarn.Sold
import YM.CF.Cloak.Coil
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
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r j:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
open Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
variable(T:Tube G S)(x u v:ℝ)(P:Tab S)(q:Chi)(d:ℝ)(l:ℕ)(M:Monk G S)
local notation "a₀"=> M.key
local notation "B₀"=> M.V
local notation "p₀"=> M.park
local notation "k₁"=> M.k
local notation "A₀"=> emptyA T x k₁ a₀ p₀ B₀
local notation "Δ"=> Real.log |(credW T a₀ p₀ k₁ q d x (M.bush x) l M.V).det|
-- subtract *full* flat common tree Gram. correction gets own labels. exponent independent of all frames.
def tit(i:Site c)(p: ℕ) :ℝ:=∑ z:Run (M.zoo x) (p+1), plant S i (stave z) * (-(1/2:ℝ)* barP A₀ (perZ T x k₁ a₀ p₀ B₀) z)
def kist:=bunk S (p₀,k₁) 1
local notation "k₀"=>kist M -- actual no T arguments
local notation "X₀"=> a₀
variable{θ t η ρ:ℝ}
structure NameX (M:Monk G S) (x:ℝ)(q:Chi)(d:ℝ)(l n:ℕ)(C θ t η ρ:ℝ):Prop where
 price : Neige.Mem n T x θ C t η ρ M.park M.key M.k M.V l q d (M.bush x)
 grow :0<θ
 posT :0≤ C
 tip:C*tipPay θ x <1
 tar :t<1
 tam:η<1
local notation "D₀"=> -(1/2:ℝ)*Real.log ((baseX T x (kist M).key p₀ k₁ 1).det)
lemma detP (p:NameX T k₀ x q d l n C θ t η ρ): HasSum (fun j=>∑ i,tit T x k₀ i j) D₀:=by
 let N:= k₀; let K:= baseX T x N.key p₀ k₁ 1; let Q:= emptyA T x k₁ N.key p₀ (1:Config G c); let V:= perZ T x k₁ N.key p₀ 1
 have hp:HasSum (pulseX Q V) (Real.log K.det):=by
    have he:Vmove x (kist M).V 0=1:=by simp [Vmove,kist,bunk]
    have hx:= p.price.center.run (mul_nonneg p.posT (Real.exp_pos _).le) p.tip
    simp only [Function.comp_apply, he] at hx; simp only [emptyA,add_sub_cancel] at hx; exact hx
 let ℳ:= -(1/2:ℝ); rw [show (fun j:ℕ=>∑ i,tit T x k₀ i j)= (fun i:ℕ=> ℳ*pulseX Q V i) from ?_]; exact hp.mul_left ℳ; ext1 i; unfold tit; rw [sum_comm]; simp_rw [←sum_mul,plant_s,one_mul,←mul_sum]; change _ = ℳ * pulseX Q V i; apply congrArg (ℳ * ·) -- tune
 unfold Q V; have he: Vmove x ((kist M).V) 0=1:=by simp [Vmove,kist,bunk]
 have hv:= bS p.price.center i; simp only [Function.comp_apply, he] at hv; exact hv.symm
lemma eerie (h:NameX T M x q d l n C θ t η ρ)(p: NameX T k₀ x q d l n C θ t η ρ): let U(i):=Quill T x q d l k₀ i -∑ j∈ Finset.range 3,tit T x k₀ i j; let V(i):= Quill T x q d l M i-Quill T x q d l k₀ i
 HasSum (fun j:ℕ=>∑ i:Site c,(beds T x q d l M (j+3) i-tit T x k₀ i (j+3))) (Δ-D₀-∑ i,(U i+V i)):=by
 intro X Y; have hv: Vmove x M.V 0=M.V:=by simp [Vmove]
 let Z(r):=∑ i:Site c,beds T x q d l M r i; let W(r):=∑ i:Site c,tit T x k₀ i r
 have he: HasSum Z Δ :=by
    have hy:= earnX h.price h.grow h.posT h.tar h.tam h.tip; rw [Real.log_abs]; convert hy using 1; swap; · rfl
    ext1 i; unfold Z; rw [baseZ]; unfold pes; simp_rw [sum_add_distrib,←mul_sum]
    let A:= h.price; -- tune hw
    rw [←hv]; rw [show (neo T x k₁ a₀ p₀ (Vmove x M.V 0))=((neo T x k₁ a₀ p₀) ∘ Vmove x M.V) 0 from rfl]
    refine congrArg₂ (·+·) (congrArg₂ (·+·) ?_ ?_) (bS A.modes _).symm; exact congrArg (-(1/2:ℝ)*·) (bS A.center _).symm; exact congrArg ((1/2:ℝ)*·) (bS A.core _).symm -- probably holes unspecified use congrArg assembly
 have hh:=he.sub (detP T x q d l M p); have hg : HasSum (fun i=> Z (i+3)-W (i+3)) (Δ-D₀-∑ i∈ Finset.range 3,(Z i-W i)):=(hasSum_nat_add_iff' 3).2 hh
 -- steer
 simp_rw [sum_sub_distrib]; convert hg using 2; unfold X Y Quill; simp only [Finset.sum_add_distrib,sum_sub_distrib]; unfold Z W; rw [sum_comm]; ring_nf
 rw [sum_comm (t:=Finset.range 3) (f:=fun i j=>tit T x k₀ i j),sum_comm (t:=Finset.range 3) (f:=fun i j=>beds T x q d l M j i)]; abel
end YM.CF.Corne
