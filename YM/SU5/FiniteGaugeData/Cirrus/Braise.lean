import YM.SU5.FiniteGaugeData.Cirrus.Truc
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute Mink
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)(U V:Set E4)(t:G.Token)(w:List G.Token)
local notation "D"=> G.Model S Ω
local notation "X"=> Effort S Ω G
local notation "E"=> G.lens S Ω
local notation "Ω₁"=>G.focus S Ω []
local notation "Kₐ"=> Hull S Ω G
open Canopy Submodule
variable (A B C:Effort S Ω G) (Pn:Boundary.Action H)(L:G.Arrival S Ω Pn)
local notation "T₂"=> DualR S Ω G
local notation "M₁"=>MeanBill S Ω G
local notation "Q"=> Qof S Ω G
local notation "P"=> Pale S Ω G
variable (hΩ:∀ x:E4,M S x Ω.val=Ω.val)
include hΩ L
-- faithful Herm response criterion
lemma leanSignal (p: ¬ Pale S Ω G J K)(u:IsOpen U)(u':U.Nonempty)(v:IsOpen V)(v':V.Nonempty) : ∃ A:Effort S Ω G, A∈Kₐ J U∧ QuietM S Ω G A∧ ∃ B: (X), B∈Kₐ K V∧QuietM S Ω G B∧ Q A B≠0 :=by
 by_contra! h
 apply p; refine extinct S Ω hΩ G J K Pn L.time U V u v u' v' ?_; intro w x t s; let A:= Route S Ω G w; let B:= Route S Ω G x
 have he(S₀:X)(p:S₀∈Kₐ J U)(r:QuietM S Ω G S₀): Q S₀ B=0:=by
    obtain ⟨X₀,X₁,a,b,v,z,H⟩:=digraph S Ω G K V B Pn L (pays_κ S Ω G K V x s); rw [H, θpeace S Ω G, h S₀ p r _ a v, h S₀ p r _ b z, mul_zero, zero_add]
 have τ: Q A B=0:= by
    obtain ⟨C,C',a,b,v,z,H⟩:= digraph S Ω G J U A Pn L (pays_κ S Ω G J U w t); rw [H, θmore S Ω G,he C a v, he C' b z, mul_zero, zero_add]
 unfold Qof at τ; unfold A B at τ; rw [routeRules,routeRules] at τ; exact τ
omit hΩ L
set_option maxHeartbeats 190000
private lemma blankPos (z:ℂ)(p:z ≠0)(h:star z=z): 0<z.re ∨ 0 <(-z).re := by
 have ht:= congrArg im h; simp at ht
 by_cases h:0< z.re; exact Or.inl h
 right; simp; apply lt_of_le_of_ne (not_lt.mp h); intro v; exact p (Complex.ext v (show z.im=0 from by linarith))
private lemma moveBill (c:ℂ): MeanBill S Ω G (A+c•B)=MeanBill S Ω G A+c*MeanBill S Ω G B:= by
 unfold MeanBill; simp only [LinearMap.add_apply,map_add,LinearMap.smul_apply,map_smul,inner_add_right,inner_smul_right]
abbrev stayZ := A+ (- MeanBill S Ω G A) • 1
include L
lemma stab (p:A∈ Kₐ J U∧ QuietM S Ω G A): let A':=stayZ S Ω G A; A'∈ Kₐ J U∧ QuietM S Ω G A' ∧ MeanBill S Ω G A'=0:=by
 intro A'; refine ⟨(Kₐ J U).add_mem p.1 ((Kₐ J U).smul_mem ((Kₐ J U).one_mem) _), ?_, ?_⟩
 · have he:= cash S Ω G 1 1 (oneD S Ω G) (-(M₁ A)); rw [star_neg,taxR S Ω G A p.2] at he; exact both S Ω G A A p.2 he
 unfold A' stayZ; rw [moveBill S Ω G,tariffL S Ω G L.omega,mul_one,add_neg_cancel]
include hΩ
omit hΩ L in
lemma antiZ (f:QuietM S Ω G A): QuietM S Ω G (- A):=by intro x y; simp only [LinearMap.neg_apply,map_neg,inner_neg_left,inner_neg_right,f x y]
omit hΩ L in
lemma antiP : Q A (-B)=-(Q A B):=by
 unfold Qof linked; simp only [LinearMap.neg_apply,map_neg,inner_neg_right,mul_neg]; ring
/-- ∃ Herm observables with zero means and NONZERO (strictly pos real) product expectation at
real Minkowski separation. This Herm statement always means formal adjoints in Wightman.
Use with farther sets U V. -/
structure Soul (U V:Set E4) :Prop where
 drum : ∃ A:Effort S Ω G,A∈ Hull S Ω G J U ∧ QuietM S Ω G A ∧ MeanBill S Ω G A=0∧
        ∃ B:Effort S Ω G,B∈ Hull S Ω G K V∧ QuietM S Ω G B∧ MeanBill S Ω G B=0∧
          ∃ (c:ℝ),0<c∧ Commute A B∧ MeanBill S Ω G (A*B)=(c:ℂ)
omit hΩ in
lemma soulPos (z:separated U V) (f:A∈ Kₐ J U)(t₁:QuietM S Ω G A)(g:B∈ Kₐ K V)(t₂:QuietM S Ω G B)(p:0<(Q A B).re) : Soul S Ω G J K U V:=by
 obtain ⟨x₁,x₂,x₃⟩:= stab S Ω G J U A Pn L ⟨f,t₁⟩; obtain ⟨y₁,y₂,y₃⟩:=stab S Ω G K V B Pn L ⟨g,t₂⟩; let A':=stayZ S Ω G A; let B':=stayZ S Ω G B
 let c:= (Q A B).re; have hc:c>0:=p; have hf: Q A' B'= Q A B:=by unfold A' B' stayZ; rw [θmore,θpeace, τBlankL S Ω G _ L.omega, τBlankR S Ω G _ L.omega]; ring
 have hv: Q A B=(c:ℂ) := by
    let q:=Q A B; have hz:star q=q:= Hscalar S Ω G _ _ t₁ t₂ (apart S Ω G J K U V A B Pn L z f g); have he:= congrArg im hz; simp at he; exact Complex.ext rfl (show q.im=0 from by linarith)
 refine ⟨A',x₁,x₂,x₃,B',y₁,y₂,y₃,c,hc,apart S Ω G J K U V A' B' Pn L z x₁ y₁, ?_⟩
 rw [← hv,← hf,truth S Ω G A' B' x₂, show M₁ A'=0 from x₃, zero_mul,sub_zero]
set_option maxHeartbeats 40000 in
lemma exactC (p:¬ Pale S Ω G J K)(u:IsOpen U)(k:U.Nonempty)(v:IsOpen V)(t:V.Nonempty)(z:separated U V): Soul S Ω G J K U V:=by
 obtain ⟨A,r,h,B,e,a,q⟩:= leanSignal S Ω G J K U V Pn L hΩ p u k v t; let c:=Q A B; let d:=Q A (-B); have hp:= Hscalar S Ω G A B h a (apart S Ω G J K U V A B Pn L z r e)
 rcases blankPos c q hp with f|f; · exact soulPos S Ω G J K U V A B Pn L z r h e a f
 let u:Effort S Ω G:= Neg.neg B; have hu:u ∈ Hull S Ω G K V:= by
    suffices W:u=(-1:ℂ)•B by rw [W]; exact (Kₐ K V).smul_mem e _
    ext1 x; rw [LinearMap.smul_apply]; change -B x = _; module
 have ht: QuietM S Ω G u:= antiZ S Ω G B a
 have hz:(-c).re=(Q A u).re:= congrArg Complex.re (antiP S Ω G A B).symm
 have h₀:0<(Q A u).re:= lt_of_lt_of_eq f hz
 exact soulPos S Ω G J K U V A u Pn L z r h hu ht h₀
#print axioms exactC
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
