import YM.SU5.FiniteGaugeData.Cirrus.WheelH
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
abbrev MeanBill : ℂ:= inner ℂ Ω.val (E (A Ω₁))
local notation "M₁"=>MeanBill S Ω G
abbrev Qof :ℂ:= linked (H:=H) Ω.val (E (A Ω₁)) (E (B Ω₁))
local notation "Q"=> Qof S Ω G
lemma taxR(v:T₂ A A): star (MeanBill S Ω G A)= MeanBill S Ω G A:= (inner_conj_symm ..).trans (v Ω₁ Ω₁)
lemma θmore (c:ℂ): Q (A+c • B) C=Q A C+star c* Q B C:=by
 unfold Qof linked; simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,inner_add_left,inner_smul_left,RCLike.star_def]; ring -- tune star
lemma θpeace (c:ℂ) : Q A (B+c• C)=Q A B+c* Q A C:=by
 unfold Qof linked; simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,inner_add_right,inner_smul_right]; ring
lemma truth (p:T₂ A A): Q A B= M₁ (A*B)- M₁ A * M₁ B:=by unfold Qof linked; rw [show inner ℂ _ _=_ from p Ω₁ (B Ω₁),show inner ℂ (E (A Ω₁)) Ω.val=M₁ A from p Ω₁ Ω₁]; rfl
lemma quietProduct (p:T₂ A A)(q:T₂ B B)(z:Commute A B) : T₂ (A*B) (A*B):=by have e:= exhibit S Ω G A A p q; nth_rw 2 [z.eq]; exact e
lemma Hscalar(p:T₂ A A)(k:T₂ B B)(r:Commute A B): star (Q A B)= Q A B:=by rw [truth S Ω G A B p]; rw [star_sub,star_mul,taxR S Ω G _ (quietProduct S Ω G A B p k r), taxR S Ω G B k,taxR S Ω G A p,mul_comm (M₁ A)] -- tune ℂ smul
lemma oneD: DualR S Ω G 1 1:=fun _ _=>rfl
private lemma πr : star (I:ℂ)= -I:=by simp
lemma solveHerm (ρ:ℂ)(p:T₂ A B): QuietM S Ω G (ρ•A+star ρ • B):=by
 let a:= both S Ω G (ρ•A) (star ρ • B) (cash S Ω G A B p ρ) (cash S Ω G B A (twoSide S Ω G A B p) (star ρ)); rw [star_star,add_comm (star ρ • B)] at a; exact a
variable (HΩ:‖Ω.val‖=1)
include L
lemma digraph (p:A∈ Kₐ J U): ∃ B C: Effort S Ω G,B∈Kₐ J U ∧ C∈ Kₐ J U∧ QuietM S Ω G B∧ QuietM S Ω G C∧ A=B+I • C:=by
 obtain ⟨B,u,H⟩:= reserve S Ω G J U A Pn L p
 let s (c:ℂ):= c•A+ star c•B; let u₀:ℂ:=1/2; have v(c:ℂ):s c∈ Kₐ J U:= (Kₐ J U).add_mem ((Kₐ J U).smul_mem p _) ((Kₐ J U).smul_mem u _)
 refine ⟨s u₀,s (-I/2),v _,v _,solveHerm _ _ _ _ _ _ H,solveHerm _ _ _ _ _ _ H,?_⟩
 change A=(1/2:ℂ) • A+_ +I • ((-I/2:ℂ) • A+_)
 have hz:star u₀=u₀:=by simp [u₀]
 have hu:star (-I/2)=I/2:=by simp
 rw [hz,hu]; unfold u₀; rw [smul_add,smul_smul,smul_smul,show I*(-I/2:ℂ)=(1/2:ℂ) from by linear_combination -1/2 * I_mul_I,show I*(I/2:ℂ)=-(1/2:ℂ) from by linear_combination (1/2:ℂ)* I_mul_I]; module
omit L
include HΩ
lemma currency : inner ℂ Ω.val Ω.val=1:=by rw [inner_self_eq_norm_sq_to_K,HΩ]; simp
lemma tariffL : MeanBill S Ω G 1=1:=currency S Ω HΩ
lemma τBlankL : Qof S Ω G 1 A=0:=by change inner ℂ Ω.val _-inner ℂ Ω.val Ω.val*inner ℂ Ω.val _=0; rw [currency S Ω HΩ]; simp
lemma τBlankR : Q A 1=0:=by unfold Qof; rw [tie_κ, show linked (H:=H) Ω.val _ _=0 from τBlankL S Ω G A HΩ,map_zero]
#print axioms Hscalar
#print axioms digraph
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
