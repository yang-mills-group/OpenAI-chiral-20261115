import GaugeFieldConstruction.Corners

/-!
# Angular matrices on the point data
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Calibration.RawBank
open Gap Cauchy Conj Row Phys Function Submodule U1 Flux One Stage Wide Stage.Cell One.Lamp Floor
open Matter (Slot FlavorIndex)
open Matrix
open scoped Matrix BigOperators Topology ContDiff

-- prelim geometry
lemma allowance : ∃ χ, Chassis 0 Wick.apex χ := exists_path 0 Wick.apex Wick.exposed.symm
lemma idle {α β : Type*} (L : Lamp α β) {K χ x y p} (v : L.Latch χ K x y 0 p) (d) : L.cost x y p d=0 := by
  rw [← v]; simp [Lamp.glow, YM.GaugeFieldConstruction.Flux.Shell,Flux, currentZ,toll,YM.Maxwell.Free.exportFlux]

lemma leavesG (d) (u : J (BoxG d)) (h :(DeckG d).issue u=0) (Ω : Rotors): (DeckG d).issue ((gCard d).beta Ω u)=0 := by
  obtain ⟨χ,p⟩:= allowance; apply globe (gStress 1)
  have H:= rotor (Lamp.gloG (gStress 1)) (Go 1 (soarC Ω 0).toCourse (soarT Ω 0) d u) p
  rw [h,Submodule.coe_zero,map_zero,one_smul] at H
  exact idle _ H
lemma leavesF (d) (u : J (BoxF d)) (h :(DeckF d).issue u=0) (Ω : Rotors): (DeckF d).issue ((fCard d).beta Ω u)=0 := by
  obtain ⟨χ,p⟩:= allowance; let i:FlavorIndex:=(true,0,0); let v:= fun _ : Bool=>(1:ℂ)
  apply gloss (fStress v) i; have H:= rotor (Lamp.gloF (fStress v)) (Fo v (soarC Ω 0).toCourse (soarT Ω 0) d i u) p
  rw [h,Submodule.coe_zero,map_zero] at H; unfold v at H; rw [one_smul] at H; exact idle _ H
lemma nilX (d) (u:J (BoxX d)) (h:(DeckX d).issue u=0) (Ω:Rotors) (m V:ℂ): (DeckX d).issue (scratch Ω d m V u) =0:=by -- adjust
  obtain ⟨χ,p⟩:= allowance; let i:FlavorIndex:=(false,0,0); let v:=fun _ : Bool=>V
  apply glass (fStress v) (gStress m) i; have H:= Xout m v Ω p i d u; rw [cash,cash,h,Submodule.coe_zero,map_zero] at H
  dsimp only [v] at *; exact idle _ H
/-- diagonal idempotence in those coordinates. -/
def activates (i : Bool) : ℂ := if i then 1 else 0
lemma tripleL (d : Floor) (m b : Bool) (Ω) : scratch Ω d (activates m) (activates b)=(xCard d m b).beta Ω := by
  cases d <;> apply ket_ext <;> intro X
  · exact (show Empty from X).elim
  · exact (show Empty from X).elim
  let i:MX:=X; have he (a b) : (xCard five a b).beta Ω (ket X)=Cell.beta (PX a b) Ω (ket i):=rfl
  simp only [scratch,LinearMap.add_apply,LinearMap.smul_apply]; simp_rw [he]
  change activates m • ((PX true false).beta Ω (ket i)) + activates b • ((PX false true).beta Ω (ket i)) = (PX m b).beta Ω (ket i)
  rw [show ket i=times' (ket i.1) (ket i.2) from (takes ..).symm]; cases m <;> cases b <;> simp only [activates,PX,Bool.false_eq_true,↓reduceIte,one_smul,zero_smul] <;> first |rfl | (rw [optionB]; simp only [split_legs,vacant,map_zero,LinearMap.zero_apply,add_zero,zero_add])
  rw [optionB,optionB]; simp only [split_legs,vacant,map_zero,add_zero]; rw [add_comm]
lemma leavesX (d b c) (u:J (BoxX d)) (h:(DeckX d).issue u=0) (Ω:Rotors): (DeckX d).issue ((xCard d b c).beta Ω u)=0 := by rw [← tripleL]; apply nilX d u h

namespace Mint
variable {α β V : Type*} {R : Record β V} {F : Flip β} {H : Submodule ℂ (J β)} [Fintype α] [DecidableEq α] (B : Mint R H F α)
  (C : Cell α) (h : ∀ x : J α,B.issue x=0→∀ Ω,B.issue (C.beta Ω x)=0)

lemma bend (B : Mint R H F α): ∃ g : H→ₗ[ℂ] J α,B.issue ∘ₗ g=LinearMap.id := by
  letI : AddCommGroup ↥H:= @Submodule.addCommGroup ℂ (J β) _ _ _ H
  haveI := Module.Free.of_divisionRing ℂ ↥H
  exact B.issue.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr B.supply)
def protrude (B : Mint R H F α) : H→ₗ[ℂ] J α:= Classical.choose (bend B)
include h
lemma deduct (x y) (w : B.issue x=B.issue y) (Ω) : B.issue (C.beta Ω x)=B.issue (C.beta Ω y) := by
  have he:=h (x-y) (by rw [map_sub,w,sub_self]) Ω
  rw [map_sub,map_sub,sub_eq_zero] at he; exact he -- h not included!

-- Lie action linear & bracket directly via β
omit h in
def spin (B : Mint R H F α) (C : Cell α) (Ω:Rotors):Module.End ℂ H:= B.issue ∘ₗ C.beta Ω ∘ₗ protrude B
lemma click (Ω x): spin B C Ω (B.issue x)= B.issue (C.beta Ω x) := deduct B C h _ _ (by
  have ht : B.issue ∘ₗ protrude B=LinearMap.id:= Classical.choose_spec (bend B)
  exact LinearMap.congr_fun ht _) Ω
lemma plus (Ω Γ):spin B C (Ω+Γ)= spin B C Ω+ spin B C Γ := by
  apply LinearMap.ext; intro x; obtain ⟨s,rfl⟩:=B.supply x; simp_rw [LinearMap.add_apply, click B C h]; simp [Cell.beta,cruise]
lemma timesL (c : ℝ) (Ω): spin B C (c • Ω)=(↑c:ℂ) • spin B C Ω := by
  apply LinearMap.ext; intro x; obtain ⟨s,rfl⟩:= B.supply x; simp_rw [LinearMap.smul_apply,click B C h]; simp only [map_smul,LinearMap.smul_apply,Cell.beta,Cell.jewel]
lemma circle (Ω Γ q): spin B C (tick Ω Γ) q= spin B C Ω (spin B C Γ q)-spin B C Γ (spin B C Ω q) := by
  obtain ⟨s,rfl⟩:= B.supply q; simp_rw [click B C h];
  suffices C.beta (tick Ω Γ)= C.beta Ω*C.beta Γ-C.beta Γ*C.beta Ω by rw [this]; simp
  unfold Cell.beta; rw [C.bracket, success,success]
  apply ket_ext; intro i; simp only [LinearMap.sub_apply,bill,on_ket, Matrix.sub_apply]; push_cast; simp [sub_smul, Finset.sum_sub_distrib]

lemma faithful (M : LabelAction.Carries R H) (m : Fast B.label C) (s : Signed) (u v): M.moves s (spin B C u v)= spin B C (conjS s.ortho u) (M.moves s v) := by
  obtain ⟨p,rfl⟩:= B.supply v; rw [click B C h,← respect,← respect,click B C h]; rw [m s u]
lemma cReal (Ω v w) (p : (w:H).val= F (v:H).val): (spin B C Ω w).val=F (spin B C Ω v).val := by
  obtain ⟨x,rfl⟩:=B.supply v; have hh : w=B.issue (tr _ x):=Subtype.ext (p.trans (Mint.real B x))
  have he : tr _ ∘ₛₗ C.beta Ω=C.beta Ω ∘ₛₗ tr _ := ksets (fun i=>by simp only [LinearMap.comp_apply,tr_ket,Cell.beta,bill,on_ket,map_sum,LinearMap.map_smulₛₗ]; simp [tr_ket,bar])
  rw [hh,click B C h,click B C h]; change jet _ _=F (jet _ _); rw [Mint.real]; exact congr_arg (jet _) (Eq.symm (LinearMap.congr_fun he _))
end Mint
end YM.GaugeFieldConstruction.Calibration.RawBank
