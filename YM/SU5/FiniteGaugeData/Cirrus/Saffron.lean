import YM.SU5.FiniteGaugeData.Cirrus.Epitom
/-!
# Saffron. PointWight relative net of unbounded field polynomials

 On common invariant Domain, no claim strong commutation of extensions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute Mink
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)(U V:Set E4)(t:G.Token)(w:List G.Token)
local notation "D"=> G.Model S Ω
abbrev Effort := Module.End ℂ (G.Model S Ω)
local notation "X"=> Effort S Ω G
local notation "E"=> G.lens S Ω
local notation "Ω₁"=>G.focus S Ω []
abbrev RToken := {x:G.Token|x.1.1∈ J∧ LetterQ U x.2}
local notation "T₁"=> RToken G J U
def Hull : Subalgebra ℂ (X):= Algebra.adjoin ℂ ((G.conduct S Ω) '' (RToken G J U))
local notation "Kₐ"=> Hull S Ω G
open Canopy Submodule
lemma regi (p:J ⊆ K)(v:U ⊆ V): Hull S Ω G J U≤ Hull S Ω G K V:=by apply Algebra.adjoin_mono; exact image_mono (s:= RToken G J U) (t:= RToken G K V) (fun t d=>⟨p d.1,d.2.1,_root_.subset_trans d.2.2 v⟩)
lemma seeds (v:t∈ T₁): G.conduct S Ω t∈ Hull S Ω G J U:= Algebra.subset_adjoin ⟨t,v,rfl⟩
variable (A B:Effort S Ω G) (Pn:Boundary.Action H)(L:G.Arrival S Ω Pn)
def DualR :Prop := ∀ x y:D, inner ℂ (E (A x)) (E y) = inner ℂ (E x) (E (B y))
abbrev QuietM(A:X):= DualR S Ω G A A
local notation "T₂"=> DualR S Ω G
variable {Z W:Effort S Ω G}
lemma twoSide (q:DualR S Ω G A B): T₂ B A:=by
 intro x y; rw [← inner_conj_symm,← inner_conj_symm (E x),q y x] -- rewrite direction inspect
lemma cash (v:T₂ A B)(ρ:ℂ): T₂ (ρ•A) (star ρ•B):=by
 intro z p; simp only [LinearMap.smul_apply, map_smul,inner_smul_left,inner_smul_right]; rw [v z p]; rfl
lemma both (v:T₂ A B)(y:T₂ Z W): T₂ (A+Z) (B+W):=fun x q=>by simp only [LinearMap.add_apply,map_add,inner_add_left,inner_add_right,v x q,y x q]
lemma exhibit (h:T₂ A B)(z:T₂ Z W): T₂ (A*Z) (W*B):=fun x y=> (h (Z x) y).trans (z x (B y))
include L
lemma uniq_δ (t:T₂ A B)(q:T₂ A Z): Z=B:=by ext1 x; apply lensI G S Ω; apply L.dense.eq_of_inner_right ℂ; intro y; exact (q y x).symm.trans (t y x) -- inner eq shape
lemma reserve (v:A∈ Hull S Ω G J U): ∃ B:X, B∈ Hull S Ω G J U∧ DualR S Ω G A B:=by
 apply Algebra.adjoin_induction (s:= (G.conduct S Ω) '' (RToken G J U)) (x:=A) (p:=fun t _=>∃ B:X,_∧ T₂ t B) _ _ _ _ v
 · rintro z ⟨j,t,rfl⟩; refine ⟨G.conduct S Ω (G.reve j),seeds S Ω G J U _ ⟨t.1,?_⟩, L.hermitian j.1 j.2⟩; -- membership tsupport bar
   have he: Function.support (Probe.bar j.2)=Function.support j.2 := by ext x; simp [Function.mem_support];
   have hd: tsupport (Probe.bar j.2)=tsupport j.2:= congrArg closure he; change IsCompact _∧ _; change IsCompact (tsupport (Probe.bar j.2)) ∧ tsupport (Probe.bar j.2) ⊆ U; rw [hd]; exact t.2
 · intro r; rw [Algebra.algebraMap_eq_smul_one]; refine ⟨star r • 1,(Kₐ J U).smul_mem ( (Kₐ J U).one_mem) _,cash S Ω G _ _ ?_ r⟩; intro x y; rfl
 · rintro A B p r ⟨q,k,h⟩ ⟨v,W,e⟩; exact ⟨q+v,(Kₐ J U).add_mem k W, both S Ω G _ _ h e⟩
 rintro A B p r ⟨q,k,h⟩ ⟨v,W,e⟩; exact ⟨v*q,(Kₐ J U).mul_mem W k, exhibit S Ω G _ _ h e⟩
-- Local comm.P
abbrev separated(U V:Set E4):Prop:= ∀ x∈U,∀ y∈V,x-y∈_root_.YM.Mink.spacelike
lemma apart (p:separated U V)(q:A∈ Hull S Ω G J U)(v:B∈ Hull S Ω G K V): Commute A B:=by
 apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute v
 rintro a ⟨t,u,rfl⟩; apply Commute.symm; apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute q; rintro a ⟨s,b,rfl⟩; exact (L.localC s.1 t.1 s.2 t.2 (fun x d y r=>p x (b.2.2 d) y (u.2.2 r))).symm
-- graph closable sequential. enough metric first count
variable (v:A∈ Hull S Ω G J U)
include v
lemma final (x:ℕ→ D)(y:H)(h:Tendsto (fun i=>E (x i)) atTop (𝓝 0))(u:Tendsto (fun i=>E (A (x i))) atTop (𝓝 y)): y=0:=by
 -- include v
 obtain ⟨B,p,e⟩:= reserve S Ω G J U A Pn L v; apply L.dense.eq_of_inner_left ℂ; intro z; rw [inner_zero_left]; let Z:= E (B z); let f(i):= inner ℂ (E (x i)) Z; apply tendsto_nhds_unique_of_eventuallyEq ( u.inner (tendsto_const_nhds (x:=E z))) (show Tendsto f atTop (𝓝 0) from ?_)
 exact Eventually.of_forall fun i=> e _ _
 simpa only [f, inner_zero_left] using h.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=Z))
-- transfer locality frame. include in next.
#print axioms exhibit
#print axioms reserve
#print axioms final
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
