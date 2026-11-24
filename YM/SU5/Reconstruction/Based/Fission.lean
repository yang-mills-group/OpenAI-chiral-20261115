import YM.SU5.Reconstruction.Based.Session
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
set_option quotPrecheck false
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
open SlabMark Finset Fock Lat Laurent Cube Spire Vale Pastry Peaks Dial Phase Lifted Skye Tenant Rush Tulip Girt Scree RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
namespace LineCharge
-- the ACTUAL gauge lack-of-factorization tested on PERSISTENT PROFILE. Not claiming lack
-- of gauge covariance for the total probes, nor separate advancing of operands at overlap.
open Rooted
variable {k0:ℕ} (b:SU.Slot)(w:Fin k0→ Cover)(S:Finset Cover)
variable {J : Calibration}{μ ν : Multiset Cover}
noncomputable def bareHop (b:SU.Slot)(w:Fin k0→ Cover)(S:Finset Cover)(μ:Multiset Cover)(x:Dome J) := ∃ l:List (Fin k0),l≠ [] ∧ l.Nodup∧Rooted.Stitches J (Window.family b) w S (removal J) (creation J) l μ x.val
noncomputable def gaugeProbe (J:Calibration)(S:Finset Cover)(x:Dome J) := ∃f, Coeff false S f∧ x.val=scalar J f
noncomputable def bareAndGauge (μ:Multiset Cover)(v:Dome J):Prop:= ∃ a g:Dome J,bareHop b w S μ a∧ gaugeProbe J S g ∧ v=g*a
lemma bare_span{v:Dome J}(p:v.val∈ raw S J (Window.family b) w μ): v∈ Submodule.span ℂ {v:Dome J| bareAndGauge b w S μ v}:=by
 let T:=Submodule.span ℂ {v:Dome J | bareAndGauge b w S μ v}; let L: Dome J →ₗ[ℂ] Family J:=(screenHall J).val.toLinearMap
 let P:= T.map L; suffices e: raw S J (Window.family b) w μ ≤ P by obtain ⟨y,v,h⟩:= Submodule.mem_map.mp (e p); exact (Subtype.ext h) ▸ v -- v shadow
 apply Submodule.span_le.mpr; rintro A ⟨l,t,u,p⟩; suffices h:Rooted.scene S J (Window.family b) w l μ (removal J) (creation J) (scalar J) ≤ P from h p
 apply Submodule.span_le.mpr; rintro _ ⟨f,y,r,b,rfl⟩; let x':Dome J:=⟨f,aux_test (r.gives.inTest.widen)⟩; let g:Dome J:=⟨scalar J y,aux_test ((InTest.seed («K»:=J) b).widen)⟩
 exact Submodule.mem_map.mpr ⟨g*x',Submodule.subset_span (show _∈ _ from ⟨x',g,⟨l,t,u,r⟩,⟨y,b,rfl⟩,rfl⟩), rfl⟩

variable (s:ℕ)
variable (j:Axis)(C:Arena Y H G.history.circuit j 0 false)(χ:displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ]ℂ)(p q:Cover)
local notation "κ"=>sameRead Y H V G j C χ s
local notation "B" t:max=> streetBox (tent Y H) t S
local notation "P₀"=> reflectedBox j 0 (streetBox (tent Y H) p S)
local notation "Θ" => FirstWindows.leg (J:=tent Y H) j p
local notation "Θ'" => reposition (tent Y H) q
local notation "F"=> oneAt Y H V G j C χ s
-- find some definite charged profile AND some fiscal decomposition which cannot be factored
-- design just NoDecompose plus extra fields; onsite intensity persistence supported CP1
lemma split_price {x y : Dome (tent Y H)} (t: x.val∈ raw S (tent Y H) (Window.family b) w μ)(u:y.val∈ raw S (tent Y H) (Window.family b) w ν)(v: κ (FirstWindows.twin j p q x y)≠0):
   ∃ a b' g g':Dome (tent Y H), bareHop b w S μ a∧ bareHop b w S ν b'∧ gaugeProbe K S g∧ gaugeProbe K S g'∧ κ (FirstWindows.twin j p q (g*a) (g'*b')) ≠ 0:=by
 by_contra h; push Not at h
 apply v; let Q(x y:Dome (tent Y H)):= (Θ x)*(Θ' y); change κ (Q x y) = _
 have he(z:Dome (tent Y H)): κ z=F z:=os_ticket_val Y H V G j C χ s z _
 rw [he]; refine Submodule.span_induction (p:=fun x _=> F (Q x y)=0) (fun g p'=>?_) ?_ ?_ ?_ (bare_span b w S t)
 · refine Submodule.span_induction (p:=fun y _=> F (Q g y)=0) (fun w' hw=>?_) ?_ ?_ ?_ (bare_span b w S u)
   · obtain ⟨g₁,g₂,xh,h2,rfl⟩:=p'; obtain ⟨y₁,y₂,yh,h',rfl⟩:=hw; rw [←he]; exact h g₁ y₁ g₂ y₂ xh yh h2 h'
   · unfold Q; rw [map_zero,mul_zero,map_zero]
   · intro _ _ _ _ t v; unfold Q at *; rw [map_add,mul_add,map_add,t,v,zero_add]
   intro _ _ _ t; unfold Q at *; rw [map_smul, Algebra.mul_smul_comm, map_smul,t,smul_zero]
 · unfold Q; rw [map_zero,zero_mul,map_zero]
 · intro _ _ _ _ t v; unfold Q at *; rw [map_add,add_mul,map_add,t,v,add_zero]
 intro _ _ _ t; unfold Q at *; rw [map_smulₛₗ,Algebra.smul_mul_assoc,map_smul,t,smul_zero]

variable (o:Cover)(a d:ℕ)
local notation "R"=> booty o d a
lemma bare_no_decompose {x y : Dome (tent Y H)} (t: x.val∈ raw S K (Window.family b) (booty o d a) μ)(u:y.val∈ raw S K (Window.family b) (booty o d a) ν)
    (v: κ (FirstWindows.twin j p q x y)≠0)(g:Injective (booty o d a))(k':Disjoint (reflectedBox j 0 (streetBox (tent Y H) p S)) (streetBox (tent Y H) q S)):
     ∃ g l z z', NoDecompose Y H V G j C χ s p q b a d S o g l z z'∧ bareHop b (booty o d a) S μ g∧ bareHop b (booty o d a) S ν l:=by
 obtain ⟨x,y,F₁,F₂,e,w,f,f',pz⟩:= split_price Y H V G b (booty o d a) S s j C χ p q t u v
 have he {u:Multiset Cover} {x:Dome (tent Y H)}(h:bareHop b R S u x):x.val∈ Lode K (Window.family b) R S:= (by obtain ⟨v,p,q,z⟩:=h; exact Submodule.subset_span (show x.val∈ _ from ⟨v,p,q,z.gives⟩))
 have hx:= he e; have hy:= he w
 have hp: κ (FirstWindows.twin j p q x y)=0:=by
    rw [pigment_here]; exact Selected.remote_cold Y H V s G.history G.clipped j C χ q _ k' (mirror K j 0 (cad K ordinate p x.val)) (axial K j 0 (street_narrow p ordinate (Lode_test (S:=S) (W:=Window.family b) (b:=R) hx)).widen) R g (Window.family b) y.val hy
 refine ⟨x,y,F₁,F₂,⟨hx,hy, f,f', hp,?_⟩, e,w⟩; rw [hp,zero_mul,sub_zero]; exact norm_pos_iff.mpr pz
end LineCharge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LineCharge.bare_no_decompose
