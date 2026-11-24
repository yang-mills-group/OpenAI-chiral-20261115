import YM.SU5.Relativistic.RopeBraiding
set_option autoImplicit false
set_option synthInstance.maxSize 25000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
namespace FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H a b I E)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{i k:ℕ→ℕ}(Q:Coherent Y H (i:=a) (k:=b) (E:=E) D i k)
variable (u:ℕ→ℕ)(T:ℕ→ Bool→Family (tent Y H)→Family (tent Y H))(t:GradesAll (i:=a) (a:=i) (k:=b) (b:=k) Y H u T)
local notation "W"=> wingspan Λ l



variable (j:Axis)(z:ℤ)
namespace Lariat
section shadow
local notation "a"=> (plane j 0).motion
local notation "M" t:max=> (plane j t).motion
lemma zoom (S:Finset Cover)(r h:ℕ): Satin.liner ((reflectedBox j z S).image (fun i=>r • i)) h=reflectedBox j (r*z) (Satin.liner (S.image (fun i=>r • i)) h) :=by
 have p'(i):i∈Lattice.box h→ a i ∈Lattice.box h:=by
    intro u; obtain ⟨w,o⟩:= box_test.mp u; apply box_test.mpr; constructor <;> intro v<;> rw [fling_move]<;> split_ifs <;> have g:= w v <;>have p:=o v <;> omega
 have he(x y:Cover): (M ((r:ℤ)*z)) (x+r • y)=a x+r • (M z) y:=by
    funext t; simp only [fling_move,Pi.add_apply,Pi.smul_apply]; simp only [nsmul_eq_mul]
    split_ifs<;>ring
 apply Finset.Subset.antisymm
 · intro i p; obtain ⟨s,h0,vv⟩:= mem_biUnion.mp p; obtain ⟨x,u,rfl⟩:= mem_image.mp h0; obtain ⟨x,k,rfl⟩:= mem_image.mp u; obtain ⟨v,t,rfl⟩:=mem_image.mp vv
   have hv:a (a v)=v:=by ext p; simp only [fling_move]; split_ifs<;>ring
   let V:= a v+r • x
   refine Finset.mem_image.mpr ⟨V, Finset.mem_biUnion.mpr ⟨_, Finset.mem_image_of_mem _ k, Finset.mem_image_of_mem _ (p' v t)⟩,?_⟩ -- typing last maps
   unfold V; rw [he,hv]
 intro i w; obtain ⟨x,t0,rfl⟩:= mem_image.mp w; obtain ⟨p,h,w⟩:=mem_biUnion.mp t0; obtain ⟨x,t,rfl⟩:= mem_image.mp h; obtain ⟨i,v,rfl⟩:=mem_image.mp w
 rw [he]; exact mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem (fun i:Cover=>r • i) (Finset.mem_image_of_mem _ t),Finset.mem_image_of_mem _ (p' i v)⟩
end shadow
variable (s:ℕ) {n:ℕ}
lemma shades (f:Lariat (tent Y H) n): (turned Λ j z f).box Λ l= reflectedBox j (planeAt z Λ.R.L n) (box Λ l f):=by
 induction f with
 | start f=> rw [planeAt,pow_zero,one_mul]; rfl
 | @stretch n f g ih=>
    change W ((turned Λ j z f).box Λ l) ∪ (mate j (planeAt z Λ.R.L (n+1)) g).S=_
    rw [ih, box,←step_plane]; unfold wingspan; rw [Lariat.zoom j (planeAt z Λ.R.L n)]; exact (Finset.image_union ..).symm
lemma costsOpposed {f g:Lariat (tent Y H) n}(p:f.ordains (Λ:=Λ) l s j z)(u:g.ordains (Λ:=Λ) l s j z): standoff Λ l (turned Λ j z f) g:=by
 induction f with| start f=> cases g; trivial| stretch f a ih=> cases g with| stretch g b=> apply And.intro (show standoff Λ l (turned Λ j z f) g from ih p.1 u.1); apply Eq.mpr (congrArg (fun Z=>Detached Λ l Z (box Λ l g)) (shades Y H j z f)); exact mirror_detached Λ l (placedRoom Y H s _ p.1) (placedRoom Y H s _ u.1)
lemma physicalBill {f:Lariat (tent Y H) n}{V:Set RSpace}(p:f.stamps (Λ:=Λ) l s V): SupportedPhysically Λ l (s+n) (box Λ l f) V:=by
 induction f with| start f=>exact p| @stretch n f g ih=> have h:= ih p.1; have hp: SupportedPhysically Λ l (s+n+1) (wingspan Λ l (box Λ l f)) V:= SupportedPhysically.step h; exact physPlus hp p.2
where physPlus {S T:Finset Cover} {i:ℕ}{Λ: Preparation}{l:ℕ} {V: Set RSpace} (h:SupportedPhysically Λ l i S V)(p:SupportedPhysically Λ l i T V):SupportedPhysically Λ l i (S∪T) V:=by intro x t; exact (mem_union.mp t).elim (h x) (p x)

end Lariat

end FermionSlab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
