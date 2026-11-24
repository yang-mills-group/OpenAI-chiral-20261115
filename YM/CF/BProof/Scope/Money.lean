import YM.CF.BProof.Seam.Transfer
/- enlarged probe mapping price from near micro. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Scope
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
open Seam Moment Push.AbsoluteSums Branch Tenant
lemma groveloc {μ:Support (More N)}(p:Branch.Grove (terr (More N)) μ):Micro.Loc μ:=fun i x j y=>Branch.rooted p i x j y
lemma hot_up {μ:Support (More N)}{k:ℕ}(p:House.Seek mH μ k)(e:ℕ): House.Seek mH (Lattice.halo e μ) k:= by
 obtain ⟨⟨x,h,o,h'⟩,p,q⟩:=p; exact ⟨⟨_,Lattice.halo_subset e μ h,o,h'⟩, Micro.halo_loc e p,q⟩
variable (m u:ℕ)
abbrev acL(u k τ σ:ℕ):= House.upward τ k σ 8 *(u+u+1)^4 -- tune volume
abbrev ac := acL u Y.hall.k Y.hall.X.size m
abbrev total(m:ℕ)(k A:ℕ)(μ:ℝ) := TT m k 8 A μ 4
variable {I:Type}[Fintype I]{Λ: I→ Finset (House.Block Y.yard Y.c')}{J:I→Support (More N)}{k:ℕ}
variable (p: I→ℝ) -- tune θ shadow above
structure Adept (p: I→ℝ)(α ξ:ℝ)(k:ℕ)(e:ℕ)(J:I→Support (More N)) (X:I→ Finset (House.Block Y.yard Y.c')) : Prop where
 moves : Toll J p (3*α) ξ
 seekL(i)(v:p i≠0): Seek mH (J i) k
 queue(i)(v:p i≠0): ∃ Q: House.Queue mH g₀ Y.hall (Lattice.halo e (J i)) m 8,X i=Q.Z
variable {α ξ:ℝ} (h:Adept Y m p α ξ k u J Λ)(g:Mapping.Factor Y.g.count.val (House.up 8) (ac Y m u) α 4)(kw:2*k+1<Y.yard.long)
include h g kw
lemma mScope: Toll Λ p 4 (ξ*total Y.yard.short k Y.g.count.val α) :=by
 let b:= House.Bed mH Y.c'; let x:= addr mH g₀; let V (i:Seat N):= ∃ j,Y.yard.Vic j k (time i); apply Mapping.Factor.grant («B»:=b) (f:=x) (S:=J) _ _ _ _ _ _ _ _ _ g h.moves (budget_nonneg (h.moves.pays 0)) V _ ?_ ?_ -- Shape
 · intro j; convert! senior mH g₀ k j kw using 2; congr! 1; unfold V x; tauto
 · intro i v; obtain ⟨Q,q⟩:=h.queue i v; rw [q]; let e:ℕ:= (J i).card; let L:= (u+u+1)^4; apply le_trans Q.bound; have ht:= Lattice.Corona.halo_size (J i) u; apply le_trans (b:= fourBill 8 * (7^4*Y.g.count.val+ House.rate Y.hall.X.size Y.hall.k m *(e*L))) _; apply le_of_eq; unfold L e ac acL upward House.up; ring; gcongr -- tune
 · intro i u'; obtain ⟨x,t,p,z⟩:= (h.seekL i u').near; obtain ⟨Q,q⟩:=h.queue i u'; rw [q]; refine ⟨Q.funds,x,t,⟨p,z⟩,Q.lunch (Grid.to_collar _ _ (Grid.to_collar _ _ (mem_image_of_mem (addr mH g₀) (Lattice.halo_subset _ _ t))))⟩
end YM.CF.BProof.Scope
