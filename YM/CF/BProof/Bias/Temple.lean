import YM.CF.BProof.Rhythm.Kiosk
import YM.CF.BProof.Bias.Shack
/-! Reference is taken throughout every support formula on MD, same frames & phase on
Ω1 marks. Use actual layout with relative gauge. This supplies the second-price K^J.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
-- open namespaces *compat*, notably `rhythm` definitions
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Hearth Trek
open RG Wilson Mapping.House Pricing Gates.Stage Gates.Stage.Setup Skye Tape Rhythm
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r:ℝ}{D₀:Spin.Ready j a b l r}{u:ℝ}(E: Essence D₀ u)
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a':ℕ}{s:Side}{m:ℕ}{y:ℝ}(F:Entice S L a' m y)(Y:Setup S L a' (More s) m y)
variable {rₜ:ℕ}(Δ:Note E (Gates.gap L a') rₜ) (X:Rhythm.Season E rₜ L a' Δ y m (S:=S))
variable {n:Side}(g:Ratio n (More s)) (T:4 ≤ n.val)(W:g.count=E.H.whole) (δ:ℝ)(k:0≤δ)(x:δ ≤ E.H.calm) (z:Fin 5)
local notation "Y₀"=> Y.yard
local notation "J"=> Y.g
local notation "S₀"=> Δ.clock
local notation "DD"=> homeScript Y₀ z
lemma homerP (z:Fin 5): Trek.Permit (homeScript Y.yard z) Δ.clock 1 Y.g ∅ (Rhythm.Lease.wearC S y):= home_here Y.yard Y.g z _ _ (Rhythm.Lease.wear_p S).le
include k x in
lemma homerL : Trek.Lamp (Y:=Y₀) Δ.clock Y.g ∅ δ 1 1:= lampZ Y₀ J _ δ k x
abbrev homTrack := Rhythm.track E F Y Δ X ∅ (g:=g) (homerL E Y Δ δ k x) (homerP E Y Δ z) T W -- tune args
lemma sure : Tape.Lease E.pre Δ.stage (Pins Y₀ J ∅) ⟨(1:Bkg (More s)),guard0 k⟩ (homTrack E F Y Δ X g T W δ k x z):= (stands E F Y Δ X ∅ (g:=g) (homerL E Y Δ δ k x) (homerP E Y Δ z) T W _ rfl).1
variable (A:Core j a b l r s)(hE:E.pre.size≤s.val)(hz:δ ≤ E.pre.limit)
def claimH : Loft A δ Δ.stage.c rateH Δ.stage.η:= by
 let X':= (sure E F Y Δ X g T W δ k x z); exact ⟨_,X'.ride E.pre hE k hz A⟩ -- check ride syntax
lemma homCar : Tape.carried (claimH E F Y Δ X g T W δ k x z A hE hz).val.1=1:=rfl
lemma homP : Portrait z Y₀ (claimH E F Y Δ X g T W δ k x z A hE hz):=by
 let f:=claimH E F Y Δ X g T W δ k x z A hE hz; have he:=Rhythm.Instructions E F Y Δ X; refine ⟨⟨rfl,pinsB ..⟩,fun i a=>?_⟩ -- tune
 change Tape.roam (homTrack E F Y Δ X g T W δ k x z).val (false,false) 1 (node i)= _; rw [(stands E F Y Δ X ∅ (homerL E Y Δ δ k x) (homerP E Y Δ z) T W _ rfl).2.2.2.2]; obtain ⟨j,hj⟩:= (loom_s ..).1 ((row_at ..).1 a); have hx': node i∈ Y.yard.band j:=mem_strip.mpr hj
 dsimp only; rw [hom_H Y₀ J z S₀ g he.1 T W he.2.1 hx',←loom_b Y₀ hj]; split_ifs <;> rfl
-- receipt of all comparisons choose prechoice E.S Price. Scope before Seam; uniform
lemma aperture (d:1≤j): ∃ K p,0<p∧∀ z:Fin 5, ScopeP (Gates.gap L a') D₀ δ Δ.stage.c rateH p K z:= bought _ _ _ _ _ d Δ.stage.cE expenses.one -- tune
lemma afternoon {K:ℕ}{p:ℝ} (P:ScopeP (Gates.gap L a') D₀ δ Δ.stage.c rateH p K z) (p0:0≤ p)(b:2*K+1< Gates.DP L a' y) (s':K≤s.val) (u:z≠0) (r':4 ≤ m) (i:Block Y₀ Y.c'):
 let x:= claimH E F Y Δ X g T W δ k x z A hE hz; ∑ o ∈ CircleR Y.g Y₀ i K,Tape.bias x o ≤ -p/64*(Y.g.count.val:ℝ)^3 := by
 intro Z; apply shack Y.g Y₀ i z p Z P (homP ..) u p0 (E.pre.first _ hE A δ k hz) s' ?_ ?_ ?_; rw [Y.length F]; exact b; exact Y.width.le; rw [Y.space]; exact r'
end YM.CF.BProof.Bias
