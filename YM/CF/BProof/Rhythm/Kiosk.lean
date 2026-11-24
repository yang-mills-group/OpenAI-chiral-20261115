import YM.CF.BProof.Rhythm.Fix
/-! Constructions for any such Room, including homogeneous reference. Expose maps to Shelf. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Rhythm
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Hearth Trek
open RG Wilson Mapping.House Pricing Gates.Stage Gates.Stage.Setup Skye Tape
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r:ℝ}{D₀:Spin.Ready j a b l r}{u:ℝ}(E: Essence D₀ u)
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a':ℕ}{s:Side}{m:ℕ}{y:ℝ}(F:Entice S L a' m y)(Y:Setup S L a' (More s) m y)
variable {rₜ:ℕ}(Δ:Note E (Gates.gap L a') rₜ) (X:Season E rₜ L a' Δ y m (S:=S))
variable (B:Blocks Y.yard Y.c'){n:Side}{g:Ratio n (More s)} -- missing n
local notation "Y₀"=> Y.yard
local notation "J"=> Y.g
local notation "S₀"=> Δ.clock

include X F
lemma Instructions : Pad Y₀ E.H Δ.clock Y.g.count.val ∧ Sound Y₀ E.H Δ.clock (Lease.wearC S y) ∧ 2*Y.yard.short≤Y.yard.long:=by
 have ht:= Lease.wear_p (y:=y) S; have hx:= X; refine ⟨⟨?_,?_⟩,⟨ht,?_,X.old,?_,Δ.bound⟩,?_⟩; rw [Setup.length F Y]; exact X.long; rw [Y.space]; exact X.arrows; rw [Y.width]; exact X.focal; rw [Y.width]; exact X.fund; rw [Y.width,Setup.length F Y]; exact X.outside
variable {n':Side}{U V:Bkg (More s)}{D:Script Y.yard}{δ:ℝ}(G:Trek.Lamp (Y:=Y.yard) Δ.clock Y.g B δ U V)(P:Permit D Δ.clock U Y.g B (Lease.wearC S y))(T:4 ≤ n.val)(W:g.count=E.H.whole)
include G P W T
lemma rideH (i:Site (More s)): Money (D.HH Δ.clock J B V g i):=(P.HPort D Δ.clock Y.g B V g (Instructions E F Y Δ X).1 T W G (Instructions E F Y Δ X).2.1 i).1
-- measurable proof kept independent this instance, use lemma Shelf.
abbrev track : Skein s rateH:= Tape.drawB (D.HH Δ.clock Y.g B V g) (rideH E F Y Δ X B G P T W)
-- include variables syntax for definition depending proof? `include` only Lemmas. define with terms
-- light evidence can use equal in Eq hak
lemma stands(Q:Skein s rateH)(p: Q=track E F Y Δ X B G P T W): Tape.Lease E.pre Δ.stage (Pins Y₀ J B) ⟨V,G.year⟩ Q ∧
   (let m:= Q.val; Wick.Story (week m (true,false)) (week m (false,false)) (week m (true,true)) (week m (false,true))∧ week m (true,false) 0=postC (D.XX Δ.clock J B V g) ∧ Slow V (hook (D.XX Δ.clock J B V g)) u ∧ (roam m (false,false) 1=fun x=> D.HH Δ.clock J B V g x 2)):=by
 obtain ⟨K,M,he⟩:= Instructions E F Y Δ X; -- shadow name change
 have w(D':ℕ)(e:Y.yard.short=D')(K': Credit D₀ E.rad D')(q:K'.price=Δ.stage.price)(u:K'.reach=Δ.stage.reach): Tape.Lease E.pre K' (Pins Y₀ J B) ⟨_,G.year⟩ Q:=by
   subst D'; subst Q; apply P.LeaseP K T W G M (track E F Y Δ X B G P T W) (fun i z v=> Tape.pretty _ (rideH E F Y Δ X B G P T W) i z v) K' E.disk E.pre E.budget (q.symm ▸ X.innerp) X.hp he _; rw [u]; omega -- tune underscores
 exact ⟨w _ (Y.width) Δ.stage rfl rfl,P.readyStory K T W G M Q p⟩
end YM.CF.BProof.Rhythm
