import YM.CF.BProof.Scope.Air
/-! Scope geometry for truncated (∆^print) and corrected entries.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Prime
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye Seam
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
local notation "rawK"=> rawG Y P T θ
local notation "K_"=> Y.hall
open Hero Mark
open Spin Dream Fock Dial -- fix
set_option maxHeartbeats 260000
local notation "Ζ_"=>framesL Y P T θ
local notation "CC"=>Y.yard.long
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Orbit N → Pane N) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E T θ Δ U ν δ} (Z : School Y T θ E Δ U ν δ rB)
open Scope Moment Push.AbsoluteSums
local notation "μz"=> Z.μwage
variable (k ξ:ℕ) -- near depth, and size cutoff in F support
abbrev TimeA(ξ k:ℕ):= k+2*ξ
abbrev TimePlus (μ:ℕ):= k+2*ξ+μ
structure Clock : Prop where -- extent field readiness. k≥1 & beyond all existing Mark tests
 carries : Δ.clock.nearM ≤ k
 pos : 1≤k
 tall : (TimePlus k ξ Z.μwage)*10+10≤Deep.D Y.yard
 count : TimePlus k ξ Z.μwage +10 ≤ Y.g.count.val
 -- use these to show both visibility and comparison on Mark Belt etc.
variable (J: Clock Z k ξ)
-- does Z determine Setup? yes.
local notation "C'"=> Z.stageU
local notation "Ψ"=>Pouch Y P T θ
namespace Clock
include J
lemma deep : TimePlus k ξ Z.μwage < Deep.D mH:=by have := J.tall; omega
lemma commuter(s:ℕ)(h:s≤ TimePlus k ξ Z.μwage) : 2*s+1<Y.yard.long :=by have := Deep.D_le mH; have := J.tall; omega
lemma height: k<Deep.D mH :=by let A:=J.deep Z k ξ; unfold TimePlus at A; omega -- tune
variable {μ:Support (More N)}(p:Micro.Loc μ){o:Seat N}(q:o∈μ)(uL:Air.atFall Y k μ)(tμ:μ.card ≤ ξ)
include p q uL tμ
lemma anchor : Anthem.Manus.Shallow mH (k+ξ) o:= by
 obtain ⟨s,l,g,v⟩:= Air.atFall_on k J.pos (show μ.Nonempty from ⟨o,q⟩) uL p; refine ⟨g,Trek.along_t mH s o g v ?_⟩; exact (Micro.span_dist p l q).le.trans tμ -- notation Manus
lemma paysL {i:Seat N}(l:i∈Lattice.halo Z.μwage μ): Anthem.Manus.Shallow mH (TimePlus k ξ Z.μwage) i ∧ addr mH g₀ i∈ ray mH (πX o) 1:=by
 let v:=μz; obtain ⟨j,u⟩:= J.anchor Z k ξ p q uL tμ; let K:= TimePlus k ξ μz; have hk:= J.commuter Z k ξ K (le_refl K); obtain ⟨a,t,l⟩:=Lattice.halo_spec.mp l; have ht:separation o i ≤ ξ+μz := (separation_triangle o a i).trans (Nat.add_le_add ((Micro.span_dist p q t).le.trans tμ) l); have hK: k+ξ+(ξ+v)=K:=by unfold K TimePlus v; omega -- v appear
 have hv:Y.yard.Vic j K (time i):= by rw [←hK]; exact Trek.along_t mH o i j u ht
 have h : Trek.tag mH o=Trek.tag mH i:= (Posts.vic mH j _ (by unfold K TimePlus at hk; omega : 2*(k+ξ)+1<Y.yard.long) u).trans (Posts.vic mH j _ hk hv).symm; refine ⟨⟨j,hv⟩,Seam.germ Y h (by rw [one_mul]; apply ht.trans; have ht:= J.count; unfold TimePlus at ht; omega)⟩ -- tag amb
lemma licenses (Φ:Finset (House.Block Y.yard Y.c'))(v':ray mH (πX o) 9 ⊆ Φ): Probe Y P T θ Φ (Lattice.halo Z.μwage μ):=by
 let K:=TimePlus k ξ μz; apply paidSong Y P T θ _ (gE o) (J.deep Z k ξ) Φ; all_goals intro t v; obtain ⟨⟨i,p⟩,a⟩:= paysL Z k ξ J p q uL tμ v
 · rw [← bit_first Y o, ← ((House.ray_spec ..).1 a).2]; rw [show House.one mH (addr mH g₀ t)=i from Posts.vic mH i _ (J.commuter Z k ξ K (le_refl _)) p]; exact p
 intro i u; exact v' (Cabinet.ray_net Y _ _ a u) -- tune
end Clock
end YM.CF.BProof.Prime
