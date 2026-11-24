import YM.CF.BProof.Scope.Money
import YM.CF.BProof.Seam.Door
set_option autoImplicit false
set_option synthInstance.maxSize 26000

noncomputable section
namespace YM.CF.BProof.Scope
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
open Seam Moment Push.AbsoluteSums Branch Tenant Account
-- weak on active grabs measurable restriction & extension. `Sees` defined over LN in Pulse
variable (u m:ℕ){I:Type}[Fintype I]
variable {k q:ℕ}
abbrev Total(Mu:Pouch Y P T θ→ℂ)(x:Pod Y):ℂ:= if h:Cabinet.Ready P Y T θ x then Mu ⟨x,h⟩ else 0
@[fun_prop] lemma Total_m(f:Pouch Y P T θ→ℂ)(h:Measurable f) : Measurable (Total Y P T θ f) := Measurable.dite h measurable_const (readyV ..)
-- congruent Teller.Val
variable (rB:ℕ){J:I→Support (More N)}
structure Chain (rB k μf:ℕ)(J:I→Support (More N))(p:I→ℝ)(C: I→ Pouch Y P T θ→ℂ)(ζ α:ℝ) : Prop where
 paid: Moment.Toll J p (3*α) ζ
 map(i)(h:p i≠0): Seek mH (J i) k
 cap i x:‖C i x‖≤p i
 meas i: Measurable (C i)
 ready i(h:p i≠0)(Λ)(q:Probe Y P T θ Λ (Lattice.halo μf (J i))) (a b:Pouch Y P T θ)(v:Esp Y rB Λ a.val b.val): C i a=C i b
variable (ζ α:ℝ){p:I→ℝ}{C:I→Pouch Y P T θ→ℂ}
variable (H:Chain Y P T θ rB k u J p C ζ α)
include H
lemma titan(g:Mapping.Factor Y.g.count.val (House.up 8) (ac Y 1 u) α 4)(kw:2*k+1<Y.yard.long): Nonempty (Account.Teller (gridBase wB) (Cabinet.Ready P Y T θ) (Esp Y rB) I (Total Y P T θ (fun x=> ∑ i,C i x)) 4 (ζ*total Y.yard.short k Y.g.count.val α)):=by
 -- choose arbitrary financial output
 choose! Λ q using fun i (v:p i≠0)=> (show ∃ Λ:Finset (House.Block Y.yard Y.c'),∃ Q:House.Queue mH g₀ Y.hall (Lattice.halo u (J i)) 1 8, Λ=Q.Z from by
   obtain ⟨Q⟩:= can mH g₀ Y.hall (Lattice.halo u (J i)) 1 (agenda P Y).fund k (hot_up Y (H.map i v) u) 8; exact ⟨Q.Z,Q,rfl⟩)
 have hv:Adept Y 1 p α ζ k u J Λ := ⟨H.paid,H.map,q⟩
 refine Account.Teller.weak (adm:=Cabinet.Ready P Y T θ) (agree:=Esp Y rB) (f:=Total Y P T θ (fun x=> ∑ i,C i x)) (fun i=>Total Y P T θ (C i)) Λ p (mScope Y 1 u p hv g kw) (fun i t=>?_) (fun i x g=>by unfold Total; rw [dif_pos g]; exact H.cap i _) (fun i h x z v l t=> ?_) (fun i=> Total_m Y P T θ _ (H.meas i)) (fun x t=> ?_)
 · obtain ⟨Q,a⟩:=q i t; rw [a]; obtain ⟨x,v,j,w⟩:= (H.map i t).near; exact ⟨⟨_,fundsDoor Y _ Q x (Lattice.halo_subset u (J i) v) (ray_home mH (Cabinet.roadB Y x) 8)⟩,Q.funds⟩
 · unfold Total; rw [dif_pos l,dif_pos t]; obtain ⟨Q,e'⟩:=q i h; exact H.ready i h Q.Z (paysLong Y P T θ _ Q) ⟨x,l⟩ ⟨z,t⟩ (e' ▸ v)
 unfold Total; simp only [dif_pos t]
-- alternative submit bigger parameter ζ α rate : stage focus; all conditions eventual.
end YM.CF.BProof.Scope
