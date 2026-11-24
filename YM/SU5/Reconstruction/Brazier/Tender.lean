import YM.SU5.Reconstruction.Brazier.Fervent
/-! Bank on sets of supports using this home.Storm estimate.Translates beyond EVERY horizon, just one gate pair, true valuation costs on gauge etc. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
namespace Fervor
open Tarmac Hearth
local notation "σ"=> driveAlgebra Y H V G.history G.clipped j false C
local notation "Z₀"=> reduceToDisplay Y H V G.history G.clipped j false C
variable (w:ℕ)(T:Finset Tarmac)(p:∀ a∈T,Tarmac.Stage Λ l j a w)
local notation "Xφ"=>credit Y H V G Z j C
lemma assist : ∃ w:ℕ,0<w ∧ ∀ a∈ T,Tarmac.Stage Λ l j a w:= ( (eventually_gt_atTop 0).and ( (eventually_all_finset _).mpr fun (a:Tarmac) (_:a∈T)=> (Tarmac.allStage (Λ:=Λ) (l:=l) j a))).exists -- tune order
include p
lemma compact_catalog : ∃ S:Set (driveAlgebra Y H V G.history G.clipped j false C),IsCompact S ∧ ∀ a,∀ h:a∈T,∀ x:Cloud (Dome (tent Y H)),∀ hx:Pocket (tent Y H) a.book a.roof 1 x, Xφ (p a h) hx∈S:=by
 classical
 choose U t z using fun a:{i:Tarmac// i∈ T}=> stage_hold Y H V G Z j C 1 (p a.val a.property)
 refine ⟨⋃ i,U i,isCompact_iUnion t,fun a u x hx=>?_⟩
 exact Set.mem_iUnion.mpr ⟨⟨a,u⟩, z ⟨a,u⟩ x hx⟩
omit p
/-- every designated bill fits; height in TWO units physically paid beyond any requested sterile radius, and meeting budgets of chronology pair. -/
structure Station (r:Hearth Y H G j)(Hₜ:ℝ)(a:Tarmac) (w:ℕ): Prop where
  gap : (lantern Λ a.roof w:ℝ) + Hₜ < (r.height:ℝ)
  standby : Tarmac.Stage Λ l j a w
  strict : lantern Λ a.roof w < r.height
  futureEntry : a.roof < r.roof
structure Sightline (r:Hearth Y H G j)(Hₜ:ℝ)(a:Tarmac) : Prop where
  future : Disjoint (a.land Λ l) (flank j r.height ∪ mirrorE j 0 '' flank j r.height)
  room (x:RSpace)(p:x∈ a.land Λ l) : x j + Hₜ < r.height ∧ -(r.height:ℝ)+Hₜ<x j
  later : a.roof < r.roof
lemma Station.clearance {a:Tarmac}{g:ℝ}{w:ℕ}{r: Hearth Y H G j}(p:Station Y H G j r g a w) : Sightline Y H G j r g a:=by
 refine ⟨r.with_support Y H G j p.standby p.strict,fun x u=>?_,p.futureEntry⟩; have ht:= p.standby.fits u
 rw [← lantern_clock] at ht; have h:= p.gap; constructor <;> linarith [ht.1,ht.2]
lemma overhead (B':ℕ)(d:ℝ)(b:0<d) : ∃ (k:ℕ)(M':ℕ), B' ≤ k ∧ d < (lantern Λ 0 M':ℝ) ∧ ∀ a∈T,a.roof ≤ k ∧ (lantern Λ a.roof w:ℝ)+d < (lantern Λ 0 M':ℝ):=by
  let k:= max B' (T.sup Tarmac.roof)
  obtain ⟨i,hx,hy⟩:= ((lanterns (Λ:=Λ) 0 d).and ( (eventually_all_finset T).mpr fun a _=> lanterns (Λ:=Λ) 0 ((lantern Λ a.roof w:ℝ)+d))).exists
  exact ⟨k,i,le_max_left ..,hx,fun a u=> ⟨ (Finset.le_sup (f:=Tarmac.roof) u).trans (le_max_right ..), hy a u⟩⟩
-- Character budget at that bill-algebra.Pack
noncomputable def receives (s:ℕ) : Cloud (Dome (tent Y H)) →ₗ[ℂ] ℂ := (oneAt Y H V G j C χ s).comp (vistaFinish Y H s Z)
local notation "Ξ"=> receives Y H V G Z j C χ
local notation "Λ₀"=> vistaTake Y H Z
local notation "Sp" r:max=> Hearth.spanMark Y H G j r
abbrev BoundBooks (M:ℝ): Prop:= ∀ a∈T,∀ x: Cloud (Dome (tent Y H)),Pocket (tent Y H) a.book a.roof 1 x→ ‖Ξ a.roof x‖≤M -- notation M removed!
structure Challenge (r:Hearth Y H G j) (g d:ℝ) : Prop where
 full (a) : a ∈ T→ Station Y H G j r g a w
 height : g < (r.height:ℝ)
 valFee : ‖ vistaTake Y H Z (r.spanMark Y H G j)-1‖≤ d
 era : ∀ a∈ T, ∀ x: Cloud (Dome (tent Y H)), Pocket K a.book a.roof 1 x→ ‖vistaTake Y H Z (x*spanMark Y H G j r)- receives Y H V G Z j C χ a.roof x‖ ≤ d
local notation "χc"=> Challenge Y H V G Z j C χ
include p
lemma afforded : ∃ M:ℝ,0 ≤ M∧ BoundBooks Y H V G Z j C χ T M ∧ ∀ d g :ℝ,∀ b':ℕ, 0<d→0<g→∃ r:Hearth Y H G j, b'≤ r.roof ∧ Challenge Y H V G Z j C χ w T r g d:=by
 obtain ⟨S,s,h⟩:= compact_catalog Y H V G Z j C w T p
 obtain ⟨n,a,m⟩:= ranges Y H V G j C χ S s
 refine ⟨n,zero_le_one.trans a, fun a ha x hx=> ?bound,fun d g b' e v=>?_⟩
 case bound=> change ‖oneAt Y H V G j C χ a.roof ((Kx a.roof) x)‖≤n; rw [← Tarmac.pays_character Y H V G Z j C χ (p _ ha) hx]; exact (m _ (h a ha x hx)).2
 obtain ⟨c,f,l,o,z⟩:= overhead (Λ:=Λ) w T b' g v
 obtain ⟨r,hr,hl,y⟩:= planting Y H V G j C χ S s d e (lantern Λ 0 f) (show 0 < lantern Λ 0 f from show (0:ℝ)<(lantern Λ 0 f:ℝ) from v.trans o) c
 have hx(x:Tarmac)(k:x∈T): Station Y H G j r g x w:= by
    have hz:(lantern Λ x.roof w:ℝ)+g< (r.height:ℝ):=hr.symm ▸ (z x k).2; exact ⟨hz,p x k,show (lantern Λ x.roof w:ℝ)< (r.height:ℝ) from (lt_add_of_pos_right _ v).trans hz,(z x k).1.trans_lt hl⟩
 refine ⟨r,l.trans hl.le,⟨hx,(by rwa [hr]),?_,?_⟩⟩
 · rw [selfPay]; let H':= advance Y H V G.history.circuit j 0 false C ( (r.height:ℝ).toNNReal) (r.home Y H V G j C)
   have ht : ‖inner ℂ H' ((1:(A).Op) H')-χ (Z₀ (1:σ))‖≤ d:= y 1 (Set.mem_insert ..) ((r.height:ℝ).toNNReal)
   rw [reduce_origin, map_one,show (1:(A).Op) H'=H' from rfl,inner_self_eq_norm_sq_to_K] at ht -- `rw selfPay` implicits trouble
   rw [Complex.ofReal_pow]; exact ht
 intro a ha x p'
 let M:= Xφ (p _ ha) p'
 have hm:= y M (Set.mem_insert_of_mem _ (h a ha x p'))
 rw [purchase Y H V G Z j C r (p a ha) (hx a ha|>.strict) p']
 change ‖inner ℂ _ (M.val _)-oneAt Y H V G j C χ a.roof ((Kx a.roof) x)‖≤ d
 rw [←pays_character Y H V G Z j C χ (p a ha) p']; exact hm _
end Fervor
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
