import GaugeFieldConstruction.DoorCreek
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat
open Etch
namespace Weir
section weir
variable {K:Calibration}{I:Type*}{σ:Cover}{W:ℤ}{F:I→Family K}{o:I → Cover}{L J: List (Raft K I)}{m n:Side}{S:I→Finset Cover}
local notation "V"=> Vibro F o σ W n
def Flood (W:ℤ)(σ:Cover)(o:Cover)(F:Family K)(Y:Family K→ℂ)(n:Side)(c:ℝ):Prop:=∀ L:List (Raft K Unit), Vibro (fun _=>F) (fun _=>o) σ W n L→L.length=(n.val*2)^4→‖Y (wharf L)‖ ≤ c^((n.val*2)^4)
lemma Flood.dropper {i:I}{Y:Family K→ℂ}{c:ℝ}(q:Flood W σ (o i) (F i) Y n c)(g:V L)(t:L.length=(n.val*2)^4)(e:∀ x∈L,x.ink=i):‖Y (wharf L)‖ ≤c^((n.val*2)^4) :=by
 let f(a:Raft K I):Raft K Unit:=⟨a.posC,(),a.folio⟩
 let J:=L.map f
 have h: Vibro (fun _=>F i) (fun _=>o i) σ W n J :=by
    constructor
    · intro a p; obtain ⟨x,t,rfl⟩:=List.mem_map.mp p; rw[←e x t]; exact g.1 x t
    unfold J; rw[List.map_map]; exact g.2
 have ht:= q J h ((List.length_map ..).trans t)
 rw [show wharf J=wharf L from (by unfold wharf J; rw [List.map_map]; rfl)] at ht; exact ht
end weir
section note
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(s:ℕ)
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
variable {J:Type*}[Finite J]
variable {σ:Cover}{W:ℤ}{G G':J→ℝ}{o:J → Cover}{F:J→ℕ→Family (tent Y H)}{f:J→Family (tent Y H)}{S:J→Finset Cover}
-- any width; same pose wall moves
local notation "sf" e:max=> sharp Y H s (π e) (ζ e)
def SnowPrice (σ o:Cover)(W:ℤ)(F:ℕ→Family (tent Y H))(c:ℝ):Prop:=∀ᶠ r:ℕ in atTop, ∀ n:Side, LatticeFare K (m (π r) s) n W σ→ Flood W σ o (F r) (sf r) n c
variable (pu:∀ j,BQueue (S j) (F j) (f j))(h:∀ j,Barn (tent Y H) W σ (o j) (S j))
include V Q h pu
lemma hot_G (v:∀ j,0<G j)(t:∀ j,G j<G' j)(z: ∀ j, SnowPrice (i:=i) (k:=k) (a:=a) (b:=b) Y H s σ (o j) W (F j) (G j)):
 ∀ᶠ e:ℕ in atTop,∀ n:Side, LatticeFare K (m (π e) s) n W σ→∀ L:List (Raft K J),Vibro (fun j=> F j e) o σ W n L→ ‖hot Y H s (π e) (ζ e) (wharf L)‖ ≤ buoy G' L:=by
 letI:= Fintype.ofFinite J
 choose A1 a1 a2 a3 using fun j:J=> (pu j).bdd
 let c:= (∑ i, (G' i)⁻¹ +1)⁻¹ -- latter scope ambiguous tune
 have hg(j):0<G' j:=(v j).trans (t j)
 have u:0≤ ∑ i, (G' i)⁻¹:=Finset.sum_nonneg (fun i _=>(inv_pos.mpr (hg i)).le)
 have ht:0<c:=by unfold c; positivity
 have hc:c≤1:=by unfold c; rw[inv_le_one₀ (by positivity)]; linarith only [u]
 have hv(j):c≤G' j:= by
    rw[← inv_inv (G' j)]; exact inv_anti₀ (inv_pos.mpr (hg j)) ((Finset.single_le_sum (fun (i:J) (_:i∈univ)=> (inv_pos.mpr (hg i)).le) (mem_univ j)).trans (le_add_of_nonneg_right zero_le_one))
 let A:= (∑ i,A1 i)+1
 have hz:1≤ A:= le_add_of_nonneg_left (Finset.sum_nonneg (fun i _=>(a1 i).le))
 have y:∀ j,A1 j≤ A:=fun j=> (Finset.single_le_sum (fun i (_:i∈univ)=> (a1 i).le) (mem_univ j)).trans (le_add_of_nonneg_right zero_le_one)
 have ha:= (eventually_all.mpr a3).mono (fun e w i n x=> ((w i) n x).trans (y i)) -- tune
 filter_upwards [Q.finance s,eventually_all.mpr z,ha,eventually_all.mpr (fun j=> screenFlash Y H V s Q A (G j) (G' j) (zero_lt_one.trans_le hz) (v j) (t j))] with e E e₀ qu qr n B L P
 have D(j): InTest K true (S j) false (F j e):= (pu j).whereTo e
 unfold hot; rw [dif_pos E.depth]
 apply quake hz ht hc hv qu D h (boxprice Y H _ _ _ s E.fire E.enters) B _ P
 intro J V u i T
 let m':=(n.val*2)^4; have he:T₀ (π e) s =(K).c (m (π e) s):=(terrain ..).symm
 have hX: 0 < m':= by unfold m'; positivity
 have hp:n.val≤(T₀ (π e) s).val:=by
    rw[he]; exact_mod_cast (le_trans (le_of_eq (one_mul (n.val:ℤ)).symm) (le_trans (mul_le_mul_of_nonneg_right (show 1≤W from B.earn) (show (0:ℤ)≤n.val by positivity)) (le_of_eq B.fare.symm)))
 have hx: m' ≤ (2*(T₀ (π e) s).val)^4:=by unfold m'; rw[mul_comm 2 ((T₀ (π e) s).val)]; gcongr
 have ht:= (qr i m' hX hx (wharf J) (tow_test D h V) (by unfold m'; rw [←u]; exact tow_paid qu V)).1 ((e₀ i n B).dropper V u T)
 unfold hot at ht; rw [dif_pos E.depth] at ht; exact ht
omit h pu Q V in
lemma eventually_nFar {i:ℕ → ℕ} (z:Tendsto i atTop atTop)(c:ℕ):∀ᶠ e:ℕ in atTop,∀ (n:Side)(W₁:LatticeFare (tent Y H) (m (i e) s) n W σ), c≤n.val:=by
 let f':= goes Y H s
 filter_upwards [(f'.comp z).eventually_ge_atTop (W.toNat*c)] with e a n hn
 have ht:=hn.fare; rw[side_register] at ht; have he:W*(c:ℤ)≤ ((T₀ (i e) s).val:ℤ):=by
    conv_lhs=> lhs; rw[←Int.toNat_of_nonneg hn.earn.le]
    exact_mod_cast a
 rw[ht] at he; exact_mod_cast (le_of_mul_le_mul_left he hn.earn)
end note
end Weir
end YM.CF.Buffered.Afterglow.Tower.SlabMark
