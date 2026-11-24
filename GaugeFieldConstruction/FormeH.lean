import GaugeFieldConstruction.Leisure
import GaugeFieldConstruction.MortarS
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 5800
set_option maxHeartbeats 280000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scree.Ing
open Function Filter MeasureTheory NormedSpace Finset
open scoped Topology BigOperators Classical
open Skye Lattice Corona
open Lattice.Corona.Hive
open Spire
section singular
variable {n:Side}{I:Type}[Fintype I]
variable {b:ℕ}{L:List (Site (Cube.More n))}{a η:ℝ}(P:Hub n)(y:Seat n)(w:Bool)
variable {Ω:ℝ}
local notation "C"=> ColdB b a η L
local notation "R"=> RedB b a η L
local notation "c"=> Cube_M b
variable (z:I→Force n)(U:I→ℝ)(p:∀ i, 0≤U i)(l:Scales b a η L)(g:0≤Ω)(q:∀ y:Seat n,postG (plateI z) U (ColdB b a η L) y ≤ Ω)(t:Cube_M b *Ω ≤1)
include p l g q t
local notation "A"=>P.val.2
open BasisI
lemma deltan (o:Seat n)(h:o∈P.val.2): (∑ x:Base z P w, if y∈plateI (roost z P w) x then (∏ i∈x.val,U i)* C (plateI (roost z P w) x) else 0) ≤ R P.val.2 * ((if y∈P.val.2 then c*Ω else 0)+η⁻¹*respite b (a+2*ζd) η L (plateI z) U o y):=by
 let T:=Base z P w; let S:=plateI z
 let K:=univ.filter (fun i:Finset I=>BasisI z P w i ∧ y∈P.val.2∪ i.biUnion S)
 let Δ:= η⁻¹ * respite b (a+2*ζd) η L S U o y
 have hΔ:0≤Δ:=mul_nonneg (inv_pos.mpr l.pos).le (respite_0 _ _ p _ _ _ _ _ _ l.pos.le)
 let f(i:Finset I):=(∏ j∈i,U j)* C (P.val.2∪i.biUnion S)
 have hx: (∑ x:Base z P w, if y∈plateI (roost z P w) x then (∏ i∈x.val,U i)* C (plateI (roost z P w) x) else 0) = ∑ i∈K,f i:=by
    rw [←Finset.sum_filter]; refine sum_bij (fun a h=>a.val) ?_ ?_ ?_ ?_
    · intro a h; exact mem_filter.mpr ⟨mem_univ _,a.property,(mem_filter.mp h).2⟩
    · intro a _ b _ t; exact Subtype.ext t
    · intro i h; obtain ⟨a,t⟩:=(mem_filter.mp h).2
      exact ⟨⟨i,a⟩,mem_filter.mpr ⟨mem_univ _,t⟩,rfl⟩
    rintro ⟨i,x⟩ a; rfl
 rw [hx]; have he :∀ i∈K,i⊆ clouds S P.val.2:=fun i h j k=> mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2.1.busy _ k⟩ -- shadow
 split
 next hx=> exact (guide P.val.2 S U p l g q t K (fun i h=> ((mem_filter.mp h).2.1).inhab) he).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hΔ) (Temp_p ..|>.le))
 next hx=> rw [zero_add]; exact fuel_touch P.val.2 y S U p l g q t K o h he (fun i h=> (mem_union.mp (mem_filter.mp h).2.2).resolve_left hx)
end singular
section storm
open Cube
variable {n:Side}{I J:Type}[Fintype I][Fintype J]
variable {b:ℕ}{L:List (Site (More n))}{a η:ℝ}(B:Hub n)(y:Seat n)(w:Bool)
variable {Ω:ℝ}
local notation "C"=> ColdB b a η L
local notation "R"=> RedB b a η L
local notation "c"=> Cube_M b
variable (S:I→Support (More n))(V:I→ℝ)(r:∀ i,0≤ V i)(z:J→Force n)(U:J→ℝ)(p:∀ i, 0≤U i)(l:Scales b a η L)(g:0≤Ω)(q:∀ y:Site (More n),postG (plateI z) U (ColdB b a η L) y ≤ Ω)(v:∀ y:Site (More n),postG S V (RedB b a η L) y ≤Ω)(t:Cube_M b *Ω ≤1)
include l r g v t
def Heart (P:Hub n)(S:I→Support (More n))(d:ℕ) := {v: Fin d→I // v∈ LeadQ P.val.2 S d}
def Legist (P:Hub n)(S:I→Support (More n))(d:ℕ)(V: Heart P S d):Hub n:= ⟨⟨P.val.1, lengthQ P.val.2 S V.val⟩, length0 P.val.2 S V.val P.property⟩
noncomputable instance fintist (V:Hub n)(S:I→Support (More n))(d:ℕ):Fintype (Heart V S d):= inferInstanceAs (Fintype ↥(LeadQ V.val.2 S d)) -- same defin.Bashing macro.
variable (d:ℕ)(D:d≤2)
local notation "H0"=>Heart B S d
local notation "K0"=>Legist B S d
local notation "G0"=>R B.val.2 * ridg b B.val.2^3
local notation "Δπ"=>η⁻¹*respite b (a+2*ζd) η L (plateI z) U B.val.1 y
local notation "Γπ"=>η⁻¹*respite b (a+6*ζd) η L S V B.val.1 y
local notation "gπ"=> Cube_M b* Ω
local notation "Mπ"=> windPulse b B.val.1 y
open BasisI
include D
lemma stroll : (∑ x:H0,(∏ i,V (x.val i))* R ((K0 x).val.2)) ≤ G0 :=by
    let f(i:Fin d→I):=(∏ j,V (i j))* R (lengthQ B.val.2 S i)
    let h:= LeadQ B.val.2 S d; change ∑ i:↥h,f i.val≤ _; rw[←sum_subtype h (fun i=> Iff.rfl)]
    let T:= if d=0 then (1:ℝ) else gπ
    have ht:T≤1:=by unfold T; split; rfl; exact t
    refine (safari _ _ _ r l g v t D).trans (le_trans (mul_le_of_le_one_right ?_ ht) ?_)
    · exact mul_nonneg (Temp_p ..|>.le) (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (ridg_one ..) (by norm_num)) (Temp_p ..|>.le)
lemma stroll_site:
 (∑ x:H0, if y∈ (K0 x).val.2 then (∏ i,V (x.val i))* R ((K0 x).val.2) else 0) ≤ G0 * (Mπ*(if d=0 then 1 else gπ)+2*Γπ):=by
    let H:=LeadQ B.val.2 S d; let f(i:Fin d→I):=(∏ j,V (i j))* R (lengthQ B.val.2 S i)
    change (∑ x:↥H,if y∈ lengthQ B.val.2 S x.val then f x.val else 0) ≤ _
    rw [←sum_subtype H (p:=fun j=> j∈H) (fun i=> Iff.rfl) (fun i=>if y∈ lengthQ B.val.2 S i then f i else 0),←sum_filter]
    rw [←mul_assoc 2]; exact safari_y B.val.2 S V r l g v t B.val.1 y B.property D
include p q
lemma crewTouch : (∑ x:H0,∑ k : Base z (K0 x) w, if y∈ plateI (roost z (K0 x) w) k then
 ((∏ i,V (x.val i)) * (∏ i∈k.val,U i)) * C (plateI (roost z (K0 x) w) k)
 else 0) ≤ G0 *((Mπ*gπ+2*Γπ)+Δπ):=by
 let e:=if d=0 then (1:ℝ) else gπ
 let Δ:= Δπ; let Γ:= Γπ; let Y:=gπ; have hy:Y ≤1:=t; have ht:e≤1:=by unfold e; split; rfl; exact t
 have hx:0≤Y:= mul_nonneg (cube_M_pos ..|>.le) g
 let Z(v:H0):=(∏ i,V (v.val i))* R ((K0 v).val.2)
 let Ψ(v:H0)(y:Site (More n)):= if y∈ (K0 v).val.2 then Z v*Y else 0
 let t0:= Mπ; have h1:0≤t0:=pulse_pos ..|>.le; let G:= G0; have hG:0≤G:= mul_nonneg (Temp_p ..|>.le) (pow_nonneg (ridg_pos ..|>.le) _); have hη:=l.pos
 have h2:0≤Δ:=mul_nonneg (inv_pos.mpr hη).le (respite_0 _ _ p _ _ _ _ _ _ hη.le)
 have h3:0≤Γ:= mul_nonneg (inv_pos.mpr hη).le (respite_0 _ _ r _ _ _ _ _ _ hη.le)
 have he(α:H0): (∑ k:Base z (K0 α) w, if y∈ plateI (roost z (K0 α) w) k then ((∏ i,V (α.val i)) * (∏ i∈k.val,U i)) * C (plateI (roost z (K0 α) w) k) else 0) ≤ Ψ α y+Z α*Δ:=by
    let T:=K0 α
    have hp:= mul_le_mul_of_nonneg_left (deltan T y w z U p l g q t B.val.1 T.property) (prod_nonneg (s:= (univ:Finset (Fin d))) (fun i _=> r (α.val i))) -- tune
    rw [mul_sum] at hp; convert! hp using 1
    · apply Finset.sum_congr rfl; intro i _; unfold T; split_ifs; exact mul_assoc ..; simp
    change Ψ _ _+ _*_ = _*(R T.val.2*((if y∈ _ then _ else _)+Δ))
    unfold Ψ Z T Y; split_ifs <;> ring
 apply (sum_le_sum (fun x _=>he x)).trans
 rw [sum_add_distrib,←sum_mul]; refine (add_le_add (b:=(G*(t0*e+2*Γ))*Y) ?_ (mul_le_mul_of_nonneg_right (stroll B S V r l g v t d D) h2)).trans ?_
 · have he:= mul_le_mul_of_nonneg_right (stroll_site B y S V r l g v t d D) hx
   apply le_trans (le_of_eq ?_) he; rw[sum_mul]; apply Finset.sum_congr rfl; intro i _; unfold Ψ; split_ifs <;> first|rfl| exact (zero_mul _).symm; -- tune
 change _+ G* _≤G * _; change G*(t0*e+2*Γ)*Y+G*Δ≤G*((t0*Y+2*Γ)+Δ); nlinarith only [mul_le_mul_of_nonneg_right ht (mul_nonneg (mul_nonneg hG h1) hx),mul_le_mul_of_nonneg_left hy (mul_nonneg hG h3)]
end storm
end YM.CF.Scree.Ing
end
