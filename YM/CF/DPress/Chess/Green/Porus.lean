import YM.CF.DPress.Chess.Green.Gale
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Green
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube RP Phase Branch Mir Mir.Trip Brace Nacre Window Tenant
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m B:Side}{l':Site (More m)}
local notation "V_"=> CSide m B
local notation "I_"=> northTrip m l'
local notation "α_"=> W.i
local notation "κ_"=> mealU (lagX W.od) 1 inert (V_)
local notation "J_"=>costarU m B l' (northZ m B) W.i
local notation "Θc"=> seamShift m B W.i
-- window map needed by Green.
variable (p:Attend W B l')
include p
lemma clock (i: Site (Domain m B)): run B (I_) i W.i=i W.i+ (((2*W.o:ℤ)): Per _) :=by
 unfold run; rw [pose0 W p]; change i W.i+(( (( (2 • W.od : Cover) W.i) : ℤ)):Per _)=_; congr 2; simp [Wall.od] -- tune
lemma clock_v (i:Site (Domain m B)) : run B (I_) i∈ W.crop V_ 0 ↔ i∈ north V_ W.i:=by
 rw [W.stay,north_mem,clock W p]; let x:= i W.i; have hz:= ZMod.natCast_zmod_val x; constructor
 · rintro ⟨k,h,t,v⟩; have he:(k.toNat:ℤ)=k:=Int.toNat_of_nonneg (by omega); have hk: x=(k.toNat:Per (Domain m B)):=by change x+_= _ at h; rw [show ((k.toNat:ℕ): Per (Domain m B))=( (k:ℤ) : Per (Domain m B)) from (by rw [←Int.cast_natCast, he]),Int.cast_add] at *; exact add_right_cancel (h.trans (add_comm ..)) -- tune
   unfold nextPlane; change x.val≤ _; rw [hk,ZMod.val_natCast_of_lt (show k.toNat < (Domain m B).val from ?_)]; omega; change k.toNat<(V_).val*2; have h:0< (V_).val:= (V_).property; omega
 intro u; change x.val ≤ (V_).val at u; refine ⟨(x.val:ℤ),?_ ,by positivity,by exact_mod_cast (by omega : x.val+0 ≤ (V_).val)⟩; rw [Int.cast_add,Int.cast_natCast,ZMod.natCast_zmod_val]; exact add_comm _ _
lemma reading{U V:Pane (V_)} (h:Agrees (north (V_) W.i) U V): Agrees (W.crop (V_) 0) (through B (I_)⁻¹ U) (through B (I_)⁻¹ V):=by
 have he (x:Seat V_)(t:x∈ W.crop _ 0):run B (I_)⁻¹ x∈ north V_ W.i:=(clock_v W p _).1 (by rw [run_last]; exact t); intro ⟨e,i⟩ x y; have u:glazed ((I_)⁻¹).glare=1:=rfl; let g:= torShift B (I_)⁻¹; have hv(k:Seat V_): run B (I_)⁻¹ k=k+g:= by unfold run; rw [u]; rfl
 let M:=run B (I_)⁻¹; have ht:M (e+step i)=M e+step i:=by change run B (I_)⁻¹ _ = _; unfold M; rw [hv,hv]; abel -- let notation bug
 have hx:=h (M e,i) (he e x) (ht ▸ (he _ y)); unfold through; rw [u]; exact hx -- tune d comp
omit p
-- reordering spaces on both grids. before cut operation translated physical->virtual.
abbrev roi(W:Wall)(m B:Side):Finset (Model (CSide m B)) := univ.filter fun i=> node i.1∈ W.crop _ 0
lemma col_v(x:Model V_):x∈roi W m B ↔ node x.1 ∈ W.crop _ 0:=by unfold roi; rw [mem_filter]; exact and_iff_right (mem_univ _)
open Spark
lemma site_h {A:FC (Single V_)}{b}(h:Sector (Fixed.matterRegion _ (W.crop V_ 0)) b A): Sector (roi W m B) b (crossL (helix _).symm A):=cross_sector (helix _).symm (by intro i; rw [Fixed.mem_matterRegion,col_v]; rfl) h
include p
lemma port_Γ : twist (J_) (cutM (roi W m B))=cutM (colony m B W.i):=by
 have ht:twist (fringe (Trip.far B (I_) (northZ m B)) (portal m B l' (northZ m B) W.i)) (cutM (colony m B W.i))=cutM (colony m B W.i):=by
    apply Mir.twist_comm; ext x y; rw [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; change jump (Equiv.refl _) _ _ _ * _=_ * jump _ _ _ _; rw [jump_apply]; by_cases e:x.1=y.1
    · have he:x∈colony m B W.i ↔ y∈colony m B W.i:=by rw [RP.colony_at,RP.colony_at,e]
      split_ifs<;> simp_all
    simp [e]
 unfold costarU; rw [Fock.twin,show twist (siteM _) _= _ from ?_, ht] -- duplicate syntax
 apply Mir.twist_comm; ext x y; rw [cutM,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; let R:= fperm m B (I_); change jump R _ x y* _=_*jump R _ x y; rw [jump_apply]; by_cases h:R x.1=y.1; swap; · rw [if_neg h,zero_mul,mul_zero]
 have he:x∈colony m B W.i↔ y∈ roi W m B:=by rw [colony_at,col_v,RP.holder,← h,Trip.track]; exact (clock_v W p _).symm
 split_ifs <;> simp_all
end YM.CF.DPress.Chess.Green
