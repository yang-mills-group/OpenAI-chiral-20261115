import YM.SU5.FiniteGaugeData.Hills.Terrace
import Mathlib.Topology.Instances.Int

/-!
# The moment group for this hierarchy
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist
open Function Filter Metric Finset Lattice Hills
open scoped Topology BigOperators InnerProductSpace
variable (L:Side)
-- ffi units rational. tick zero resolution.Avoid integer casts at C.
def spinT (s:ℕ)(j:ℤ):ℝ:= (j:ℝ)/(L.val:ℝ)^s
variable (s t:ℕ)(j k:ℤ)
lemma tea_pos :0 < (L.val:ℝ)^s:= by have h:=L.property; positivity
@[simp] lemma slot_zero : spinT L s 0=0:=by simp [spinT]
lemma slot_lower : 0 ≤ spinT L s j ↔ 0≤j:=by simp [spinT,div_nonneg_iff, (tea_pos L s).le, (tea_pos L s).not_ge]
lemma slot_add : spinT L s (j+k)= spinT L s j + spinT L s k:=by simp only [spinT, Int.cast_add,add_div]
lemma slot_neg : spinT L s (-j)= -spinT L s j:=by simp [spinT,neg_div]
lemma slot_le : spinT L s j ≤ spinT L s k ↔ j≤ k:=by simp [spinT,div_le_div_iff_of_pos_right (tea_pos L s)] -- lemma?
lemma slot_strict : StrictMono (spinT L s):=by intro a b p; exact lt_of_not_ge (fun t=>p.not_ge ((slot_le L s b a).1 t))
lemma slot_up : spinT L (s+1) ((L.val:ℤ)*j)= spinT L s j:=by
 unfold spinT; push_cast; rw [pow_succ]; have p:=tea_pos L s; have he:0<(L.val:ℝ):=by exact_mod_cast L.property
 field_simp
lemma slot_more : spinT L (s+t) (((L.val:ℤ)^t)*j)= spinT L s j:=by
 induction t with
 | zero=> simp
 | succ t ih=> rw [pow_succ',mul_assoc,← Nat.add_assoc,slot_up L (s+t),ih]

def CastQ : AddSubgroup ℝ where
 carrier:={x|∃ s:ℕ,x∈Set.range (spinT L s)}
 zero_mem':=⟨0,0,slot_zero ..⟩
 neg_mem':=by rintro x ⟨s,j,rfl⟩; exact ⟨s,-j, slot_neg ..⟩
 add_mem':=by
   rintro x y ⟨s,j,rfl⟩ ⟨t,k,rfl⟩; refine ⟨s+t, (L.val:ℤ)^t*j+(L.val:ℤ)^s*k,?_⟩; rw [slot_add,slot_more, Nat.add_comm s t,slot_more] -- rewrite both spinT at s+t.Care
abbrev VistaQ (L:Side):=↥(CastQ L)
def ticQ : VistaQ L:= ⟨spinT L s j,s,j,rfl⟩
#check VistaQ
#synth AddCommGroup (VistaQ L)
@[simp] lemma zeroQ : ticQ L s 0=0:= Subtype.ext (slot_zero ..)
lemma lowerQ : 0≤(ticQ L s j).val ↔ 0≤j:= slot_lower ..
lemma addQ : ticQ L s (j+k)= ticQ L s j+ticQ L s k:=Subtype.ext (slot_add ..)
lemma negQ : ticQ L s (-j)= -ticQ L s j:=Subtype.ext (slot_neg ..)
lemma stepQ : ticQ L (s+1) ((L.val:ℤ)*j)=ticQ L s j:=Subtype.ext (slot_up ..)
lemma moreQ : ticQ L (s+t) (((L.val:ℤ)^t)*j)=ticQ L s j:=Subtype.ext (slot_more ..)
lemma monoQ : Injective (ticQ L s):=fun _ _ t=>(slot_strict L s).injective (congrArg Subtype.val t)
lemma frequentT (x:VistaQ L):∀ᶠ s:ℕ in atTop, x∈ Set.range (ticQ L s):=by
 obtain ⟨p,i,t⟩:= x.property
 filter_upwards [eventually_ge_atTop p] with k hk
 obtain ⟨w,rfl⟩:= Nat.exists_eq_add_of_le hk; exact ⟨(L.val:ℤ)^w*i,(moreQ L p w i).trans (Subtype.ext t)⟩
lemma indicate (w:1<L.val) : IsDenseInducing ((↑) : VistaQ L→ℝ) := by
 refine ⟨Topology.IsInducing.subtypeVal,?_⟩ -- lemma name
 intro x; refine Metric.mem_closure_iff.mpr (fun r p=>?_); have he: Tendsto (fun n:ℕ=> (L.val:ℝ)⁻¹ ^n) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).2 (by exact_mod_cast w)) -- tune
 obtain ⟨n,t⟩:=(he.eventually (gt_mem_nhds p)).exists
 let z:= (L.val:ℝ)^n; let y:= x*z; let i:=⌊y⌋; have hv:= Int.floor_le y; have hy:=Int.lt_floor_add_one y; have hp:z>0:=tea_pos L n
 refine ⟨spinT L n i,⟨ticQ L n i,rfl⟩,?_ ⟩; change dist x ((i:ℝ)/z)<r; rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hp).2 hv))]; apply lt_trans _ (show z⁻¹<r from ?_); swap
 · simpa only [z, inv_pow] using t -- hp coe x
 rw [sub_lt_iff_lt_add,← one_div, ← add_div, lt_div_iff₀ hp, add_comm]; exact hy
variable {H:Hilbert} {a:Axis} {L} (X:Terrace H L a)(b c:Axis)(p:b ≠ a)
local notation "R"=> VistaQ L
include X
section
include p
private abbrev Tg (i:ℤ)(r:ℕ):= X.stepT r b i (fun h=>(p h).elim)
local notation "T" => Tg X b p
-- ordering in binder includes ℤ then r? #check
#check Tg
private lemma Tg_up : Tg X b p (L.val*j) (s+1)=T j s:= (X.ascent s b j _).symm
private lemma Tg_more : Tg X b p (((L.val:ℤ)^t)*j) (s+t) = T j s:=by
 induction t with
 | zero=> simp
 | succ t ih=> rw [pow_succ',mul_assoc,←Nat.add_assoc]; exact (Tg_up ..).trans ih
private lemma Tg_align (h:ticQ L s j=ticQ L t k) : Tg X b p j s = T k t:=by
 have hx : ticQ L (s+t) (((L.val:ℤ)^t)*j)=ticQ L (s+t) (((L.val:ℤ)^s)*k):=by rw [moreQ L, h,Nat.add_comm s t, moreQ L]
 rw [←Tg_more s t j X b p, (monoQ ..) hx,Nat.add_comm s t,Tg_more t s]
variable (r:R)
def Driver (x:R): H.Op := (T) ((frequentT L x).exists.choose_spec.choose) ((frequentT L x).exists.choose)
lemma Driver_eq : Driver X b p (ticQ L s j)=X.stepT s b j (fun h=>(p h).elim):= Tg_align _ s _ j X b p (frequentT _ _ |>.exists.choose_spec.choose_spec)
lemma Driver_zero : Driver X b p 0=1:=by rw [← zeroQ L 0, Driver_eq]; exact X.ident ..
lemma Driver_plus (x y:R): Driver X b p (x+y)= Driver X b p x * Driver X b p y:=by
 obtain ⟨g,⟨i,rfl⟩,⟨j,rfl⟩⟩:= ((frequentT L x).and (frequentT L y)).exists; rw [←addQ, Driver_eq,Driver_eq,Driver_eq]; exact (X.via g b _ _ _ _ _ _ rfl).symm
lemma Driver_bound (x:R): ‖Driver X b p x‖ ≤ 1:=by obtain ⟨g,i,rfl⟩:=(frequentT L x).exists; rw [Driver_eq]; exact X.size_ ..
lemma Driver_plus_apply (x y:R)(w:H): Driver X b p (x+y) w= Driver X b p x (Driver X b p y w):= DFunLike.congr_fun (Driver_plus X b p x y) w
lemma Driver_chip (x:R)(w:H): ‖Driver X b p x w‖ ≤ ‖w‖:= ((Driver X b p x).le_of_opNorm_le (Driver_bound X b p x) _).trans_eq (one_mul _)
lemma Driver_move (x:R)(w:H): ‖Driver X b p x w‖=‖w‖:= le_antisymm (Driver_chip X b p x w) (by
 nth_rw 1 [←show Driver X b p (-x) (Driver X b p x w)=w from (by rw [← Driver_plus_apply,neg_add_cancel,Driver_zero]; rfl)]; exact Driver_chip X b p (-x) _) -- nth rw likely rewrites WRONG in target ≥. 
lemma Driver_cool (r:R)(h:Allows a c k): Commute (Driver X b p r) (X.stepT s c k h):=by obtain ⟨i,w,rfl⟩:=(frequentT L r).exists; rw [Driver_eq]; exact X.cool ..
lemma Driver_group (r:R)(u:c≠ a)(w:R): Commute (Driver X b p r) (Driver X c u w):=by obtain ⟨i,w,rfl⟩:=(frequentT L w).exists; rw [Driver_eq]; exact Driver_cool ..
end
/-! May extend one trivial axis for push when needing E4 with no time info. -/
def ramble (x:R): H.Op:= if p:b=a then 1 else Driver X b p x
lemma ramble_eq (x:R)(p:b≠a): ramble X b x=Driver X b p x:=dif_neg p
lemma ramble_self (x:R) : ramble X a x=1:=dif_pos rfl
lemma ramble_two (x y:R): ramble X b (x+y)=ramble X b x*ramble X b y:=by
 by_cases p:b=a; · subst b; simp_rw [ramble_self,one_mul]
 rw [ramble_eq _ _ _ p,ramble_eq _ _ _ p,ramble_eq _ _ _ p,Driver_plus] -- indent tune
lemma ramble_zero : ramble X b 0=1:= by unfold ramble; split_ifs; rfl; exact Driver_zero ..
lemma ramble_price (x:R)(w:H): ‖ramble X b x w‖= ‖w‖:=by unfold ramble; split; rfl; exact Driver_move ..
lemma ramble_cool (x:R)(h:Allows a c k): Commute (ramble X b x) (X.stepT s c k h):=by unfold ramble; split; exact Commute.one_left _; exact Driver_cool ..
lemma ramble_across (x y:R): Commute (ramble X b x) (ramble X c y):= by unfold ramble; split_ifs; exact Commute.one_left _; exact Commute.one_left _; exact Commute.one_right _; exact Driver_group ..
end YM.CF.Buffered.Afterglow.Hierarchy.Mist
