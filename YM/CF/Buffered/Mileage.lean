import YM.CF.Buffered.Spun
/-!
# Closed tiles. Gauge rooms can be shared: exact fiber costs.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Lattice Cube Finset
open scoped BigOperators Topology Fin.NatCast
variable {w v: Side} {A D:Finset Axis}

def topwall (w:Side)(A:Finset Axis) (i:Axis) : ℤ := if i∈A then w.val-1 else w.val
-- ensure type is Cover
abbrev Roost (w:Side)(A:Finset Axis):= {x:Cover// ∀ i, 0 ≤ x i ∧ x i ≤ topwall w A i}
abbrev Post (w:Side) := Roost w univ
abbrev Rail (δ:Axis→Side) := (i:Axis)→ Fin (δ i).val
abbrev Uniform (p:Side) : Axis→Side :=fun _=>p

def Landing (δ: Axis→Side) := ∀ i, Even (δ i).val
lemma landing_ge {δ:Axis→Side}(p:Landing δ)(i:Axis): 2 ≤ (δ i).val:=by obtain ⟨v,h⟩:=p i; have ht: 0 < (δ i).val:= (δ i).property; omega
-- anticut last tile markers via val not valMinAbs
variable {δ:Axis→Side} (p:Rail δ)(i:Axis)
def endsAt := (p i).val+1=(δ i).val
def next (i:Axis) (r: Rail δ) := r+Pi.single i 1
def shade (r: Rail δ) : Finset Axis := univ.filter fun i=> (r i).val%2=1
lemma next_rail : next i p i=p i+1 := by simp [next]
lemma next_at {j:Axis}(h:j≠i): next i p j=p j:= by simp [next,h]
lemma next_val : (next i p i).val=if (p i).val+1=(δ i).val then 0 else (p i).val+1 :=by
 rw [next_rail,Fin.val_add_eq_ite, Fin.val_one']; have he:= (p i).isLt; by_cases t:(δ i).val=1; rw [show 1%(δ i).val=0 from (by rw [t])]; split_ifs <;> omega
 rw [Nat.mod_eq_of_lt (by omega:1<(δ i).val)]; split_ifs <;> omega
lemma shade_next (h:Landing δ) (j:Axis) : j∈shade (next i p) ↔ if j=i then j∉shade p else j∈shade p:=by
 unfold shade; simp only [mem_filter,mem_univ,true_and]; split
 · subst j; rw [next_val p]; obtain ⟨x,k⟩:=h i; split_ifs with t
   · have he:(p i).val%2=1:=by omega
     simp [he]
   omega
 next e=> rw [next_at p i e]
lemma next_away (h:Landing δ) : next i p≠p:= by
 intro u; have he:= shade_next p i h i; simp [u] at he

lemma floorL : 0 < w.val := w.property -- use lemma
lemma wall_top : topwall w A i ≤ w.val := by unfold topwall; split <;> omega
lemma wall_mem (p:i∈A) : topwall w A i=(w.val:ℤ)-1:=if_pos p

namespace Roost
instance roostFinite : Fintype (Roost w A) :=Fintype.subtype (box w.val |>.filter fun x => ∀ i,0≤ x i ∧ x i ≤topwall w A i) (by
 intro i; rw [mem_filter]; apply and_iff_right_of_imp; intro h
 rw [box_test]; constructor <;> intro j <;> obtain ⟨b,e⟩:=h j <;> have h₃:= wall_top (A:=A) (w:=w) j <;> omega)

variable (x:Roost w A)
lemma nonneg : 0 ≤ x.val i := (x.property i).1
lemma maxval : x.val i ≤ w.val := (x.property i).2.trans (wall_top i)
lemma below (h:i∈A) : x.val i < w.val := by have hv:= (x.property i).2; rw [wall_mem i h] at hv; omega

def ofpost (A:Finset Axis)(x:Post w) : Roost w A:= ⟨x.val,fun i=> ⟨x.nonneg i,by have h:= (x.property i).2; rw [wall_mem i (mem_univ _)] at h; unfold topwall; split <;> omega⟩⟩
def wallet : Post w := ⟨fun i=> if x.val i = w.val then 0 else x.val i,fun i=> by
 rw [wall_mem i (mem_univ _)]; have he: 0<w.val:=floorL; have hu:= x.nonneg i; have hv:= x.maxval i; dsimp only; split_ifs <;> omega⟩
lemma wallet_a (y:Post w)(A:Finset Axis): wallet (ofpost A y)=y:= Subtype.ext (funext fun i => if_neg (by exact (y.below i (mem_univ _)).ne))

-- reflection(s) in the interior middle of these tiles.
def shades (T:Finset Axis)(x:Roost w A):Roost w A:=⟨fun i=>if i∈T then topwall w A i-x.val i else x.val i, fun i=>by
 obtain ⟨v,b⟩:= x.property i; dsimp only; split_ifs <;> omega⟩
def shadeOne (i:Axis)(x:Roost w A):= shades {i} x
lemma shades_eq {T:Finset Axis} {i:Axis} (p:i∈T): (shades T x).val i= topwall w A i-x.val i:= if_pos p
lemma shades_other {T:Finset Axis} {i:Axis}(p:i∉T): (shades T x).val i=x.val i:=if_neg p
lemma shades_square (T:Finset Axis):shades T (shades T x)=x:=by
 apply Subtype.ext; funext i; unfold shades; dsimp; split_ifs <;> omega
lemma shades_push {T:Finset Axis}{i:Axis}(p:i∉T): shades (insert i T) x=shadeOne i (shades T x):=by
 apply Subtype.ext; funext j; by_cases e:i=j
 · subst j; unfold shadeOne; rw [shades_eq _ (mem_insert_self _ _),shades_eq _ (mem_singleton_self _),shades_other _ p]
 change _=(shades _ _).val _; rw [shades_other _ (mem_singleton.not.mpr (Ne.symm e))]; simp only [shades, mem_insert, Ne.symm e, false_or]

def mirrorR (T:Finset Axis): Equiv.Perm (Roost w A) := ⟨shades T,shades T,fun x=> shades_square x T,fun x=> shades_square x T⟩

-- corners (x_j=w, shared with next), and number of copies read at any port
-- (open tile (rail,x) rep)
def plusWall : Finset Axis := univ.filter fun j=> x.val j=w.val
def ball (A:Finset Axis)(x:Post w):Finset Axis := univ.filter fun j=> x.val j=0 ∧ j∉A
def share := ((ball A x.wallet).powerset.card:ℝ)⁻¹
lemma plus_allowed : x.plusWall ⊆ ball A x.wallet:=by
 intro i h; replace h:= (mem_filter.mp h).2; refine mem_filter.mpr ⟨mem_univ _, if_pos h, fun i'=> (x.below i i').ne h⟩ -- tune r tuple
lemma ball_iff : i∈ball A x.wallet ↔ i∉A ∧ (x.val i=0 ∨ x.val i=w.val):=by
 simp only [ball,mem_filter,mem_univ,true_and, wallet]; split_ifs <;> tauto
lemma ball_mirror (T:Finset Axis):ball A (wallet (shades T x))=ball A (wallet x):=by
 ext i; rw [ball_iff,ball_iff]; by_cases p:i∈A; tauto
 by_cases h:i∈T; swap; · rw [shades_other _ h]
 rw [shades_eq _ h]; unfold topwall; rw [if_neg p,and_iff_right p,and_iff_right p]; omega
lemma share_mirror (T:Finset Axis):share (shades T x)=share x:=by rw [share,share,ball_mirror]
lemma share_pos : 0 < share x:= inv_pos.mpr (by exact_mod_cast card_pos.mpr (show (ball A (x.wallet)).powerset.Nonempty from ⟨∅,mem_powerset.mpr (empty_subset _)⟩))

abbrev Fib (A:Finset Axis)(x:Post w):Type:= {T:Finset Axis // T ⊆ ball A x}
def toggle (y:Post w){A:Finset Axis}(T:Fib A y):Roost w A:=⟨fun i=> if i∈T.val then w.val else y.val i,fun i=> by
 dsimp only; by_cases e:i∈T.val; swap; · rw [if_neg e]; exact (ofpost A y).property i
 have k:= (mem_filter.mp (T.property e)).2.2; rw [if_pos e,topwall,if_neg k]; omega⟩
lemma toggle_plus {y:Post w} (T:Fib A y): (toggle y T).plusWall=T.val:=by ext i; have h:= y.below i (mem_univ _); simp [toggle, plusWall,h.ne]
lemma toggle_ball {y:Post w} (T:Fib A y): wallet (toggle y T)=y:=by
 apply Subtype.ext; funext i; simp only [wallet,toggle]; by_cases H:i∈T.val; simpa [H] using (mem_filter.mp (T.property H)).2.1.symm
 simp [H,(y.below i (mem_univ _)).ne]
lemma toggle_back : toggle x.wallet ⟨x.plusWall, plus_allowed x⟩=x:=by
 apply Subtype.ext; funext i; simp only [toggle,plusWall,wallet,mem_filter,mem_univ,true_and]; split_ifs <;> omega

variable {i} -- remove tangle
def corner (δ:Axis→Side)(A:Finset Axis): Rail δ:= fun i=>if i∈A then 1 else 0
lemma corner_empty (δ):corner δ ∅=0:= funext fun _ => if_neg (notMem_empty _)
lemma corner_one (δ:Axis→Side)(i:Axis):corner δ {i}=Pi.single i 1:= by
 funext j; by_cases h:i=j
 · subst j; simp [corner]
 simp [corner,Ne.symm h]
lemma corner_off (A:Finset Axis)(e:i∉A): corner δ A i=0:= if_neg e
def slide (r:Rail δ)(x:Roost w A):Rail δ × Post w:= (r + corner δ x.plusWall, x.wallet)
lemma slide_first (r:Rail δ)(y:Post w)(A:Finset Axis): slide r (ofpost A y)=(r,y):=by
 unfold slide; rw [wallet_a,show plusWall (ofpost A y)= ∅ from ?_,corner_empty,add_zero]; ext i; simp [plusWall, ofpost,(y.below i (mem_univ _)).ne]
-- fibers
variable {r:Rail δ}{y:Post w}
def splay (δ:Axis→Side)(A:Finset Axis)(w:Side)(z:Rail δ × Post w):Finset (Rail δ × Roost w A):= univ.filter fun t=>slide t.1 t.2=z
noncomputable def atball (r:Rail δ)(A:Finset Axis)(y:Post w): {x:Rail δ × Roost w A // slide x.1 x.2=(r,y)} ≃ Fib A y where
 toFun x:=⟨x.val.2.plusWall,Subset.trans (plus_allowed x.val.2) (subset_of_eq (congrArg (ball A) (show x.val.2.wallet=y from congrArg Prod.snd x.property)))⟩
 invFun t:= ⟨(r-corner δ t.val,toggle y t),by dsimp only [slide]; rw [toggle_ball,toggle_plus,sub_add_cancel]⟩
 left_inv := by
    rintro ⟨⟨b,x⟩,h⟩; unfold slide at h; cases Prod.mk.inj h; next ht he=>
     subst r y; refine Subtype.ext (Prod.ext ?_ (toggle_back x)); exact add_sub_cancel_right b _
 right_inv t:= Subtype.ext (toggle_plus t)
lemma shares_count (v:Rail δ × Post w): (splay δ A w v).card=(ball A v.2).powerset.card:=by
 obtain ⟨r,y⟩:=v; rw [←Fintype.card_coe,←Fintype.card_coe]; apply Fintype.card_congr
 exact ((Equiv.subtypeEquivRight fun _=>by simp [splay]).trans (atball r A y)).trans (Equiv.subtypeEquivRight fun x=>by simp) -- tunes
lemma share_all (A:Finset Axis){F:Type*}[AddCommGroup F][Module ℝ F](g: Rail δ × Post w → F): ∑ r:Rail δ,∑ x:Roost w A, x.share • g (slide r x)= ∑ v,g v:=by
 rw [←Fintype.sum_prod_type (f:=fun p:Rail δ × Roost w A=> p.2.share • g (slide p.1 p.2)),←sum_fiberwise _ (fun p:Rail δ × Roost w A=> slide p.1 p.2)] -- tune
 refine sum_congr rfl fun v _=> ?_; change (∑ x∈ splay δ A w v, _)= _
 let k:ℕ:=(ball A v.2).powerset.card; have hk:k≠0:=by unfold k; rw [card_powerset]; positivity
 rw [sum_congr rfl (g:=fun _=>(k:ℝ)⁻¹ • g v) (fun i p=>?_)] -- tune
 · rw [sum_const,shares_count,← Nat.cast_smul_eq_nsmul ℝ, smul_smul,show _ = (1:ℝ) from mul_inv_cancel₀ (show (k:ℝ)≠0 by exact_mod_cast hk), one_smul]
 have he:= (mem_filter.mp p).2; unfold k share; rw [he,show i.2.wallet=v.2 from congrArg Prod.snd he]
end Roost
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Roost.share_all
