/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Next.RANK.Axial
/-! # Local axial positions on noncentered grid. Used for oriented taste estimate. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Box
open Function Finset Lattice Tree Wilson Next.Rank.Axial
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n:Side}
variable (r:Side)
def landmark (p:Site n)(i:Axis):ℕ:= (p i).val
variable {i:Axis}
def skid (p:Site n)(i:Axis):= landmark p i%r.val
def region (p:Site n)(i:Axis):= landmark p i / r.val
-- internal even across coarsening if not exact divisibility. Natural wrap never internal
def sheltered (b:Edge (Site n)) : Prop := landmark b.1 b.2+1<n.val ∧ skid r b.1 b.2+1<r.val
instance (b:Edge (Site n)): Decidable (sheltered r b):=by unfold sheltered; infer_instance
lemma landmark_pos {p:Site n} {i:Axis} (h:p i≠0):0<landmark p i:=Nat.pos_of_ne_zero (fun t=> h (by conv_lhs => rw [← ZMod.natCast_zmod_val (p i), (show ZMod.val (p i)=0 from t)]; norm_num))
@[simp] lemma mark_zero : landmark (0:Site n) i=0:=ZMod.val_zero
lemma mark_up {p:Site n} (h: landmark p i+1<n.val) : landmark (p+step i) i= landmark p i+1:=by
 have hc: 1<n.val:= by omega
 unfold landmark at *; rw [Pi.add_apply,step_apply,if_pos rfl,ZMod.val_add,ZMod.val_one'' hc.ne', Nat.mod_eq_of_lt h]
lemma mark_down {p:Site n} (h:0 < landmark p i): landmark (p-step i) i+1= landmark p i :=by
 have hp: landmark p i < n.val:= (p i).val_lt; have hc:1<n.val:=by omega
 have hk: (1:Per n).val=1:= ZMod.val_one'' hc.ne'
 unfold landmark at *; rw [Pi.sub_apply,step_apply,if_pos rfl,ZMod.val_sub (hk.symm ▸ h),hk]; omega
@[simp] lemma mark_else (p:Site n) {j:Axis} (h:j≠i) : landmark (p+step i) j=landmark p j:=by simp [landmark,h]
@[simp] lemma mark_else' (p:Site n) {j:Axis} (h:j≠i) : landmark (p-step i) j=landmark p j:=by simp [landmark,h]
lemma skid_lt (p:Site n)(i:Axis): skid r p i<r.val:= Nat.mod_lt _ r.property
-- avoid tedious tearing of nat div proof by single simple recurrence theorem
private lemma plus_mod (x r:ℕ) (p:0<r)(h:x%r+1<r): (x+1)%r=x%r+1:=by
 rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1<r from by omega), Nat.mod_eq_of_lt h]
private lemma plus_div (x r:ℕ) (p:0<r)(h:x%r+1<r): (x+1)/r=x/r:=by
 apply Nat.eq_of_mul_eq_mul_left p; have hp:=plus_mod x r p h; have hv:= Nat.mod_add_div x r; have ht:= Nat.mod_add_div (x+1) r; omega
private lemma slide (x z r:ℕ) (p:0<r) (h:z+1=x) (t:0<x%r) : z%r+1<r:=by
 by_contra u; have he:= Nat.mod_lt z p; have hp:z%r+1=r:=by omega
 have hr:r>1:=by have hf:= Nat.mod_lt x p; omega
 subst x; rw [Nat.add_mod,Nat.mod_eq_of_lt hr,hp,Nat.mod_self] at t; omega
lemma skids {p:Site n} {i:Axis}(h: sheltered r (p,i)) : skid r (p+step i) i= skid r p i +1:=by unfold skid; rw [mark_up h.1]; exact plus_mod _ _ r.property h.2
lemma blocks {p:Site n}(h: sheltered r (p,i)) : region r (p+step i)= region r p:=by
 funext j; rcases eq_or_ne j i with he|he; · subst j; unfold region; rw [mark_up h.1]; exact plus_div _ _ r.property h.2
 simp [region,he]
lemma early {p:Site n}(h:0<skid r p i): sheltered r (p-step i,i):=by
 have hv:0<landmark p i:= lt_of_lt_of_le h (Nat.mod_le ..); have he:=mark_down hv; exact ⟨he.trans_lt (p i).val_lt, slide _ _ _ r.property he h⟩
def kane (p:Site n) : Finset Axis:= univ.filter fun i=>0< skid r p i
def support (p:Site n):Finset Axis:= univ.filter fun i=> 0 < landmark p i
lemma withstand (p:Site n)(h:p ≠0) : (support p).Nonempty:=by
 obtain ⟨i,hi⟩:= Function.ne_iff.mp h; exact ⟨i,mem_filter.mpr ⟨mem_univ _,landmark_pos hi⟩⟩
def crest (x:Site n):Axis:= if h:(kane r x).Nonempty then (kane r x).max' h else if p:(support x).Nonempty then (support x).max' p else 0
lemma crest_pos {x:Site n}(h:x≠0): 0< landmark x (crest r x) :=by
 unfold crest; split
 next t=> exact lt_of_lt_of_le ((mem_filter.mp (Finset.max'_mem _ t)).2) (Nat.mod_le ..)
 next=> rw [dif_pos (withstand x h)]; exact (mem_filter.mp (Finset.max'_mem _ (withstand x h))).2
lemma crest_asc {x:Site n}(h:(kane r x).Nonempty): 0< skid r x (crest r x) :=by rw [crest,dif_pos h]; exact (mem_filter.mp (Finset.max'_mem _ h)).2
lemma crest_gt {x:Site n}(t:0< skid r x i): i≤ crest r x:=by
 have hx:i∈ kane r x:= mem_filter.mpr ⟨mem_univ _,t⟩; rw [crest,dif_pos (show (kane r x).Nonempty from ⟨i,hx⟩)]; exact le_max' _ _ hx
lemma crest_eq {x:Site n}(t:0<skid r x i)(p:∀ j:Axis,i<j→skid r x j=0): crest r x=i:=by
 have hh: i∈kane r x:=mem_filter.mpr ⟨mem_univ _,t⟩; exact (le_antisymm (le_of_not_gt fun v=>by have hx:=p _ v; exact (crest_asc r (show (kane r x).Nonempty from ⟨i,hh⟩)).ne hx.symm) (crest_gt r t))
private lemma leaf_ (x:Site n) : leaf (whole n) x ↔ x≠0 := by
 haveI : Subsingleton (Site (1:Side)) := inferInstanceAs (Subsingleton (Axis → ZMod 1))
 unfold leaf; simp only [Subsingleton.elim ((whole n).parent x) 0, show (whole n).embed 0 = 0 from (whole n).root.map_zero]
-- height global, satisfies original condition.
def sumSite (x:Site n):=∑ i, landmark x i
lemma sinks (x:Site n)(h:0<landmark x i) : sumSite (x-step i)<sumSite x:=by
 have hp:=mark_down h; have hx:landmark (x-step i) i<landmark x i:=by omega
 unfold sumSite; refine sum_lt_sum (fun j _=> ?_) ⟨i,mem_univ _,hx⟩; rcases eq_or_ne j i with he|he; · subst j; exact hx.le
 rw [mark_else' _ he]
def columbia (n:Side) : Forest (whole n) where
 height:=sumSite
 bound x:= by
   change sumSite x≤4*n.val; calc
   _ ≤ ∑ _ : Axis, n.val := sum_le_sum fun i _=> (x i).val_lt.le
   _ = _:=by simp [Axis]
 up x:=negDir (crest r x)
 rise x hx := by rw [Step.vec_neg,← sub_eq_add_neg]; exact sinks _ (crest_pos r ((leaf_ _).mp hx))
 stays _ _ := by
   haveI : Subsingleton (Site (1:Side)) := inferInstanceAs (Subsingleton (Axis → ZMod 1))
   exact Subsingleton.elim ..
lemma col_erect (x:Site n)(h:sheltered r (x,i))(u:∀ j:Axis, i<j→ skid r x j=0) : (x,i)∈ (columbia r n).trunks:=by
 rw [(columbia r n).trunk_mem_iff]; let y:= x+step i; have hp: 0 < skid r y i:= by rw [show skid r y i=_ from skids r h]; omega
 have hx: crest r y =i:= crest_eq r hp (fun j h=> by simpa [skid,y,h.ne'] using u j h)
 refine ⟨y,(leaf_ _).2 (fun H=>by simp [H,skid] at hp),?_⟩; change (y-step (crest r y),crest r y)=(x,i); simp [hx,y]
variable {r}
def pile (r:Side)(x:Site n):ℕ:=∑ i:Axis,skid r x i
-- because accidental hidden n maybe #check
lemma pile_move (x:Site n){i}(h:sheltered r (x,i)) : pile r (x+step i)=pile r x+1:=by
 unfold pile; rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ (skid r x) (mem_univ i), skids _ h]; rw [add_right_comm]; congr 2; exact sum_congr rfl fun j h=>by simp [skid,(mem_erase.mp h).1]
lemma pile_span (x:Site n)(r:Side):pile r x ≤ 4*r.val:= by unfold pile; exact (sum_le_sum (g:=fun _=> r.val) fun i _=> (skid_lt r x i).le).trans_eq (by simp [Axis])
lemma sheltered_shift {x:Site n}(hx:sheltered r (x,i)) {j:Axis}(p:i≠j) : sheltered r (x+step j,i)∧ sheltered r (x-step j,i):=by
 simpa [sheltered,skid,p] using hx -- tune
variable {G:Gauge}{U : Config G n} {t:ℝ}
lemma pile_axial (x:Site n)(h:0 ≤ t)(p:sheltered r (x,i))(b:∀ p:Face (Per n), region r p.1 = region r x → G.chord (faceValue U p)≤ t)(s:∀ e∈(columbia r n).trunks,U e=1) : G.chord (U (x,i)) ≤ pile r x * t:=by
 classical
 generalize he : pile r x=k
 induction k using Nat.strong_induction_on generalizing x with
 | h k ih=>
    by_cases e:(x,i)∈(columbia r n).trunks
    · rw [s _ e, G.chord_one]; positivity
    obtain ⟨j,xj,u⟩:∃ j:Axis, i<j∧0<skid r x j:= by
       by_contra! q; exact e (col_erect r x p (fun j hj=>Nat.eq_zero_of_le_zero (q j hj)))
    let c:= crest r x
    have hc: i<c:= lt_of_lt_of_le xj (crest_gt r u); have hv:0<skid r x c:= crest_asc r (show (kane r x).Nonempty from ⟨j,mem_filter.mpr ⟨mem_univ _,u⟩⟩)
    let y:= x-step c; have hy:y+step c=x:=sub_add_cancel ..; have ht:sheltered r (y,c):= early r hv; have hu:region r y= region r x:=  (blocks r ht).symm.trans (congrArg _ hy)
    have hw (a:Axis)(x':c < a): skid r y a=0:= by
      simp only [y,skid,mark_else' _ x'.ne']; by_contra e; exact x'.not_ge (crest_gt r (show 0<skid r x a from Nat.pos_of_ne_zero e))
    have q:=value_eq U y hc; rw [hy,s _ (col_erect r y ht hw),s _ (col_erect r (y+step i) (sheltered_shift ht hc.ne').1 (fun j t=>by simpa [skid,(hc.trans t).ne'] using hw j t))] at q; simp only [inv_one,mul_one] at q
    let E:=U (x,i); let D:= U (y,i); have A : G.chord (D*E⁻¹) ≤ t:= q ▸ b (y,⟨(i,c),hc⟩) hu; have W:G.chord E≤ t+G.chord D:= calc
       G.chord E=G.chord ((D*E⁻¹)⁻¹*D):=by group
       _ ≤ _ := (G.chord_triangle (D*E⁻¹)⁻¹ D).trans (add_le_add ((G.chord_inv _).trans_le A) le_rfl)
    have hz:pile r y+1=k:= by rw [← pile_move y ht,hy,he]
    have hz':(k:ℝ)= (pile r y:ℝ)+1:=by exact_mod_cast hz.symm
    have hl : G.chord D ≤ (pile r y)*t:= ih (pile r y) (by omega) y (sheltered_shift p hc.ne).2 (fun z x=>b z (x.trans hu)) rfl
    change G.chord E≤ _; rw [hz']; linarith
lemma cordon (x:Site n)(h:0 ≤ t)(p:sheltered r (x,i))(b:∀ p:Face (Per n), region r p.1 = region r x → G.chord (faceValue U p) ≤ t)(v:(columbia r n).Slice G)(s:U=(columbia r n).drape v) : G.chord (U (x,i)) ≤ (4*r.val) * t:=by
 apply (pile_axial _ h p b (fun y p=> s ▸ (columbia r n).on_tree v ⟨y,p⟩)).trans
 gcongr; exact_mod_cast pile_span x r
end YM.Hill.Box
#print axioms YM.Hill.Box.cordon
#print axioms YM.Hill.Box.columbia
