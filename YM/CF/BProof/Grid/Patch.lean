import YM.CF.BProof.Grid.Wire

/-! Transport weights for pricing mesh entities. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Lattice Function Set Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : ℕ} {c s : Side} (g : Ratio c s)
namespace Entity
variable (p : Entity n c)

lemma stepMem {x:Cubic n s}(i:Fin n) (hc:4≤ c.val)(h : p.Mem g x):
    p.Mem g (slide x i) ↔ p.coord g x i < p.len g i := by
 constructor
 · intro v; have hq:= v i; rw [coord_step p g x h i hc,update_self] at hq; exact hq
 intro v j; rw [coord_step p g x h i hc]; by_cases u:j=i; subst j; rw [update_self]; exact v
 rw [update_of_ne u]; exact h j
lemma inside_put_step (a : Tick (n:=n)) (i : Fin n) (h:a≤p.len g)(u:a i<p.len g i) : update a i (a i+1) ≤ p.len g := by intro j; by_cases g:j=i; subst j; rw [update_self]; exact u; rw [update_of_ne g]; exact h j
lemma set0 (a : Tick (n:=n)) (i:Fin n)(h:a≤ p.len g): update a i 0 ≤ p.len g:=by intro j; by_cases g:j=i; subst j; rw [update_self]; exact Nat.zero_le _; rw [update_of_ne g]; exact h j
lemma restore' (a : Tick (n:=n)) (i:Fin n)(k:ℕ) : jump (p.put g (update a i 0)) i k=p.put g (update a i k):=by ext j; by_cases h:j=i; subst j; simp [put,jump]; rw [jump_off _ k h]; unfold put; rw [update_of_ne h,update_of_ne h]
lemma restore (a : Tick (n:=n)) (i:Fin n) : jump (p.put g (update a i 0)) i (a i)=p.put g a := by rw [restore',update_eq_self]
lemma expandM (a : Tick (n:=n)) (i:Fin n)(k:ℕ)(h:a≤p.len g)(e:k≤a i)(hc:4≤c.val):p.Mem g (jump (p.put g (update a i 0)) i k):=by
 rw [restore']; apply p.mem_put g hc; intro j; by_cases u:j=i; subst j; rw [update_self]; exact e.trans (h i); rw [update_of_ne u]; exact h j

variable (G) (U : Wire G n s)
def turtle : List (Fin n)→Tick (n:=n)→ G.El
 | [],_=>1
 | i::l,a=> turtle l (update a i 0)* Wire.line G U (p.put g (update a i 0)) i (a i)

def paths (x:Cubic n s):= p.turtle G g U (List.finRange n) (p.coord g x) -- parameter order tune
@[fun_prop] lemma turtle_c (l) (a : Tick (n:=n)) : Continuous (fun U: Wire G n s=> p.turtle G g U l a):=by induction l generalizing a with|nil=>exact continuous_const|cons i l ih=> exact (ih _).mul (Wire.continuous_line ..)
lemma turtle_eq (V: Wire G n s)(hc:4≤c.val)(hh: Wire.Agrees G {x|p.Mem g x} U V)
    (l : List (Fin n))(a : Tick (n:=n)) (h:a≤p.len g): p.turtle G g U l a=p.turtle G g V l a:= by
 induction l generalizing a with
 | nil=>rfl
 | cons i l ih=> rw [turtle,turtle,ih _ (p.set0 g a i h),Wire.line_eq G U V _ _ _ (fun k e=>p.expandM g _ i _ h e hc) hh]

lemma turtle_step (hc:4≤c.val){m:ℝ}(hm:0≤m)(H:Wire.Flat G U {x|p.Mem g x} m)
    (l:List (Fin n)) (a : Tick (n:=n))(h:a≤p.len g)(i:Fin n)(v:i∈l) (ha:a i<p.len g i):
    cd G (p.turtle G g U l a*U (p.put g a,i)) (p.turtle G g U l (update a i (a i+1))) ≤ l.length*g.count.val*m := by
 induction l generalizing a with
 | nil=> simp at v
 | cons j l ih=>
    rw [turtle,turtle]
    by_cases e:i=j
    · subst i; simp only [update_idem,update_self,Wire.line, p.restore g a j,mul_assoc (turtle ..),cd_self]; positivity
    let x := update a j 0; let X:=p.put g x; let y:=update x i (x i+1); let k:=a j
    have hj : x ≤ p.len g := p.set0 g a j h
    have he : x i=a i:=update_of_ne e ..
    have ht:= ih x hj ((List.mem_cons.mp v).resolve_left e) (he.symm ▸ ha)
    have hq:y=update (update a i (a i+1)) j 0 := by unfold y; rw [he,update_comm e]; -- tune
    have hm' : slide X i=p.put g y := (p.put_step g x i).symm
    have hr (b:ℕ)(hg:b≤k): jump X j b ∈ {x|p.Mem g x} ∧ slide (jump X j b) i∈{x|p.Mem g x}:=by
       have hl:= p.expandM g a j b h hg hc
       refine ⟨hl,(p.stepMem g i hc hl).mpr ?_⟩ -- tune
       rw [coord, jump_off _ b e]; change along (p.first g i) (p.first g i+ ↑(x i)) < _; rw [he,along_add _ (lt_of_lt_of_le ha (p.narrow g hc i).le)]; exact ha
    have hi:=Wire.translate G U X j i k _ _ H hr
    dsimp only [Set.mem_setOf_eq] at *
    rw [hm',show jump X j k=p.put g a from p.restore ..] at hi
    rw [←hq,update_of_ne (Ne.symm e)]
    let T:=Wire.line G U (p.put g y) j k; let V:=p.turtle G g U l x; let B:=U (X,i)
    apply le_trans (cd_triangle G _ (V*B*T) _); rw [mul_assoc V _ (U _),mul_assoc V B T,cd_mul_left]; nth_rw 1 [← mul_assoc V B T]; rw [cd_mul_right,List.length_cons]; push_cast
    have he : (k:ℝ) ≤ g.count.val:= by exact_mod_cast (h j).trans (p.width g j)
    exact (add_le_add hi ht).trans (by linarith [mul_le_mul_of_nonneg_right he hm])

lemma smooth {x:Cubic n s}{i}(h:p.Mem g x)(hl:p.Mem g (slide x i))(hc:4≤c.val){m:ℝ}(hm:0≤m)(H:Wire.Flat G U {x|p.Mem g x} m) :
    cd G (p.paths G g U x * U (x,i)) (p.paths G g U (slide x i)) ≤ n*g.count.val*m := by
 unfold paths; rw [coord_step p g x h i hc]; have he:= p.turtle_step G g U hc hm H (List.finRange n) (p.coord g x) h i (by simp) ((p.stepMem g i hc h).mp hl); rw [put_coord,List.length_finRange] at he; exact he
end Entity
end YM.CF.BProof.Grid
