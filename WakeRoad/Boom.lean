import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rod
import YM.Planned.ATOM_REGULAR_ESTIMATE.Pin
/-! # Constructive curl circuits on actual small torus patches.
Explicit discrete Poincare lemma (tangents abelian).
Quotient **each piece** by its nulls, kept ℓ¹ price. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000
noncomputable section
namespace YM.WakeRoad
open Lattice Finset Function Work.E01 Work.E08
open scoped BigOperators
namespace Boom
-- signed sum from 0, all values use positive bond convention
variable {E:Type*}
def stint [AddCommGroup E] (f:ℤ→E)(z:ℤ):E:=if 0≤z then ∑ i∈Finset.Ico 0 z,f i else -(∑ i∈Finset.Ico z 0,f i)
lemma stint_step [AddCommGroup E](f:ℤ→E)(z:ℤ):stint f (z+1)=stint f z+f z:=by
 have hz (a:ℤ)(h:a ≤ z):Finset.Ico a (z+1)=insert z (Finset.Ico a z):= by ext j; simp; omega
 by_cases v:0 ≤ z
 · rw [stint,stint,if_pos (by omega),if_pos v,hz _ v, sum_insert (by simp)]; exact add_comm ..
 have t (j:ℤ)(l:j<0):Finset.Ico j 0=insert j (Finset.Ico (j+1) 0):=by ext i; simp; omega
 rw [stint,stint, if_neg v,t z (by omega),sum_insert (by simp)]
 by_cases b:z+1=0
 · rw [if_pos (by omega),b,Finset.Ico_self,sum_empty]; abel
 rw [if_neg (by omega)]; abel
lemma stint_add [AddCommGroup E](f g:ℤ→E)(z:ℤ):stint (f+g) z=stint f z+stint g z:=by unfold stint; split <;> simp [sum_add_distrib,add_comm]
lemma stint_sub [AddCommGroup E](f g:ℤ→E)(z:ℤ):stint (f-g) z=stint f z-stint g z:=by unfold stint; split <;> simp [sub_eq_add_neg,Pi.sub_apply,add_comm,sum_add_distrib]
lemma stint_flux [AddCommGroup E](f:ℤ→E)(z:ℤ): stint (fun t=>f (t+1) - f t) z=f z-f 0:=by
-- reduce to int induction fw bw.
 induction z using Int.induction_on with
 | zero => simp [stint]
 | succ z ih=> rw [stint_step, ih]; abel
 | pred z ih=> have hp:=stint_step (fun t=> f (t+1) - f t) (- (z:ℤ)-1); rw [sub_add_cancel, ih] at hp; rw [eq_sub_of_add_eq hp.symm]; abel

variable [AddCommGroup E]
private def shift(j:Axis)(x:Cover)(t:ℤ):Cover:=update x j t
@[simp] private lemma shift_he(j:Axis)(x:Cover)(t:ℤ): shift j x t j=t:=by simp [shift]
@[simp] private lemma shift_next{j k:Axis}(g:k≠j)(x:Cover)(t:ℤ): shift j x t k=x k:=by simp [shift,g]
private lemma run_next(j:Axis)(x:Cover)(t:ℤ):shift j x (t+1)= shift j x t+ step j:= by
 ext k; by_cases h:k=j<;> simp [h,step_apply]
private lemma run_xt{j i:Axis}(u:j≠i)(x:Cover)(t:ℤ): shift j (x+step i) t=shift j x t+step i:= by ext k; by_cases h:k=j<;> simp [h,step_apply,u]
private lemma run_home(j:Axis)(x:Cover)(t:ℤ):shift j (x+step j) t=shift j x t:= by ext k; by_cases h:k=j<;> simp [h,step_apply]
private lemma run_stays(j:Axis)(x:Cover):shift j x (x j)=x:=by simp [shift]

def potential (a:Cover→Axis→E): List Axis→ Cover → E
 | []=>fun _=>0
 | j::l=> fun x=>potential a l (shift j x 0)+stint (fun t=>a (shift j x t) j) (x j)
abbrev axis_flux (a:Cover→Axis→E)(x:Cover)(j i:Axis):E:= a (x+step j) i - a x i -(a (x + step i) j - a x j)
def depose (Q:Cover→Axis→Axis→E):List Axis→ Cover → Axis→ E
 | [] => fun _ _=>0
 | j::l=>fun x i=> if j=i then 0 else depose Q l (shift j x 0) i + stint (fun t=>Q (shift j x t) j i) (x j)
lemma zone (a:Cover→Axis→E)(x:Cover){i:Axis}{l:List Axis}(h:i ∈ l):
 potential a l x + a x i-potential a l (x+step i)=depose (axis_flux a) l x i:=by
 induction l generalizing x with
 | nil=> cases List.not_mem_nil h
 | cons j l ih =>
    simp only [depose,potential]
    split
    · next v =>
      subst i
      simp only [run_home,Pi.add_apply,step_apply,ite_true]
      rw [stint_step,run_stays]; abel
    next p =>
    have v:i∈l:= (List.mem_cons.mp h).resolve_left (fun v=>p v.symm)
    simp only [run_xt p, Pi.add_apply,step_apply, if_neg p, add_zero,←ih _ v]
    let A:ℤ→E := fun t=> a (shift j x t) i
    let B:ℤ→E := fun t=> a (shift j x t) j
    let C:ℤ→E := fun t=> a (shift j x t+step i) j
    rw [show (fun t=>axis_flux a (shift j x t) j i) = ((fun t=> A (t+1)-A t) - (C-B):ℤ→E) from ?_,stint_sub,stint_sub,stint_flux]
    · dsimp only [A]
      rw [run_stays]; dsimp [C,B]; abel
    funext t; simp [A,B,C,axis_flux,run_next]
omit [AddCommGroup E] in
private lemma shift_inside {m:ℕ}(j:Axis){x:Cover}(h:x∈ box m){t:ℤ}(v:- (m:ℤ)≤t)(p:t≤m):shift j x t∈box m:=by
 apply box_test.mpr; obtain ⟨h,m'⟩:=box_test.mp h
 constructor <;> intro k<;> by_cases b:k=j
 · simpa [b]
 · rw [shift_next b]; exact h k
 · simpa [b]
 rw [shift_next b]; exact m' k
section
omit [AddCommGroup E]
variable {E₁:Type*}
private lemma stint_paid [NormedAddCommGroup E₁] {m:ℕ}(f:ℤ→E₁){z:ℤ}{C:ℝ}(hz:- (m:ℤ)≤z)(vz:z≤m)(c:0≤C)(g:∀ i:ℤ,-(m:ℤ)≤ i → i≤m → ‖f i‖ ≤ C):‖stint f z‖ ≤ m*C:=by
 unfold stint; split
 · next p=>
   refine (norm_sum_le ..).trans ((sum_le_sum (fun i t=>g i (by obtain ⟨_,_⟩:= mem_Ico.mp t;omega) (by obtain ⟨_,_⟩:=mem_Ico.mp t;omega))).trans ?_)
   rw [sum_const,Int.card_Ico,nsmul_eq_mul]; gcongr; omega
 next p=>
 rw [norm_neg]
 refine (norm_sum_le ..).trans ((sum_le_sum (fun i t=>g i (by obtain ⟨_,_⟩:=mem_Ico.mp t;omega) (by obtain ⟨_,_⟩:=mem_Ico.mp t;omega))).trans ?_)
 rw [sum_const,Int.card_Ico,nsmul_eq_mul]; gcongr; omega

lemma wage [NormedAddCommGroup E₁](F:Cover→Axis→Axis→E₁)(l:List Axis)(i:Axis){m:ℕ}{x:Cover}(h:x∈box m){C:ℝ}(pC:0≤C)(p:∀ x∈box m,∀i j, ‖F x i j‖ ≤ C): ‖depose F l x i‖ ≤ (l.length*m:ℕ)*C :=by
 induction l generalizing x with
 | nil => simp [depose]
 | cons j l ih=>
   rw [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.cast_add,add_mul,depose]; dsimp only; split
   · rw [norm_zero]; positivity
   obtain ⟨a,b⟩:=box_test.mp h; refine (norm_add_le ..).trans (add_le_add (ih (shift_inside j h (by omega) (by omega))) (stint_paid _ (a _) (b _) pC fun k e r=>p _ (shift_inside j h e r) j i))
end
lemma stint_scale [Module ℝ E](a:ℝ)(f:ℤ→E)(t:ℤ):stint (a • f) t=a • stint f t:=by unfold stint; split <;> simp [Finset.smul_sum]
def deposeLinear [Module ℝ E] (l:List Axis)(x:Cover)(i:Axis):(Cover→Axis→Axis→E) →ₗ[ℝ] E:=
 {toFun:=fun F=>depose F l x i
  map_add':=by intro F T; induction l generalizing x with
             | nil=>simp [depose]
             | cons j l ih=>
               rw [depose,depose,depose]; dsimp only; split
               · simp_all
               next v=> rw [ih,show (fun t=>(F+T) (shift j x t) j i) = (fun t=>F (shift j x t) j i)+(fun t=>T (shift j x t) j i) from rfl, stint_add]; abel
  map_smul':=by intro a F; induction l generalizing x with
               | nil=>simp [depose]
               | cons j l ih=>
                 rw [depose,depose]; dsimp only; split
                 · simp_all
                 next v=>rw [smul_add,ih,show (fun t=> (a • F) (shift j x t) j i)=a • (fun t=> F (shift j x t) j i) from rfl,stint_scale]; rfl}
variable {n:Side}
private abbrev locus (o:Site n)(x:Site n) := lift (x-o)
abbrev port (o:Site n)(x:Cover) := (wrap n x)+o
lemma inlet (o x:Site n):port o (locus o x)=x:=by simp [port,locus]
lemma unroll (o:Site n){x:Cover}{m:ℕ}(hx:x∈box m)(g:2*m<n.val): locus o (port o x)=x:=by
 unfold locus port;rw [add_sub_cancel_right]; apply lift_eq_iff.mpr ⟨rfl,?_⟩; intro j; obtain ⟨a,b⟩:=box_test.mp hx; have h:=a j; have ht:=b j; omega
abbrev veh (o:Site n)(f: Edge (Site n) → E)(x:Cover)(i:Axis):= f (port o x,i)
open Wilson Laurent RG
abbrev rent (Q:(Site n × PlaqAxes)→E)(x:Site n)(i j:Axis):E:= if h:i<j then Q (x,⟨(i,j),h⟩) else if v:j< i then -(Q (x,⟨(j,i),v⟩)) else 0 -- (Site n × PlaqAxes)amespace?
open RG Wilson Exterior
abbrev collar (f: Edge (Site n) → E)(p:(Site n × PlaqAxes)):E:= let i:=p.2.1.1; let j:=p.2.1.2; f (p.1+step i,j)- f (p.1,j) -(f (p.1+step j,i)- f (p.1,i))
lemma shed (f: Edge (Site n)→ E)(o:Site n) : (axis_flux (veh o f))=fun x=>rent (collar f) (port o x):=by
 funext x i j; unfold axis_flux veh rent collar port; simp_rw [map_add,wrap_step]; split
 · simp only [add_right_comm _ (step i),add_right_comm _ (step j)]
 next v=> split
          · simp only [add_right_comm _ (step i),add_right_comm _ (step j)]; abel
          next w=> have : i=j := le_antisymm (le_of_not_gt w) (le_of_not_gt v);subst j
                   abel
def stitch (o:Site n)(Q:Site n × PlaqAxes→ E)(i:Edge (Site n)):E:= depose (fun x=> rent Q (port o x)) (List.finRange 4) (locus o i.1) i.2
private lemma airing(o:Site n){m:ℕ}{x:Site n}(p:separation o x ≤m):locus o x∈box m:= lift_mem_box (x:=o) p
private def currency(o:Site n)(f: Edge (Site n)→ E)(x:Site n):=potential (veh o f) (List.finRange 4) (locus o x)
lemma curl_in (o:Site n)(f:Edge (Site n) → E) : ∃ P:Site n→E, ∀ {m:ℕ}(i:Edge (Site n)),separation o i.1 ≤m → 2*(m+1)<n.val→P i.1 + f i-P (i.1+step i.2)=stitch o (collar f) i:=by
 refine ⟨currency o f,fun {m} i h w=>?_⟩
 let p:=locus o i.1; let k:=i.2
 have h':p+step k ∈ box (m+1):= by
   apply box_test.mpr; obtain ⟨a,b⟩:=box_test.mp (airing o h)
   constructor <;> intro j <;> have t:= a j <;> have v:= b j <;> simp only [p,Pi.add_apply,step_apply] <;> split <;>omega
 have t:port o (p+step k)=i.1+step i.2:=by unfold port; rw [map_add,wrap_step,add_right_comm]; change port _ _ + _=_; rw [inlet]
 have e:locus o (i.1+step k)=p+step k:=by rw [←t]; exact unroll o h' w
 have b:veh o f p k=f i:=by unfold veh p; rw [inlet]
 unfold currency stitch; rw [e,←b,zone _ _ (List.mem_finRange _),shed]

variable [Module ℝ E]
def income (o: Site n)(i:Edge (Site n)): ((Site n × PlaqAxes)→ E) →ₗ[ℝ] E :=
 (deposeLinear (List.finRange 4) (locus o i.1) i.2).comp ({
 toFun:=(fun Q x=>rent Q (port o x))
 map_add':= by intro x y; funext z i j; simp only [Pi.add_apply]; unfold rent; split <;> first|rfl|split <;> simp [Pi.add_apply,add_comm]
 map_smul':= by intro x y; funext z i j; simp only [RingHom.id_apply,Pi.smul_apply]; unfold rent; split <;> first | rfl | split <;> simp [Pi.smul_apply] } : ((Site n × PlaqAxes)→ E) →ₗ[ℝ] (Cover→Axis→Axis→ E))
lemma income_stitch (o:Site n)(i:Edge (Site n))(Q:Site n × PlaqAxes → E): income o i Q=stitch o Q i:=rfl

variable {E₁:Type*} [NormedAddCommGroup E₁]
lemma income_local_bound {m:ℕ}(o:Site n){i:Edge (Site n)}(v:separation o i.1 ≤ m)(Q:Site n × PlaqAxes → E₁){C:ℝ}(p:∀x:Site n,separation o x≤m → ∀j,‖Q (x,j)‖≤C): ‖stitch o Q i‖ ≤ 4*(m:ℝ)*C:=by
 let z:PlaqAxes:= ⟨(0,1),by decide⟩;have h:0 ≤ C:=(norm_nonneg _).trans (p o (by rw [separation_self]; omega) z)
 unfold stitch
 have hx:4*(m:ℝ)=(↑((List.finRange 4).length *m:ℕ):ℝ):=by simp
 rw [hx]; apply wage _ _ _ (airing o v) h; intro x s j k; unfold rent; split
 · exact p _ (separation_box_add o s) _
 split
 · rw [norm_neg]; exact p _ (separation_box_add o s) _
 rw [norm_zero]; exact h
#print axioms curl_in
