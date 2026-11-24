import YM.CF.BProof.Angular.Draw

/-! Cover labels so default-aligned sites are in the fixed center meaning; the sum before
integrating already uses this enumeration, choice-independent. Nonabelian insertion
may depend on the frames. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Gauge Mag CF.BProof.Face SU MeasureTheory Wilson Finset Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {s : Side} (a : Per s)(l:ℕ)(y:ℝ)(S:Hall s)(U:Config G s)
abbrev Signs (s : Side):= Bool × Space s → Fin 5

def peeks (D:Signs s) : Eyes s := fun i p=> orient S.K y (inlet a l U i) p (D (i,p))
lemma peek_inj : Injective (peeks a l y S U):=fun _ _ h=>funext fun ⟨i,p⟩=> center_inj (mul_right_cancel (congrFun (congrFun h i) p))
lemma peek_m (D:Signs s) : Measurable (fun U : Config G s=> peeks a l y S U D):=by
 apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro p; unfold peeks orient; apply measurable_const.mul; let A (U:Config G s):= label S.K y (inlet a l U i) p
 have hh(n:Fin 5):Measurable (fun U:Config G s=> A U n):= (label_c S.K y p n).comp (sheet_m (front a l i)).measurable
 have he: Measurable (fun U:Config G s=> nearIndex S.K y (inlet a l U i) p):= (near_c S.K y p).comp (sheet_m (front a l i)).measurable
 change Measurable (Function.uncurry A ∘ (fun U : Config G s => (U,nearIndex S.K y (inlet a l U i) p)))
 exact (measurable_from_prod_countable_left (f:=Function.uncurry A) hh).comp ((measurable_id (α:=Config G s)).prodMk he) -- tune

def Seen (K:Chart G)(y:ℝ) : Prop := ∀ s U p u, Mood (s:=s) K y U p u→ orbit u=orbit (lead (tilt K y U p))
lemma peek_w (h: Seen S.K y)(b:Eyes s)(hp:lifts a l y S U b):∃ F,peeks a l y S U F=b:=by
 have hh(i:Bool)(p:Space s):∃ j, b i p=orient S.K y (inlet a l U i) p j:=
    (fiber _ _).mp ((aisle ..).trans (h s _ _ _ ((hp i).1 p)).symm) -- tune
 choose F hF using hh
 exact ⟨fun x=> F x.1 x.2,funext fun i=>funext fun p=> (hF i p).symm⟩
lemma lifts_m : MeasurableSet {p:Config G s × Eyes s| lifts a l y S p.1 p.2}:=by
 unfold lifts inlet; simp only [Set.setOf_forall]; refine MeasurableSet.iInter fun i=>?_
 have he: Measurable (fun p : Config G s × Eyes s=> (sheet p.1 (front a l i),p.2 i)):=by fun_prop
 exact he (lift_c S.K y (s:=s)) -- tune
lemma peeks_local (he:l<s.val)(V:Config G s)(h:Agrees (↑(strip a l)) U V)(F:Signs s) : peeks a l y S U F=peeks a l y S V F:=by
 ext1 i; ext1 p; unfold peeks; rw [local_inlet a _ U _ he V h]

def wages := univ.filter (fun F=> lifts a l y S U (peeks a l y S U F))
@[simp] lemma wages_mem (F:Signs s) : F ∈ wages a l y S U ↔ lifts a l y S U (peeks a l y S U F):=by simp [wages]
lemma wages_local (he:l<s.val)(V:Config G s)(h:Agrees (↑(strip a l)) U V) : wages a l y S U=wages a l y S V:=by
 ext x; rw [wages_mem,wages_mem,peeks_local a _ y S U he V h]; apply forall_congr' (p:=fun i=>Lift S.K y _ _ ) -- simpler simp_rw
 intro i; rw [local_inlet a _ U i he V h]
lemma wage_m (F: Signs s) : MeasurableSet {U : Config G s| F ∈ wages a l y S U}:=by
 simp_rw [wages_mem]; exact (measurable_id.prodMk (peek_m a l y S F)) (lifts_m a l y S)

lemma wages_sum {K:Type*}[AddCommMonoid K](F D:Eyes s → K)(h:Seen S.K y)(t)
    (e:∀ b:Eyes s,lifts a l y S U b → F b=D (b*(eye a l t)⁻¹)):
    let W:=Lattice.gauge t U; ∑ p∈ wages a l y S U,F (peeks a l y S U p)= ∑ p∈ wages a l y S W,D (peeks a l y S W p):=by
 let P:= peeks a l y S U; let V:=Lattice.gauge t U; let D':=peeks a l y S V; let L(b:Eyes s):=lifts a l y S U b; let T:=eye a l t
 have hh(b:Eyes s): L b ↔ lifts a l y S V (b*T⁻¹):=lifts_rot ..
 choose! f hf using fun (p : Signs s)(hp:L (P p))=> peek_w a l y S V h (P p*T⁻¹) ((hh _).1 hp)
 refine sum_nbij f ?_ ?_ ?_ ?_
 · intro i hi; replace hi:= (wages_mem ..).1 (mem_coe.mp hi); apply mem_coe.mpr; apply (wages_mem ..).2; rw [hf i hi]; exact (hh _).1 hi
 · intro i hi j hj e; exact peek_inj a l y S U (mul_right_cancel ((hf i ((wages_mem ..).1 hi)).symm.trans ((congrArg D' e).trans (hf j ((wages_mem ..).1 hj))))) -- dots tune
 · intro j hj
   let u:= D' j; have hu:L (u*T):= (hh _).2 (by rw [mul_inv_cancel_right]; exact (wages_mem ..).1 (mem_coe.mp hj)); obtain ⟨p,hp⟩:= peek_w a l y S U h (u*T) hu
   rw [← hp] at hu; exact ⟨p,(wages_mem ..).mpr hu,peek_inj a l y S V (by rw [hf p hu]; rw [show P p= u*T from hp,mul_inv_cancel_right])⟩
 intro p hp; specialize hf p ((wages_mem ..).1 (mem_coe.mp hp)) -- nbij h?- tune
 rw [hf]; exact e _ ((wages_mem ..).1 hp)

/-- Sup count. Can afford a cruder version by volume s^3 per slot, but here we also
expose the 25-term bill. -/
lemma wages_p (h: Seen S.K y)(hp: ∀ i,(labelSet S.K y (inlet a l U i)).card ≤ 5): (wages a l y S U).card ≤ 25:= by
 let T:=wages a l y S U; let X(i:Bool):= labelSet S.K y (inlet a l U i)
 let D(i:Bool)(j):= labels S.K y (inlet a l U i) j
 have hh (i:Bool)(j)(hj:j∈T):∃ F, F∈ X i∧ D i F=peeks a l y S U j i:=by
   have he:= (wages_mem ..).1 (show j∈ wages a l y S U from ‹_›); have hi:=he i; let b:=peeks a l y S U j
   choose f hf using fun p=> (fiber _ _).mp (h _ _ _ _ (hi.1 p)).symm; have hf:D i f=b i:=funext fun p=> (hf p).symm; exact ⟨f,(test_label ..).2 (show Lift S.K y (inlet a l U i) (D i f) from hf.symm ▸ (show Lift S.K y (inlet a l U i) (b i) from hi)),hf⟩
 choose! f hF hf using hh
 let t:=X false×ˢ X true
 apply le_trans (b:=t.card) (card_le_card_of_injOn (fun j=> (f false j,f true j)) (fun x hx=> mem_product.mpr ⟨hF _ _ hx,hF _ _ hx⟩) (fun x hx y' hy h'=> peek_inj a l y S U (funext fun i=>?_)))
 · unfold t; rw [card_product]; exact Nat.mul_le_mul (hp _) (hp _)
 cases i; exact (hf false _ hx).symm.trans ((congrArg (D false) (congrArg Prod.fst h')).trans (hf _ _ hy)); exact (hf true _ hx).symm.trans ((congrArg (D true) (congrArg Prod.snd h')).trans (hf _ _ hy))
end YM.CF.BProof.Angular
