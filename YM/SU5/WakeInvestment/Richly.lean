import YM.SU5.WakeInvestment.Layout
import YM.CF.Buffered.Mark

/-!
Mirror-invariant ℓ¹ issue. Use unitary orientations in an intermediate language
`Cadre`. Pays polynomial in number of basis modes, **not** the number of mirror moves
in those foil switches. Issue literal finite spin words again in the end frame. No
loss of real-part comparison here. Can use also in high-volume pricing where sizes
in constructors might be large with cancellations. `Cadre` is an algebraic proof, not
an implicit budget always satisfied by a bounded chiral polynomial.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.WakeInvestment
open Function Filter Fock Lattice Finset NormedSpace
open Papyrus Papyrus.Franc
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I] [Fintype I] {A B : Op I}
variable {s t:Finset I} {r p q n m:ℕ} {v u E D:ℝ} {F G : FC I}

private abbrev Pants (I : Type*) [LinearOrder I][Fintype I] := List (ℂ × Cage I)
private abbrev volume (l:Pants I): ℝ:=(l.map (fun z=> ‖z.1‖)).sum
private lemma pee (l:Pants I) : 0 ≤ volume l:= List.sum_nonneg (by intro i h; obtain ⟨z,_,rfl⟩:= List.mem_map.mp h; positivity)
private abbrev pop (s:Finset I)(m:ℕ)(l:Pants I):= ∀ z∈l,z.2.length≤ m∧∀ i∈ z.2,i.2∈s
private lemma composeA (l l':Pants I)(u:pop s m l)(v:pop s m l') : pop s m (l++l'):=fun z p=> (List.mem_append.mp p).elim (u z) (v z)
private lemma use_cut (l l':Pants I) : useLine (l++l')=useLine l+useLine l':=by simp [useLine]
private lemma vol_cut (l l':Pants I) : volume (l++l')=volume l+volume l':=by simp [volume]

lemma Lyrics.source (l:Cage I)(u:∀ i∈l,i.2∈s) : Lyrics s l.length 1 (textSpin l):=by
 refine ⟨[(1,l)],?_,?_,?_⟩; · simp [useLine]
 · simp
 simpa using u
lemma Lyrics.nonneg (g:Lyrics s n E F): 0≤ E:=by obtain ⟨l,_,h,_⟩:=g; exact (pee l).trans h
lemma Lyrics.expend (g:Lyrics s n E F) (p:n≤ m) (v:E≤ D): Lyrics s m D F:=by obtain ⟨l,k,h,a⟩:=g; exact ⟨l,k,h.trans v,fun z w=>⟨((a z w).1).trans p,(a z w).2⟩⟩
lemma Lyrics.zeroS (s:Finset I)(n:ℕ): Lyrics s n 0 0 := ⟨[],rfl,le_rfl,by simp⟩
lemma Lyrics.unit (s:Finset I): Lyrics s 0 1 1:= Lyrics.source _ (by simp : ∀ i∈ ([]:Cage I),i.2 ∈ s)
lemma Lyrics.add (g:Lyrics s n E F) (t:Lyrics s n D G): Lyrics s n (E+D) (F+G):=by
 obtain ⟨l,h,u,f⟩:=g; obtain ⟨l',g,v,p⟩:=t
 refine ⟨l++l',?_,(vol_cut l l').le.trans (add_le_add u v),composeA l l' f p⟩ -- occurs f p?
 rw [use_cut,h,g]

private lemma volt_scale (z:ℂ)(l:Pants I) : volume (l.map fun a=>(z*a.1,a.2))= ‖z‖*volume l :=by
 induction l with|nil=> simp [volume]|cons i l ih=> change ‖z*i.fst‖ + volume _=‖z‖*(‖i.fst‖+volume l); rw [norm_mul,ih,mul_add]
private lemma use_scale (z:ℂ)(l:Pants I) : useLine (l.map fun a=>(z*a.1,a.2))= z • useLine l:= by induction l with|nil=> simp [useLine]|cons i l ih=> change (z*i.fst) • textSpin i.snd + useLine _=z • (i.fst • textSpin i.snd + useLine l); rw [mul_smul,ih,smul_add]
lemma Lyrics.scale (g:Lyrics s n E F)(z:ℂ): Lyrics s n (‖z‖*E) (z • F):=by
 obtain ⟨l,k,u,v⟩:=g; refine ⟨l.map fun a=>(z*a.1,a.2), (use_scale z l).trans ?_, (volt_scale z l).le.trans (mul_le_mul_of_nonneg_left u (norm_nonneg _)),?_⟩; rw [k]; intro w h; obtain ⟨a,e,rfl⟩:= List.mem_map.mp h; exact v a e

open Buffered
private lemma use_more (e:ℂ × Cage I) (g: Lyrics s n E F)(h: e.2.length≤ p) (t:∀ i∈e.2,i.2∈s): Lyrics s (n+p) (E*‖e.1‖) (F*(e.1 • textSpin e.2)):=by
 obtain ⟨l',rfl,u,v'⟩:=g; let U:Pants I:= l'.map fun z=>(z.1*e.1,z.2++e.2)
 suffices hm:∀ l':Pants I, useLine (l'.map (fun z=> (z.1*e.1,z.2++e.2)))= useLine l'*(e.1 • textSpin e.2)∧ volume (l'.map fun z=>(z.1*e.1,z.2++e.2))=volume l'*‖e.1‖ by
    refine ⟨U,(hm l').1,(hm l').2.le.trans (mul_le_mul_of_nonneg_right u (norm_nonneg _)),fun i g=>?_⟩
    obtain ⟨i,e1,rfl⟩:= List.mem_map.mp g; obtain ⟨u,w⟩:=v' i e1; refine ⟨List.length_append.le.trans (add_le_add u h),fun i j=>?_⟩; exact (List.mem_append.mp j).elim (w _) (t _)
 intro l; induction l with
 | nil=> simp [volume,useLine]
 | cons i l ih=>
    obtain ⟨a,b⟩:=ih; constructor
    · change (i.fst*e.fst) • textSpin (i.snd++e.snd) + useLine _ = (i.fst • textSpin i.snd+ useLine l)*(e.fst • textSpin e.snd); unfold textSpin; rw [List.map_append,List.prod_append,mul_smul]; unfold textSpin at a; rw [a,add_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,Algebra.mul_smul_comm]
    change ‖i.fst* e.fst‖ + volume _ = (‖i.fst‖+volume l)* _; rw [b,norm_mul,add_mul]
lemma Lyrics.mul (g:Lyrics s n E F)(u:Lyrics s m D G): Lyrics s (n+m) (E*D) (F*G):=by
 obtain ⟨l,rfl,v,w⟩:=u
 suffices h:∀ l:Pants I,pop s m l → Lyrics s (n+m) (E*volume l) (F*useLine l) by exact (h l w).expend le_rfl (mul_le_mul_of_nonneg_left v g.nonneg)
 intro l p; induction l with
 | nil=> simpa [useLine,volume] using (Lyrics.zeroS s (n+m))
 | cons i l ih=>
    change Lyrics _ _ (E*(‖i.fst‖+volume l)) (F* (i.fst • textSpin i.snd + useLine l)); rw [mul_add,mul_add]
    have ht:= p i List.mem_cons_self; have hp:pop s m l:=fun i v=>p i (List.mem_cons_of_mem _ v); exact (use_more i g ht.1 ht.2).add (ih hp)
lemma Lyrics.sumF {J:Type*}(S:Finset J){E:J→ℝ}{F:J→FC I}(v:∀ i∈S,Lyrics s n (E i) (F i)): Lyrics s n (∑ i∈S,E i) (∑ i∈S,F i):=by
 classical
 induction S using Finset.induction_on with|empty=> simp [Lyrics.zeroS]|insert i S h ih=> rw [sum_insert h,sum_insert h]; exact (v i (mem_insert_self ..)).add (ih fun i w=> v i (mem_insert_of_mem w))

lemma Lyrics.singleton (b:Bool)(i:I)(p:i∈s): Lyrics s 1 1 (Flare.ton (b,basisKet i)):=by
 rw [show Flare.ton (b,basisKet i)=textSpin [(b,i)] by unfold textSpin; rw [List.map_singleton,List.prod_singleton]; rfl]; exact Lyrics.source _ (by simpa using p)

lemma Lyrics.issue (b:Bool)(x:Ket I)(p:withinM s x)(v:‖x‖≤1): Lyrics s 1 ↑s.card (Flare.ton (b,x)):=by
 let f:=fun i:I=>if b then star (x.ofLp i) else x.ofLp i
 let F:=fun i:I=>f i • Flare.ton (b,basisKet i)
 rw [show Flare.ton (b,x)= ∑ i∈s,F i from ?_]; swap
 · have he:∀ i, i ∉ s→ F i=0:=by intro i h; unfold F f; rw [(within_test ..).mp p i h]; simp
   rw [Finset.sum_subset (subset_univ s) (fun i _ k=> he _ k)] -- sum_subset binder i explicit?
   unfold F f; cases b
   · change create x= _; simpa [Flare.ton,creed] using create_def x
   change Fock.remove x=_; simpa [Flare.ton,creed] using remove_def x
 refine (Lyrics.sumF s (fun i h=> Lyrics.scale (Lyrics.singleton b i h) (f i))).expend le_rfl ((Finset.sum_le_sum (g:=fun _=>1) ?_).trans_eq (by simp)); intro i w; rw [mul_one]; have ht:‖f i‖=‖x.ofLp i‖:=by cases b <;> simp [f];--
 rw [ht, ←basis_inner]; exact (norm_inner_le_norm (basisKet i) x).trans (by simpa [basisKet] using v)

/-- Intermediate language, cost survives movement by any unitary with those support licenses. -/
inductive Cadre (s:Finset I) : ℕ → ℝ → FC I→Prop where
 | zero (m:ℕ) : Cadre s m 0 0
 | unit : Cadre s 0 1 1
 | leaf(b:Bool)(v:Ket I) (p: withinM s v)(h:‖v‖≤1) : Cadre s 1 1 (Flare.ton (b,v))
 | scale {m : _}{v : _}{F : _} (q:Cadre s m v F)(w:ℂ) : Cadre s m (‖w‖*v) (w • F)
 | and_ {m : _}{n : _}{E : _}{v : _}{F : _}{G : _}(p:Cadre s m E F)(q:Cadre s n v G): Cadre s (m+n) (E*v) (F*G)
 | add {m : _}{E : _}{v : _}{F : _}{G : _}(p:Cadre s m E F)(q:Cadre s m v G): Cadre s m (E+v) (F+G)
 | buy {m : _}{n : _}{E : _}{v : _}{F : _}(p:Cadre s m E F)(q:m≤n)(k:E≤v): Cadre s n v F
-- inclusion when needed
lemma Cadre.cover (u: s⊆ t)(p:Cadre s n E F): Cadre t n E F:=by
 induction p with
 | zero v=> exact .zero _
 | unit=> exact .unit
 | leaf b v p e=> exact .leaf _ _ ((within_test ..).2 fun i h=> (within_test ..).1 p i (fun e=>h (u e))) e
 | scale _ w p=> exact p.scale w
 | and_ _ _ p q=> exact p.and_ q
 | add _ _ p q=> exact p.add q
 | buy _ q e p=> exact p.buy q e
lemma Cadre.sumF {J:Type*}(S:Finset J){E:J→ℝ}{F:J→FC I}(v:∀ i∈S,Cadre s n (E i) (F i)): Cadre s n (∑ i∈S,E i) (∑ i∈S,F i):=by
 classical
 induction S using Finset.induction_on with|empty=> simp [Cadre.zero]|insert i S h ih=> rw [sum_insert h,sum_insert h]; exact (v i (mem_insert_self ..)).add (ih fun i w=> v i (mem_insert_of_mem w))
lemma Cadre.march (p:Cadre s n E F)(U:UNI I)(g:twist U (cutM s)=cutM t): Cadre t n E (theta U F):=by
 induction p with
 | zero v=> rw [theta_zero]; exact .zero _
 | unit=> rw [theta_one]; exact .unit
 | leaf b v p e=>
    have hv: withinM t (acts U.val v):=by unfold withinM; rw [←g,twist_formula,←act_mul,mul_assoc (_*_),U.property.1,mul_one,act_mul,p]
    let X:=acts U.val v; have hu:‖X‖≤1:=by simpa [X] using e
    cases b
    · change Cadre t 1 1 (theta U (create v)); rw [theta_upV]; simpa [Flare.ton,creed,X] using (Cadre.leaf true X hv hu).scale (-Complex.I)
    change Cadre t 1 1 (theta U (Fock.remove v)); rw [theta_downV]; simpa [Flare.ton,creed,X] using (Cadre.leaf false X hv hu).scale Complex.I
 | scale p w ih=>rw [theta_smul]; simpa only [norm_star] using ih.scale (star w)
 | and_ _ _ p q=> rw [theta_mul]; exact p.and_ q
 | add _ _ p q=> rw [theta_add]; exact p.add q
 | buy _ q e p=> exact p.buy q e
lemma Cadre.price (p:Cadre s n E F) : ‖F‖≤E:=by
 induction p with
 | zero v=> exact (norm_zero ..).le
 | unit=> exact (norm_one ..).le
 | leaf b v p e=> exact le_trans (Flare.cost_pe b v) e
 | scale p w ih=> exact (norm_smul ..).le.trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
 | and_ _ _ p q=> exact (norm_mul_le ..).trans (mul_le_mul p q (norm_nonneg _) ((norm_nonneg _).trans p))
 | add _ _ p q=> exact (norm_add_le ..).trans (add_le_add p q)
 | buy _ _ e p=> exact p.trans e
lemma Cadre.output (p:Cadre s n E F) : Lyrics s n (E*(↑s.card+1)^n) F:=by
 let C:ℝ:= (s.card:ℝ)+1; have hc:1≤ C:=le_add_of_nonneg_left (Nat.cast_nonneg _); have hx:0≤ C:=zero_le_one.trans hc
 induction p with
 | zero v=> rw [zero_mul]; exact Lyrics.zeroS s _
 | unit=> simp [Lyrics.unit]
 | leaf b v p e=> rw [pow_one,one_mul]; exact (Lyrics.issue b v p e).expend le_rfl (le_add_of_nonneg_right zero_le_one)
 | scale p w ih=> rw [mul_assoc ‖w‖]; exact ih.scale w
 | and_ x y ih il=> refine (ih.mul il).expend le_rfl (le_of_eq ?_); rw [pow_add]; ring
 | add _ _ ih il=>rw [add_mul]; exact ih.add il
 | buy p q e ih=> exact ih.expend q (mul_le_mul e (pow_le_pow_right₀ hc q) (pow_nonneg hx _) (((norm_nonneg _).trans p.price).trans e))
#print axioms Cadre.output
end YM.CF.WakeInvestment
