import YM.CF.BPress.Grid.Half
/-! Dyadic bounds, one set of axes in staggered refinement. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid.Half
open Function Filter Lattice MeasureTheory Finset SU Cube
open scoped Topology BigOperators Classical
variable {s : Side} {r d : ℕ}
def stride (r : ℕ) (S : Finset (Fin d))(i:Fin d):= if i∈S then r else r+r
def nodeM (r : ℕ)(S:Finset (Fin d)):= {x:Space d s| ∀ i, aligned (x i) (stride r S i)}
lemma nodeM_mono {S T : Finset (Fin d)} (h:S⊆ T){x:Space d s}(p:x∈nodeM r S): x ∈ nodeM r T:=by
 have hp (i:Fin d) : aligned (x i) (stride r S i):=p i; intro i; by_cases t:i∈ T; swap; · simpa only [stride,t,if_false,(mt (fun p:i∈S=>h p) t)] using hp i
 change aligned (x i) _; have hh(i): r ∣ stride r S i:=by unfold stride; split; rfl; simp
 rw [stride,if_pos t]; exact dvd_trans (hh i) (hp i)
@[simp] lemma nodeM_empty (s:Side)(r d:ℕ): nodeM (s:=s) (d:=d) r ∅= mesh (r+r):=by simp [nodeM,mesh,stride]
@[simp] lemma nodeM_all (s:Side)(r d:ℕ): nodeM (s:=s) (d:=d) r univ=mesh r:=by simp [nodeM,stride,mesh]
lemma subnodeM {x:Space d s}{S:Finset (Fin d)}(p:x∈nodeM r S): x∈mesh r:= nodeM_all s r d ▸ nodeM_mono (subset_univ _) p
lemma stride_dvd {S: Finset (Fin d)}(h:r+r∣s.val)(i): stride r S i∣s.val:=by unfold stride; split; exact dvd_trans (Nat.dvd_add (dvd_refl _) (dvd_refl _)) h; exact h
lemma advanceM (h:r+r∣s.val) (x:Space d s) (S:Finset (Fin d)) (i:Fin d)(l k:ℕ) (p:l=stride r S i*k):
    hop x i l∈nodeM r S ↔ x∈nodeM r S:=by
 have he:stride r S i ∣ l:= p ▸ dvd_mul_right ..
 unfold nodeM; simp only [Set.mem_setOf_eq]; apply forall_congr'; intro j; by_cases g:j=i; subst j; rw [hop_same]; exact ⟨fun p=> aligned_of_add (stride_dvd h _) _ p he,fun p=>aligned_add (stride_dvd h _) _ p he⟩
 rw [hop_diff x _ _ g]
lemma advance_one (h:r+r∣s.val)(x:Space d s)(S:Finset (Fin d))(i:Fin d): hop x i (stride r S i)∈nodeM r S ↔ x∈nodeM r S:= advanceM h x S i _ 1 (mul_one _).symm
lemma divides_half (h:r+r∣s.val) (u:Per s) (p:aligned u r) (t:0<r) : aligned (u+(r:Per s)) (r+r) ↔ ¬aligned u (r+r):=by
 have z : ¬(r+r∣ r):= fun H=> (not_lt.mpr (Nat.le_of_dvd t H)) (by omega)
 refine ⟨fun a v=>z ((aligned_add_iff h _ v r).mp a),fun k=>?_⟩
 unfold aligned at *; obtain ⟨l,L⟩:=p; rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod,L]; apply (Nat.dvd_mod_iff h).mpr
 rcases Nat.even_or_odd l with ⟨n,e⟩|⟨n,e⟩
 · exact (k ⟨n,by rw [L,e]; ring⟩).elim
 exact ⟨n+1,by rw [e]; ring⟩
lemma origin_agree {i j : Fin d}(p:i≠j)(S:Finset (Fin d))(r:ℕ): stride r (insert i S) j=stride r S j:=by simp [stride,Ne.symm p]
@[simp] lemma line_insert (S: Finset (Fin d))(i:Fin d)(r:ℕ):stride r (insert i S) i=r:=by simp [stride]
lemma flip_step (h:r+r∣s.val)(p:0<r) (x:Space d s)(S:Finset (Fin d)) {i:Fin d} (t:i∉S) (g:x∈nodeM r (insert i S)):
    hop x i r∈nodeM r S ↔ x∉nodeM r S:=by
 have he(j)(e:j≠i): aligned (x j) (stride r S j):= by rw [←origin_agree (Ne.symm e) S]; exact g j
 have hz:aligned (x i) r:= (subnodeM g) i
 have a:x∈nodeM r S ↔ aligned (x i) (r+r):= by refine ⟨fun a=> ?_, fun l (j:Fin d)=>?_ ⟩; have h:aligned _ (stride r S i):= a i; simpa [stride,t] using h; by_cases e:j=i; subst j; simpa [stride,t] using l; exact he _ e
 rw [a,← divides_half h _ hz p]; refine ⟨fun x=> ?_,fun a (j:Fin d)=> ?_⟩
 · have h:aligned _ (stride r S i):= x i; simpa [stride,t] using h
 change aligned (hop x i r j) _; by_cases p:j=i; subst j; simpa [stride,t] using a; rw [hop_diff x _ _ p]; exact he _ p

-- full-sized error bound a (half along already-polished axes). one step degrades by charge proportional a^2+m*r^2. independent of grid size.
variable (P: Method) (S:Finset (Fin d)) (U:GaugeField group d s) (F:Fabric d s E) (i:Fin d)
def ahead (x : Space d s) (i:Fin d):= hop x i r  -- r explicit?
def polish (r:ℕ) (x:Space d s) :=
    if x∈nodeM r S then F x else P.pick (F (backs x i r)*pad r U (backs x i r,i), F (hop x i r)*(pad r U (x,i))⁻¹)
def fee (S:Finset (Fin d))(a : ℝ) (i:Fin d) := if i∈S then a/2 else a
def Nice (r:ℕ)(a:ℝ):Prop:= ∀ x∈nodeM r S,∀ i:Fin d, chord (F x * line U x i (stride r S i)) (F (hop x i (stride r S i))) ≤ fee S a i
lemma nice_weaken {a b:ℝ} (p: Nice S U F r a)(h:a≤b) : Nice S U F r b:= fun x v i=> (p x v i).trans (by unfold fee; split; gcongr; exact h)
def ends (r:ℕ) (x:Space d s): E×E:= (F (backs x i r)*pad r U (backs x i r,i), F (hop x i r)*(pad r U (x,i))⁻¹)
lemma ends_bound {a:ℝ} (p:Nice S U F r a)(t:i∉S) (x: Space d s)(hx: backs x i r∈nodeM r S) : chord (ends U F i r x).1 (ends U F i r x).2 ≤ a := by
  have ht := p _ hx i; rw [stride,if_neg t,fee,if_neg t] at ht; unfold ends pad; rw [← chord.right _ _ (line U x i r)]; simpa [ends,line_cat,← hop_hop,mul_assoc] using ht -- simp loops?
private lemma parallel (h:r+r ∣ s.val)(S:Finset (Fin d))(x:Space d s)(i:Fin d) :
    hop x i r∈nodeM r (insert i S) ↔ x ∈ nodeM r (insert i S):=by simpa using advance_one h x (insert i S) i
lemma parentM (h:r+r∣s.val)(p:0<r)(t:i∉S)(x:Space d s)(u:x∉nodeM r S)(v:x∈nodeM r (insert i S)): backs x i r∈ nodeM r S := by
  let y:= backs x i r; have he: hop y i r=x:=hop_backs ..; have hv:=flip_step h p y S t ((parallel h S y i).mp (he.symm ▸ v)); rw [he] at hv; by_contra! hh; exact u (hv.mpr hh)

variable {S U F i}
lemma parallel_step {a δ K : ℝ} (hp:Price δ K)(ha:a<δ)(p: Nice S U F r a)(x : Space d s)(t:r+r∣s.val)(l:0<r) (z:x∈nodeM r (insert i S))(g:i∉S) :
    let f:=polish P S U F i r; chord (f x * line U x i r) (f (hop x i r))≤ a/2+K*a^2:=by
 intro f; let y:=hop x i r; have hy:y∈nodeM r (insert i S):=(parallel t S x i).mpr z; have ht:=flip_step t l _ _ g z
 have hx(v:Space d s)(p:v∈nodeM r S):f v=F v:=if_pos p; have he(v:Space d s)(p:v∉nodeM r S): f v=P.pick (ends U F i r v):= if_neg p
 by_cases k:x∈nodeM r S
 · have hl: y∉nodeM r S:= mt ht.mp (not_not.mpr k); have hq: x= backs y i r:= (backs_hop ..).symm; have hu:=hp.spanL (P:=P) _ _ ha (ends_bound S U F i p g y (hq ▸ k)); change chord _ (f y) ≤ _; rw [hx _ k,he _ hl,chord.comm]
   unfold ends y at *; simpa only [backs_hop,pad] using hu.1 -- tune
 have hw: y∈nodeM r S:= ht.mpr k; have hu:=hp.spanL (P:=P) _ _ ha (ends_bound S U F i p g x (parentM S i t l g x k z)); change chord _ (f y)≤ _; rw [he x k,hx y hw]; rw [←chord.right _ _ (line U x i r)⁻¹,mul_inv_cancel_right]; exact hu.2 -- tune via chord.right

-- through a square x→xi / y→yi. useful for both directions of midpoint
private lemma price_sq {a v x y u t : E}{m r : ℝ} (p : chord (x*v) (a*y)≤m)(g : chord (u*a) t≤r) : chord (u*x*v) (t*y) ≤ r+m := by
 refine (chord.triangle _ (u*a*y) _).trans ?_; rw [add_comm r]; apply add_le_add _ (chord.right ..|>.le.trans g); rw [mul_assoc,mul_assoc,chord.left]; exact p
private lemma invert_sq (a v x y : E) : chord (x⁻¹*a) (v*y⁻¹)= chord (x*v) (a*y) := by
 rw [← chord.left _ _ x,← chord.right _ _ y, mul_inv_cancel_left,mul_assoc x, inv_mul_cancel_right]; rw [chord.comm]
 -- tune
variable {δ K a m:ℝ}
lemma lateral {j : Fin d}(p:i∉S)(g:i≠j)(h:Flat U m)(hk:Nice S U F r a)(hr:Price δ K)(ha:a<δ)(t:r+r∣s.val) (r0:0<r)
    (x:Space d s)(e:x∈nodeM r (insert i S)) : let l:=stride r S j; let y:=hop x j l; let f:=polish P S U F i r
    chord (f x * line U x j l) (f y) ≤ (fee S a j + r*l*m) + 2*K*a^2:= by
  intro l y f; have hx:y∈nodeM r (insert i S):=by unfold y l; rw [← origin_agree g S r]; exact (advance_one t x _ j).mpr e -- tune
  have hy:y∈nodeM r S ↔ x∈nodeM r S:= advance_one t x S j; have hp:=h.positive; have hz:=hr.positive
  by_cases w:x∈nodeM r S
  · rw [show f x=F x from if_pos w, show f y=F y from if_pos (hy.mpr w)]; exact (hk x w j).trans ((le_add_of_nonneg_right (by positivity:r*l*m≥ (0:ℝ))).trans (le_add_of_nonneg_right (by positivity)))
  let X:= backs x i r; let Y:= backs y i r; let x':= hop x i r; let y':= hop y i r; have he:X∈nodeM r S:= parentM S i t r0 p x w e; have hX:=parentM S i t r0 p y (mt hy.mp w) hx
  rw [show f x=P.pick (ends U F i r x) from if_neg w, show f y=P.pick (ends U F i r y) from if_neg (mt hy.mp w)]
  apply hr.spanM _ _ _ _ _ ha (ends_bound S U F i hk p _ he) (ends_bound S U F i hk p _ hX) _
  · have hg : hop X j l= Y := by apply ((backs_eq ..).mp ?_: _ = backs y i r); rw [hop_comm, hop_backs]
    have E:=h.rect i j X r l; unfold tension at E; rw [hg,hop_backs] at E
    have t:=hk X he j; rw [show stride r S j=l from rfl, hg] at t; exact price_sq E t
  have E:=h.rect i j x r l; have hw:=hk x' ((flip_step t r0 x S p e).mpr w) j; rw [show stride r S j=l from rfl,hop_comm] at hw; unfold tension at E; rw [←invert_sq] at E; exact price_sq E hw
lemma one_axis (p:i∉S)(h:Flat U m)(hk:Nice S U F r a)(hr:Price δ K)(ha:a<δ)(t:r+r∣s.val)(r0:0<r):
   Nice (insert i S) U (polish P S U F i r) r (a+4*(r^2*m+K*a^2)):=by
  intro x e j; by_cases z:i=j
  · subst j; rw [line_insert,fee,if_pos (mem_insert_self ..)]; apply (parallel_step P hr ha hk x t r0 e p).trans; nlinarith [h.positive,hr.positive]
  rw [origin_agree z]; apply (lateral P p z h hk hr ha t r0 x e).trans; by_cases q:j∈S <;> simp only [stride,fee,q,if_true,if_false,Nat.cast_add,mem_insert,Ne.symm z, false_or] <;> nlinarith [h.positive,hr.positive]
-- tune expression `r^2*m` casts
end YM.CF.BPress.Grid.Half
