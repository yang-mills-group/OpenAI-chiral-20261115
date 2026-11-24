import YM.CF.BPress.Tunnel
/-!
Axial gauges with one or two fixed ends (leave arbitrary cut). Normal links except cuts set to identity. Measurability, locality, readings, covariance. For the gap use front or rear without cut (can purchase those as specialization of the same f functions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Tunnel
open Function MeasureTheory Lattice SU Mag Cube Grid Finset
open scoped Topology BigOperators Classical Matrix
variable {s : Side} (W : Tunnel s) (U : Micro s)

def fores : ℕ → HFrame s
 | 0 => 1
 | k+1 => fores k * normal (W.rise k) U
def rears : ℕ → HFrame s
 | 0 => 1
 | k+1 => rears k * (normal (W.fall (k+1)) U)⁻¹
lemma fore_cont (k:ℕ) : Continuous fun U=> W.fores U k:= by induction k with| zero=> exact continuous_const| succ k ih=> exact ih.mul (cont_normal _)
lemma rear_cont (k:ℕ) : Continuous fun U=> W.rears U k:= by induction k with| zero=> exact continuous_const| succ k ih=> exact ih.mul (cont_normal _).inv

lemma viewF (a : Mach s)(k:ℕ) : W.fores (gauge a U) k=confine W.o a * W.fores U k * (confine (W.rise k) a)⁻¹ := by
 induction k with
 | zero => simp [fores]
 | succ k ih=> rw [fores,ih,fores,rise_succ]; funext x; simp only [Pi.mul_apply,Pi.inv_apply,vl_gauge]; group
lemma viewR (a : Mach s){k:ℕ}(t:k≤W.n.val) : W.rears (gauge a U) k= confine W.last a * W.rears U k * (confine (W.fall k) a)⁻¹ := by
 induction k with
 | zero=> simp [rears]
 | succ k ih=> rw [rears,ih (by omega), rears]; funext x; simp only [Pi.mul_apply,Pi.inv_apply,vl_gauge]; rw [← W.fall_before t]; group
lemma fores_only {V : Micro s} {k:ℕ}(h : ∀ l<k, normal (W.rise l) U= normal (W.rise l) V) : W.fores U k=W.fores V k:=by
 induction k with|zero=>rfl|succ k ih=> rw [fores,fores, ih (fun l b=> h l (by omega)),h k (Nat.lt_succ_self _)]
lemma rears_only {V : Micro s}{k:ℕ}(p : ∀ l<k, normal (W.fall (l+1)) U=normal (W.fall (l+1)) V) : W.rears U k=W.rears V k:=by
 induction k with|zero=>rfl|succ k ih=> rw [rears,rears, ih (fun l b=>p l (by omega)),p k (Nat.lt_succ_self _)]

def access (α β : HFrame s) (k:ℕ) := if k≤W.cut then α else β
def along (k:ℕ) := W.access (W.fores U k) (W.rears U (W.n.val-k)) k
def axial := W.book (W.along U)
lemma axial_cont : Continuous W.axial:= by
 refine W.book_cont.comp (f:=fun U=> W.along U) (continuous_pi fun k=>?_ ); unfold along access; split; exact W.fore_cont _; exact W.rear_cont _
lemma axial_o : confine W.o (W.axial U)=1:= by nth_rw 1 [←W.rise_zero]; rw [axial,W.booked _ (Nat.zero_le _),along,access,if_pos (Nat.zero_le _),fores]
lemma axial_last : confine W.last (W.axial U)=1:= by rw [axial,W.booked _ le_rfl,along,access,if_neg W.cut_lt.not_ge,Nat.sub_self,rears]
def orient := Lattice.gauge (W.axial U) U
lemma orient_cont : Continuous W.orient:= gauge_joint.comp (f:=fun U=>(W.axial U,U)) (W.axial_cont.prodMk continuous_id)
lemma flatF_eq (a : Mach s) {k:ℕ}(h:confine (W.rise k) a= W.fores U k)(l:confine (W.rise (k+1)) a=W.fores U (k+1)) : normal (W.rise k) (gauge a U)=1:=by
 funext x; rw [vl_gauge,←rise_succ,h,l,fores, Pi.mul_apply, mul_inv_cancel]; rfl
lemma flatR_eq (a : Mach s) {k:ℕ}(t:k<W.n.val)(h:confine (W.rise k) a= W.rears U (W.n.val-k))(l:confine (W.rise (k+1)) a=W.rears U (W.n.val-(k+1))) : normal (W.rise k) (gauge a U)=1:=by
 have ht := W.n.property; let L:= W.n.val-(k+1); have hv: W.n.val-k=L+1:=by unfold L; omega
 funext x; rw [vl_gauge,←rise_succ,h,l,hv,rears,fall,Nat.sub_eq_iff_eq_add (by omega : L+1≤W.n.val)|>.mpr (by omega : W.n.val = k+(L+1))]; change _=1; simp only [Pi.mul_apply,Pi.inv_apply]; dsimp [L]; group -- tune
lemma orient_o : horizontal W.o (W.orient U)=horizontal W.o U:= by rw [orient,adj_gauge,axial_o,adjust_one]
lemma orient_last : horizontal W.last (W.orient U)=horizontal W.last U:= by rw [orient,adj_gauge,axial_last,adjust_one]
lemma orient_uncut {k:ℕ} (t:k<W.n.val)(h:k≠W.cut): normal (W.rise k) (W.orient U)=1:=by
 have he(W':ℕ)(p:W'≤ W.n.val) : confine (W.rise W') (W.axial U)=W.along U W':= W.booked _ p
 rcases lt_or_gt_of_ne h with p|p
 · refine W.flatF_eq U _ ((he k t.le).trans (if_pos p.le)) ((he (k+1) t).trans (if_pos p))
 exact W.flatR_eq U _ t ((he k t.le).trans (if_neg p.not_ge)) ((he (k+1) t).trans (if_neg (lt_of_lt_of_le p (Nat.le_succ k)).not_ge))

def stores := ((range W.n.val).erase W.cut ×ˢ univ).image fun e:ℕ × Tri s=> vl (W.rise e.1) e.2
lemma stores_eq {e : Link s} : e∈ W.stores ↔ ∃ k<W.n.val,k≠ W.cut ∧ ∃ x,e=vl (W.rise k) x:=by
 constructor
 · intro p; obtain ⟨⟨i,j⟩,v,rfl⟩:=mem_image.mp p; simp only [mem_product,mem_erase,mem_range] at v; exact ⟨i,v.1.2,v.1.1,j,rfl⟩
 rintro ⟨k,b,v,x,rfl⟩; apply mem_image_of_mem (a:=(k,x)); simp [v,b]
lemma stores_sub : W.stores⊆ inside W.mem:=fun e p=> by obtain ⟨k,t,_,x,rfl⟩:= W.stores_eq.mp p; exact W.normal_in x|>.mpr ⟨k,t,rfl⟩
lemma orient_trivial {e : Link s}(p:e∈ W.stores): W.orient U e=1 := by obtain ⟨k,t,v,x,rfl⟩:= W.stores_eq.mp p; exact congrFun (W.orient_uncut U t v) x
lemma along_only {k:ℕ}{V : Micro s}(t:k≤W.n.val)(p:Set.EqOn U V W.stores): W.along U k=W.along V k:=by
 have he(k)(t:k<W.n.val)(v:k≠W.cut): normal (W.rise k) U=normal (W.rise k) V:= funext fun x=> p (W.stores_eq.mpr ⟨k,t,v,x,rfl⟩)
 unfold along access; split; next g=> exact W.fores_only U fun i h=> he i (by omega) (by omega)
 next g => apply W.rears_only; intro i h; apply he (W.n.val-(i+1)) <;> omega
lemma axial_only {V : Micro s}(p:Set.EqOn U V W.stores): W.axial U=W.axial V:=by
 funext x; unfold axial book; split
 next t=>rw [W.along_only U ((arc_mem ..).mp t) p]
 next t=> rfl -- tune
lemma orient_local {V: Micro s} (p : Lattice.Agrees W.mem U V) : Lattice.Agrees W.mem (W.orient U) (W.orient V):=by
 have ht := W.axial_only U (show Set.EqOn U V W.stores from fun i h=> p i ((inside_iff ..).mp (W.stores_sub h)).1 ((inside_iff ..).mp (W.stores_sub h)).2); intro i a b; rw [orient,orient,ht,Lattice.gauge,Lattice.gauge,p i a b]

lemma along_gauge (a : Mach s){k:ℕ}(p:k≤W.n.val): W.along (gauge a U) k=W.access (confine W.o a) (confine W.last a) k * W.along U k * (confine (W.rise k) a)⁻¹:=by
 unfold along access; split; exact W.viewF ..; rw [W.viewR U a (Nat.sub_le ..),fall,Nat.sub_sub_self p]
def branch (a : Mach s) := W.access (confine W.o a) (confine W.last a)
def branchM (a : Mach s) := W.book (W.branch a)
lemma overlap (a : Mach s) : Set.EqOn (W.axial (gauge a U)*a) (W.branchM a * W.axial U) W.mem:=by
 intro x hx; let u:=(x 0-W.o).val; have hu:u≤ W.n.val:=(arc_mem ..).mp hx; have hs: W.rise u=x 0:=(time_eq ..).symm; simp only [Pi.mul_apply,axial,book,Finset.mem_coe.mp hx,↓reduceIte,branchM]; change W.along _ u _*_= _; rw [W.along_gauge U a hu, Pi.mul_apply,hs,Pi.inv_apply,confine,event_eta]; unfold branch; rw [Pi.mul_apply]; group; rfl
lemma orient_a (a : Mach s) : Lattice.Agrees W.mem (W.orient (gauge a U)) (gauge (W.branchM a) (W.orient U)):=by
 unfold orient; rw [gauge_trans,gauge_trans]; intro i x y; rw [Lattice.gauge,Lattice.gauge,W.overlap U a x,W.overlap U a y]
lemma branch_o (a : Mach s): confine W.o (W.branchM a)=confine W.o a:=by nth_rw 1 [←W.rise_zero]; rw [branchM,W.booked _ (Nat.zero_le _),branch,access,if_pos (Nat.zero_le _)]
lemma branch_last (a : Mach s): confine W.last (W.branchM a)=confine W.last a:=by rw [branchM,W.booked _ le_rfl,branch,access,if_neg W.cut_lt.not_ge]

lemma no_axial (h : ∀ i∈W.stores,U i=1): W.axial U=1:=by
 let A:Micro s:=1; have ht := W.axial_only U (V:=A) (fun _ x=>h _ x); rw [ht]
 funext x; change W.book _ _=1; have he(k): W.fores A k=1:=by induction k with| zero=> rfl| succ k ih=> rw [fores,ih,one_mul]; rfl
 have hx(k): W.rears A k=1:=by induction k with| zero=> rfl| succ k ih=> rw [rears,ih,one_mul]; exact inv_eq_one.mpr rfl
 unfold book along access; split; simp only [hx,he,ite_self]; rfl; rfl
lemma no_orient (h : ∀ i∈W.stores,U i=1): W.orient U=U:=by rw [orient,W.no_axial U h, gauge_self]
end YM.CF.BPress.Tunnel
