import YM.CF.BProof.Chess.Sermon
import YM.CF.BProof.Anthem.Waltz
/-! Step D-sew to B sheet. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter Metric NormedSpace Finset Lattice Cube Bide Spire Bide.Half RG Fock Lat Skye Scree
open scoped Matrix.Norms.L2Operator Matrix ComplexOrder Topology BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N L:Side}{s t h z P w:ℕ}
local notation "Trup"=> Scute N L 0 w
namespace Drift
variable (T: Bands (More N) L s P)
open Drum Scute Tack
abbrev lane :ℕ := 2^T.rP
abbrev axis := lane T+1 -- namespace abbrev tune
lemma size :field L (lane T)=P:=by apply Eq.trans _ (T.powP.symm); unfold lane field; ring -- dependent T issue P occurs T
lemma course : field L (axis T)=T.grid.count.val:=by rw [axis,field_add,size]; unfold field; rw [mul_one,T.lengths]
lemma pitch(k:ℕ): field L (axis T*k)=T.grid.count.val*k:=by rw [← course]; unfold field; ring
lemma vacantS{k:T.Index}(u:w≤ s): T.band k ⊆ regionD (drive N L 0 (axis T*k.val)) (span N L 0 (lane T) w):=by
 intro x t; obtain ⟨p,v⟩:= T.order_in (mem_strip.mp t); simp only [regionD,mem_map_equiv,Equiv.symm_symm,spans, drive_i]; refine ⟨_,u.trans p,(?_),?_⟩
 · rw [size]; exact (Nat.add_le_add_left u _).trans v
 have he:= add_along (T.blank_p k) (time x); rw [pitch,Nat.cast_mul,←base_nat,ZMod.natCast_zmod_val]; change time x-_=_; rw [sub_eq_iff_eq_add]; rw [← he]; simp [Bands.blank_p, add_comm]
lemma half_m (y:ℕ)(v:T.q.val = 2*y): halfC L N ((axis T)*y):=by
 unfold halfC; rw [pitch]; have hx:=(T.grid).exact_size; rw [v,natM] at hx; rw [mul_comm ((T.grid).count.val)]; rw [mul_assoc] at hx -- tune
 omega
lemma block_half :∃ z:ℕ, 0<z∧ T.q.val=2*(z*2^T.rP):=by
 obtain ⟨z,g⟩:=T.dyadicH; refine ⟨z,?_,?_⟩; · have hx:= T.enough; by_contra k; push Not at k; rw [Nat.le_zero.mp k,mul_zero] at g; omega
 rw [g,pow_succ]; ring
variable (F:T.Index→ Obs N)(p:∀ i,Allowed (T.band i) (F i))(e:w≤ s){A B C:ℝ}(v:∀ i,Paid (F i) C)
local notation "R" k:max => drive N L 0 ((axis T)*k)
local notation "Pt"=> Scute N L 0 w
def point (k:T.Index): Scute N L 0 w:=
 let U:=drive N L 0 (axis T*k.val)
 let t:=span N L 0 (lane T) w
 ⟨lane T,move U⁻¹ (F k), mode_p (movement (mode_p (p k) (vacantS T e)) rfl) (by change regionD U⁻¹ (regionD U t) ⊆ t; unfold regionD; rw [sitU,Finset.map_map]; intro x h; simpa using h)⟩
abbrev place(k:T.Index):= point T F p e k * vacant N L 0 w 1
def earlier (y:ℕ):List T.Index:= (List.range y).map (fun k:ℕ=> (k:T.Index))
abbrev roll (y:ℕ):= stack (place T F p e) (earlier T y)
abbrev px := Pairwise (Commute on F)
include p
lemma pxF :Pairwise (Commute on F):=fun i j u=> (p i).commute (p j) (T.band_disjoint u)
abbrev title := Anthem.edgeP F (pxF T F p) univ -- explicit p needed (implicit v?)
include e
lemma step_load(k:T.Index): move (R k.val) (place T F p e k).mark= F k:=by
 unfold place; rw [slash,mVac,moving_one,mul_one]; change move _ (move _ (F k)) = _; rw [dance _ _ (plain (p k)),inv_mul_cancel, move_e (plain (p k))]
lemma descend(z:ℕ)(h:z≤ T.q.val): (roll T F p e z).mark=((earlier T z).map F).prod:=by
 have he(y:ℕ): (roll T F p e y).length=(axis T)*y:=by
    unfold roll stack; rw [amount (s:=axis T) ?_, List.length_map]; simp only [earlier,List.length_map,List.length_range];
    intro k u; obtain ⟨x,h,g⟩:=List.mem_map.mp u; rw [←g]; rfl
 induction z with
 | zero=> simp [roll,earlier, stack]
 | succ k ih=>
    have ht:earlier T (k+1)=earlier T k++[(k:T.Index)]:=by simp [earlier,List.range_succ];
    let F':= place T F p e; let x:=(k:T.Index); have hz: x.val=k:= ZMod.val_natCast_of_lt (show k<T.q.val by omega)
    have hb: roll T F p e (k+1)= (roll T F p e k)*(F' (x)):=by rw [roll,ht,Tack.chat,show stack _ [(k:T.Index)]= F' x from ?_]; simp [stack,F',x] -- `simp [place]` tune
    have hp := step_load T F p e x; rw [hz] at hp
    rw [ht,hb, slash, ih (by omega), he,hp]; rw [List.map_append,List.prod_append,List.map_singleton,List.prod_singleton] -- tune
lemma form(k:ℕ)(h:T.q.val=k) : title T F p=(roll T F p e k).mark:=by
 rw [descend T F p e k h.ge]; let x:=earlier T k; have ht : x.toFinset=univ:=by
    apply Finset.eq_univ_of_forall; intro i; unfold x earlier; simp only [List.mem_toFinset,List.mem_map,List.mem_range]; exact ⟨i.val,h ▸ ZMod.val_lt i,ZMod.natCast_zmod_val _⟩ -- h order
 have hh:x.Nodup:=by unfold x earlier; refine (List.nodup_range).map_on fun i u j v e=> ?_; exact (ZMod.val_natCast_of_lt ((List.mem_range.mp u).trans_le h.ge)).symm.trans ((congrArg ZMod.val e).trans (ZMod.val_natCast_of_lt ((List.mem_range.mp v).trans_le h.ge))) -- trans type
 unfold title; rw [←ht]; exact Finset.noncommProd_toFinset x F _ hh
-- q aligns grid, wholew paid ≤ C^qval. height y x runtime.
include v
local instance (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩
lemma key (k:T.Index) : Drum.eligible (lane T) C (point T F p e k):= ⟨rfl,normD (s:=(drive N L 0 (axis T*k.val))⁻¹) (v k) rfl⟩
lemma serial(k:ℕ)(h:T.q.val=k) : Envelope (title T F p)∧ Paid (title T F p) (C^k):=by
 rw [form T F p e k h]; refine ⟨(roll T F p e k).permit.bounded,?_⟩; have he(k:T.Index): Paid (place T F p e k).mark C:= by unfold place; rw [slash,mVac,moving_one,mul_one]; exact (key T F p e v k).2
 unfold roll; have ht:(earlier T k).length=k:=by simp [earlier]
 nth_rw 2 [←ht]; generalize earlier T k=G; induction G with|nil=>rw [List.length_nil,pow_zero]; exact vCost 0|cons i d g=> rw [List.length_cons,pow_succ']; exact towerP _ _ (he i) g
variable {H:Obs N→ℝ} (D:Drum N L 0 w H)(K: Costed D (lane T) C A B)
include D K
theorem decides(j:ℕ)(h:0<j)(g:T.q.val=2*(j*2^T.rP)): H (title T F p)≤ A^(2*j*2^T.rP)*B^(2*j):=by
 let d:=earlier T T.q.val; let P' (x:T.Index):= place T F p e x; let x:=d.map (fun x=>(x,false)); have hx(k:T.Index): stamped (lane T) 1 1 C (P' k):= ⟨_,pair.coin (key T F p e v k), rfl⟩; have he(k:T.Index× Bool): either (lane T) 1 1 C (code P' k):=by rcases k with ⟨b,u⟩; cases u; exact Or.inl (hx b); exact Or.inr (by change stamped (lane T) 1 1 C ((P' b).bar.bar); rw [bar_b]; exact hx b)
 rw [form T F p e _ (rfl : T.q.val=T.q.val)]; have hp : roll T F p e T.q.val= stack (code P') x:=by unfold x roll; rw [stack, stack, List.map_map]; rfl
 rw [hp]; have ht:= K.path D j h T.rP 1 1 (by unfold lane; rw [one_mul]) (by rw [mul_one]; exact half_m T _ g) (T.Index×Bool) inferInstance (code P') Drum.jump (equip P' (fun i=> stampX (hx i))) he x (by simp [x,d,earlier,List.length_range,←g]); rw [one_mul] at ht; exact ht
end Drift
end YM.CF.BProof.Chess
