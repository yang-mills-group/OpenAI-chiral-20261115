import YM.CF.BPress.Assignment
/-! Eq for gauge fixing (VolumeB-gate end). Construct gauge shift on actual links; N can glue the action from the BOTH gaps (its stores end before cut); D must remain fixed. Buys independently of tags and other factor values. Doing these two gauges as one forest shift, still preserves free Haar conditionals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bands
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Sheet Tunnel Finset
open scoped Topology BigOperators Classical Matrix
variable {s : Side}{B : BandWidth} (X : Bands s B) (U : Micro s)
def arcF (i : X.Index)(k:ℕ) := if i ∈ X.dc then (X.ditch i).fores U k else (X.ditch i).rears U (B.D-k)
def restF (i : X.Index) (k : ℕ) := if i∈X.dc then 1 else (X.mark i).access (X.arcF U (i-1) B.D) (X.arcF U i 0) k * (X.mark i).along U k
lemma restF_o (i:X.Index): X.restF U i 0=X.arcF U (i-1) B.D:=by
 unfold restF; split; next h=> rw [arcF,if_neg _,Nat.sub_self,rears]; simp [X.next_prev,(X.dc_index _).mp h]
 next h=> rw [access,if_pos (Nat.zero_le _),along,access,if_pos (Nat.zero_le _),fores,mul_one]
lemma restF_last (i:X.Index): X.restF U i B.marked.val=X.arcF U i 0:=by
 unfold restF; split; next h=> rw [arcF,if_pos h,fores]
 rw [access,if_neg ((show (X.mark i).cut<B.marked.val from (X.mark i).cut_lt).not_ge),along,access,if_neg ((show (X.mark i).cut<B.marked.val from (X.mark i).cut_lt).not_ge),X.mark_n i, Nat.sub_self,rears,mul_one]
def reader (x:X.Index × Fin B.full.val) : HFrame s:= if x.2.val ≤ B.marked.val then X.restF U x.1 x.2.val else X.arcF U x.1 (x.2.val-B.marked.val)
def arrange : Mach s:= fun x=> X.reader U (X.clock.symm (x 0)) (Fin.tail x)
lemma arranged (u:X.Index × Fin B.full.val): confine (X.clock u) (X.arrange U)=X.reader U u:=by funext i; rw [confine,arrange,event_time,X.clock.symm_apply_apply]; simp [event]
lemma arrive_book (i:X.Index){k:ℕ} (v:k≤ B.marked.val): confine ((X.mark i).rise k) (X.arrange U)=X.restF U i k:=by rw [X.mark_clock _ (lt_of_le_of_lt v B.marked_lt),X.arranged, reader, if_pos v]
lemma arrive_ditch (i:X.Index){k:ℕ}(v:k ≤ B.D): confine ((X.ditch i).rise k) (X.arrange U)=X.arcF U i k:=by
 rcases lt_or_eq_of_le v with v|v; rw [X.ditch_clock i v, X.arranged,reader]; dsimp only; split
 · rw [show k=0 by omega,Nat.add_zero,X.restF_last]
 · rw [Nat.add_sub_cancel_left]
 subst k; rw [show (X.ditch i).rise B.D=_ from X.ditch_last i, ← X.mark_o (i+1), ← (X.mark (i+1)).rise_zero,X.arrive_book U _ (Nat.zero_le _),X.restF_o,add_sub_cancel_right]

lemma fixes_D (i:X.Index)(g:i∈X.dc): Set.EqOn (X.arrange U) 1 (X.band i):=by
 intro x h; obtain ⟨k,a,b⟩:= (X.mark i).internal _|>.mp h
 have hv:= congrFun (X.arrive_book U i a) (Fin.tail x); rw [restF,if_pos g,confine,←b,event_eta] at hv; exact hv
lemma poles_zero_gap (i:X.Index) (x:Link s)(v:x∈X.gaps i): gauge (X.arrange U) U x=1:=by
 obtain ⟨k,u,p,rfl⟩:= X.gaps_b i x|>.mp v; let A:=X.ditch i; let b(k)(p:k≤B.D):= X.arrive_ditch U i p; by_cases h:i∈X.dc; exact congrFun (A.flatF_eq U _ ((b _ u.le).trans (if_pos h)) ((b _ u).trans (if_pos h))) p; exact congrFun (A.flatR_eq U _ u ((b _ u.le).trans (if_neg h)) ((b _ u).trans (if_neg h))) p -- tune
lemma poles_zero_N (i:X.Index)(x:Link s)(v:x∈ X.storesN i): gauge (X.arrange U) U x=1:=by
 obtain ⟨w,v⟩:= X.store_h i v; have h:i∉X.dc:= fun h=> w ((X.dc_index _).mp h); obtain ⟨k,l,g,x,rfl⟩:= Tunnel.stores_eq _|>.mp v -- tune shadow
 let W:= X.mark i; let f:= W.access (X.arcF U (i-1) B.D) (X.arcF U i 0); let U':= X.arrange U; have hh : f k=f (k+1):=by unfold f access W; split_ifs <;> first| omega| rfl
 have hg(k)(v:k≤W.n.val) : confine (W.rise k) U'=f k*W.along U k:= (X.arrive_book U i v).trans (if_neg h)
 change normal (W.rise k) (gauge U' U) x=1; rw [vl_gauge,←rise_succ,hg k l.le,hg (k+1) l, hh]; let z:=W.along U k; have he := congrFun (W.orient_uncut U l g) x; rw [Tunnel.orient,vl_gauge,←rise_succ,axial,W.booked _ l,W.booked _ l.le] at he; change _=1 at he; simp only [Pi.mul_apply]; exact Eq.trans (show _= f (k+1) x* _*(f (k+1) x)⁻¹ from (Eq.symm (show f (k+1) x*(W.along U k x*normal (W.rise k) U x*(W.along U (k+1) x)⁻¹)*(f (k+1) x)⁻¹=_ from by group))) (by rw [he,mul_one,mul_inv_cancel]) -- tune
lemma poles_zero (x:Link s)(p:x∈X.poles): gauge (X.arrange U) U x=1:=by rcases mem_union.mp p with v|v <;> obtain ⟨i,_,h⟩:= mem_biUnion.mp v; exact X.poles_zero_gap U i x h; exact X.poles_zero_N U i x h
@[fun_prop] lemma cont_arrange : Continuous X.arrange:=by
 have ht(i:X.Index)(k:ℕ) : Continuous (fun U=> X.arcF U i k):= by unfold arcF; split; exact Tunnel.fore_cont ..; exact Tunnel.rear_cont ..
 have he (i:X.Index)(k:ℕ) : Continuous (fun U=> X.restF U i k):= by
   unfold restF; split; exact continuous_const; unfold along access; split <;> exact (ht ..).mul (by first| exact Tunnel.fore_cont ..| exact Tunnel.rear_cont ..)
 have hp(i) : Continuous (fun U=> X.reader U i):= by unfold reader; split; exact he ..; exact ht ..
 apply continuous_pi; intro x; exact (continuous_apply (Fin.tail x)).comp (hp (X.clock.symm (x 0)))
lemma agree_p {V : Micro s}(t:Set.EqOn U V X.poles) : X.arrange U=X.arrange V:=by
 have h (i:X.Index)(k:ℕ)(p:k ≤ B.D): X.arcF U i k=X.arcF V i k:=by
    have e (l : ℕ)(h:l<B.D): normal ((X.ditch i).rise l) U= normal ((X.ditch i).rise l) V:= funext fun x=> t (X.poles_g i ((X.gaps_b ..).mpr ⟨l,h,x,rfl⟩))
    unfold arcF; split; exact (X.ditch i).fores_only U fun a l=>e a (by omega)
    apply Tunnel.rears_only; intro l h; rw [Tunnel.fall,X.ditch_n]; exact e _ (by omega)
 have hp(i:X.Index × Fin B.full.val) : X.reader U i=X.reader V i:= by
    unfold reader restF; have hx:= B.full_eq; have hb:= i.2.isLt; split_ifs with p q; rfl; rw [h _ _ le_rfl,h _ _ (Nat.zero_le _),(X.mark i.1).along_only U p (show Set.EqOn U V (X.mark i.1).stores from fun a t'=> t (X.poles_s i.1 (by unfold storesN; rw [if_neg q]; exact t')))]; exact h _ _ (by omega)
 funext x; unfold arrange; rw [hp]
end YM.CF.BPress.Bands
