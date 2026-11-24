import YM.CF.BPress.Blend
/-! The template in axial coordinates of the N-band `eq:B-blend`, coming from cut links and horizontal links. Holds pointwise off excluded arguments (there fallback copies also in collars but no price assumed). All read from the two faces and assigned frames. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory Lattice SU Mag Cube Grid Filter Branch Sheet
open scoped Topology BigOperators Classical Matrix
variable {s : Side} {T : Atlas} {y C C' Lf : ℝ} {B : ℕ} (F : Net s T Lf y C C' B) (W : Tunnel s) (U V : Micro s)
open Tunnel
abbrev Duo (s : Side):= HFrame s × HFrame s
abbrev FacesH (s : Side):= Horiz s × Horiz s
def Tunnel.reads (W : Tunnel s)(U:Micro s) : FacesH s:= (horizontal W.o U,horizontal W.last U)
def Tunnel.framesE (W : Tunnel s)(h:Mach s): Duo s:= (confine W.o h,confine W.last h)
lemma Tunnel.reads_a (a:Mach s) : W.reads (gauge a U)=(adjust (W.framesE a).1 (W.reads U).1, adjust (W.framesE a).2 (W.reads U).2):= Prod.ext (adj_gauge ..) (adj_gauge ..)
lemma Tunnel.reads_orient : W.reads (W.orient U)= W.reads U:= Prod.ext (W.orient_o U) (W.orient_last U)
lemma Tunnel.reads_local : LocalOn W.mem W.reads:= fun U V p=> Prod.ext (Agrees.fl p W.o W.early) (Agrees.fl p W.last W.late)
@[fun_prop] lemma Tunnel.reads_cont : Continuous W.reads:=by unfold reads; fun_prop

def Tunnel.crown (W : Tunnel s) := Finset.univ.image (fl W.o) ∪ Finset.univ.image (fl W.last)
lemma Tunnel.crown_mem (i : Link s) : i∈W.crown ↔ ∃ x : FlatLink s,i=fl W.o x ∨ i=fl W.last x:= by simp [Tunnel.crown,exists_or, eq_comm]
lemma Tunnel.crown_sub : W.crown⊆inside W.mem:= fun i p=> by obtain ⟨x,v|v⟩:= W.crown_mem _|>.mp p; rw [v]; exact W.tang_in x|>.mpr ⟨0,Nat.zero_le _, W.rise_zero.symm⟩; rw [v]; exact W.tang_in x|>.mpr ⟨W.n.val,le_rfl,rfl⟩
lemma Tunnel.reads_crown (t : Set.EqOn U V W.crown) : W.reads U=W.reads V:= Prod.ext (funext fun x=> t ((W.crown_mem _).mpr ⟨x, Or.inl rfl⟩)) (funext fun x=> t ((W.crown_mem _).mpr ⟨x,Or.inr rfl⟩))
lemma Tunnel.crown_stores : Disjoint W.crown W.stores:= Finset.disjoint_left.mpr fun i p t=> by obtain ⟨j,x,_,u,rfl⟩:= W.stores_eq.mp t; obtain ⟨k,v|v⟩:= W.crown_mem _|>.mp p; all_goals exact fl_ne_vl _ _ _ _ v.symm
-- charged links exactly these
namespace Tunnel
def banks := inside W.mem \ (W.stores∪W.crown)
lemma banks_sub : W.banks ⊆ inside W.mem:= Finset.sdiff_subset
open Finset
lemma banks_tem (k:Link s) : k∈ W.banks ↔ (∃ i:Tri s,k=vl (W.rise W.cut) i) ∨ ∃ i < W.n.val, 0 < i ∧ ∃ x:FlatLink s, k=fl (W.rise i) x:=by
 simp only [banks,Finset.mem_sdiff,mem_union,not_or]; constructor
 · rintro ⟨t,u,v⟩; let l:= k.1 0; rcases link_cases k with ⟨i,p⟩|p; right; rw [p] at t v; obtain ⟨j,h,e⟩:= W.tang_in i|>.mp t; change l=_ at e; rw [W.crown_mem] at v; change k=fl l i at p; have he:l≠W.o ∧ l ≠ W.last:=by constructor; intro h; apply v; exact ⟨i,Or.inl (fl_eq.mpr ⟨h,rfl⟩)⟩; intro h; exact v ⟨i, Or.inr (fl_eq.mpr ⟨h,rfl⟩)⟩
   refine ⟨j, lt_of_le_of_ne h (fun g=> he.2 (by rw [e,g])), Nat.pos_of_ne_zero (fun g=> he.1 (by rw [e,g,rise_zero])),i,by rw [←e,p]
    ⟩; rw [p] at t; obtain ⟨j,h,f⟩:= W.normal_in _|>.mp t; change l=_ at f; left; by_cases x:j=W.cut; exact ⟨Fin.tail k.1, by change k=_ at p; rw [x] at f; rw [←f]; exact p⟩; exact False.elim (u (W.stores_eq.mpr ⟨j,h,x,_,show k=vl (W.rise j) (Fin.tail k.1) from p.trans (congrArg (fun a=>vl a _) f)⟩))
 rintro (⟨i,rfl⟩|⟨k,t,x,i,rfl⟩); refine ⟨W.normal_in i|>.mpr ⟨W.cut, W.cut_lt,rfl⟩,?_,?_⟩
 · intro p; obtain ⟨j,t,u,w,e⟩:=W.stores_eq.mp p; exact u (W.rise_inj (by omega) (W.cut_lt.le.trans (Nat.le_succ _)) (vl_eq.mp e).1.symm)
 · intro p; obtain ⟨i,h|h⟩:= W.crown_mem _|>.mp p; all_goals exact fl_ne_vl _ _ _ _ h.symm
 refine ⟨(W.tang_in i).mpr ⟨k,t.le,rfl⟩,fun p=> ?_,fun p=> ?_⟩
 · obtain ⟨j,_,_,w,e⟩:= W.stores_eq.mp p; exact fl_ne_vl _ _ _ _ e
 obtain ⟨j,h|h⟩:=W.crown_mem _|>.mp p; exact x.ne' (W.rise_inj (by omega) (by omega) ((fl_eq.mp h).1.trans W.rise_zero.symm)); exact t.ne (W.rise_inj (by omega) (by omega) (fl_eq.mp h).1)
end Tunnel
namespace Net
variable (x : FacesH s)(p : Duo s)
def fill : Duo s:= (F.frame x.1 p.1, F.frame x.2 p.2)
def deck (k:ℕ) := W.access (F.fill x p).1 (F.fill x p).2 k
def built (k:ℕ) : Horiz s:= fun i=> chord.blend T.toChart (W.progress k) (adjust (F.fill x p).1 x.1 i) (adjust (F.fill x p).2 x.2 i)
-- product template in axial coordinates: direct copies at quarters due to fallback
-- even for invalid fields
def tarH (k:ℕ) := adjust (F.deck W x p k)⁻¹ (F.built W x p k)
def tarV (k:ℕ) : HFrame s:= (F.deck W x p k)⁻¹ * F.deck W x p (k+1)
def template (x : FacesH s)(p : Duo s) : Micro s:= fun i=> let t:=(i.1 0 - W.o).val; Fin.cases (F.tarV W x p t (Fin.tail i.1)) (fun k=> F.tarH W x p t (Fin.tail i.1,k)) i.2
lemma readH {k:ℕ}(h:k ≤ W.n.val) : horizontal (W.rise k) (F.template W x p)= F.tarH W x p k:=by
 funext i; unfold horizontal template fl; simp only [event_time,W.rise_val (by omega : k ≤ W.n.val+1),Fin.cases_succ]; simp [event]
lemma readV {k:ℕ}(h:k<W.n.val) : normal (W.rise k) (F.template W x p) =F.tarV W x p k:= by funext i; unfold normal template vl; simp only [event_time,W.rise_val (by omega : k ≤ W.n.val+1),Fin.cases_zero]; simp [event]
lemma built_o {k:ℕ}(h:k≤W.lips) : F.built W x p k= adjust (F.fill x p).1 x.1:=funext fun i=>by rw [built,W.starts h,chord.blend_zero]
lemma built_last {k:ℕ}(h:W.lip ≤ k): F.built W x p k=adjust (F.fill x p).2 x.2:=funext fun i=>by rw [built,W.ends h,chord.blend_one]
lemma tar_o {k:ℕ}(h:k≤W.lips) : F.tarH W x p k=x.1:=by rw [tarH,deck,access,if_pos (h.trans W.collar_ends.1),F.built_o W x p h, adjust_seq,inv_mul_cancel,adjust_one]
lemma tar_last {k:ℕ}(h:W.lip ≤ k) : F.tarH W x p k=x.2:=by rw [tarH,deck,access,if_neg (lt_of_lt_of_le W.collar_ends.2.1 h).not_ge,F.built_last W x p h, adjust_seq,inv_mul_cancel,adjust_one]
lemma tar_plain {k:ℕ}(h:k≠ W.cut) : F.tarV W x p k=1:=by unfold tarV deck access; split_ifs <;> first| omega| exact inv_mul_cancel _
lemma tar_cut : F.tarV W x p W.cut=(F.fill x p).1⁻¹*(F.fill x p).2:=by rw [tarV,deck,deck,access,access,if_pos le_rfl,if_neg (Nat.lt_succ_self _).not_ge]

lemma deck_meas (k:ℕ) : Measurable fun x:FacesH s× Duo s=> F.deck W x.1 x.2 k:= by
 unfold deck fill access; dsimp only; split; exact F.frame_meas.comp (f:=fun x : FacesH s × Duo s=> (x.1.1,x.2.1)) ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)); exact F.frame_meas.comp (f:=fun x : FacesH s × Duo s=> (x.1.2,x.2.2)) ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
lemma template_meas : Measurable (fun x:FacesH s × Duo s=> F.template W x.1 x.2):=by
 have b: Measurable fun x:FacesH s × Duo s=> F.fill x.1 x.2:= Measurable.prodMk (F.frame_meas.comp (f:=fun x : FacesH s × Duo s=> (x.1.1,x.2.1)) ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))) (F.frame_meas.comp (f:=fun x : FacesH s × Duo s=> (x.1.2,x.2.2)) ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
 have t(k:ℕ) : Measurable (fun x:FacesH s × Duo s=> F.tarH W x.1 x.2 k):= by
   refine adj_cont.measurable.comp (f:=fun x:FacesH s× Duo s=> ((F.deck W x.1 x.2 k)⁻¹,F.built W x.1 x.2 k)) ((F.deck_meas W k).inv.prodMk ?_); apply measurable_pi_lambda; intro i; refine (chord.blend_meas T.toChart (W.progress k)).comp (f:=fun x:FacesH s×Duo s => (adjust (F.fill x.1 x.2).1 x.1.1 i,adjust (F.fill x.1 x.2).2 x.1.2 i)) (Measurable.prodMk ?_ ?_); exact (measurable_pi_apply i).comp (adj_cont.measurable.comp (f:=fun x:FacesH s×Duo s=> ((F.fill x.1 x.2).1,x.1.1)) ((measurable_fst.comp b).prodMk (measurable_fst.comp measurable_fst))); exact (measurable_pi_apply i).comp (adj_cont.measurable.comp (f:=fun x:FacesH s×Duo s=> ((F.fill x.1 x.2).2,x.1.2)) ((measurable_snd.comp b).prodMk (measurable_snd.comp measurable_fst))) -- tune
 apply measurable_pi_lambda; rintro ⟨x,i⟩; dsimp only [template]; let l:=(x 0-W.o).val; have h: Measurable fun x:FacesH s × Duo s=> F.tarV W x.1 x.2 l:= (F.deck_meas W l).inv.mul (F.deck_meas W _); refine Fin.cases ?_ ?_ i; exact (measurable_pi_apply (Fin.tail x)).comp h; intro j; exact (measurable_pi_apply (Fin.tail x,j)).comp (t _)

-- universal frame for the template (axial input assumed)
def atlasG := W.book (F.deck W x p)
lemma universe_H {k:ℕ} (v:k≤W.n.val) : horizontal (W.rise k) (gauge (F.atlasG W x p) (F.template W x p))=F.built W x p k:=by rw [adj_gauge,atlasG,W.booked _ v, F.readH W x p v,tarH,adjust_seq,mul_inv_cancel,adjust_one]
lemma universe_V {k:ℕ} (v:k<W.n.val) : normal (W.rise k) (gauge (F.atlasG W x p) (F.template W x p))=1:=by funext i; rw [vl_gauge,atlasG,←rise_succ, W.booked _ v.le, W.booked _ v, F.readV W x p v, tarV]; change _ = 1; simp

-- gauge behavior from raw data
lemma fill_a (a:Mach s): F.fill (W.reads (gauge a U)) (p*(W.framesE a)⁻¹)=F.fill (W.reads U) p * (W.framesE a)⁻¹:= by rw [W.reads_a]; exact Prod.ext (F.frame_left ..) (F.frame_left ..)
lemma deck_a (a:Mach s)(k:ℕ) : F.deck W (W.reads (gauge a U)) (p*(W.framesE a)⁻¹) k= F.deck W (W.reads U) p k * (W.branch a k)⁻¹:=by rw [deck,F.fill_a]; unfold branch deck access; split <;> rfl
lemma built_a (a:Mach s)(k:ℕ) : F.built W (W.reads (gauge a U)) (p*(W.framesE a)⁻¹) k= F.built W (W.reads U) p k:=by unfold built; rw [F.fill_a,W.reads_a]; simp only [Prod.fst_mul,Prod.snd_mul,Prod.fst_inv,Prod.snd_inv,adjust_seq, inv_mul_cancel_right] -- tune
lemma tarH_a (a: Mach s)(k:ℕ) : F.tarH W (W.reads (gauge a U)) (p*(W.framesE a)⁻¹) k=adjust (W.branch a k) (F.tarH W (W.reads U) p k):=by rw [tarH,F.deck_a,F.built_a,tarH,mul_inv_rev,inv_inv,adjust_seq]
lemma tarV_a (a: Mach s)(k:ℕ) : F.tarV W (W.reads (gauge a U)) (p*(W.framesE a)⁻¹) k=W.branch a k* F.tarV W (W.reads U) p k * (W.branch a (k+1))⁻¹:=by rw [tarV,F.deck_a,F.deck_a,tarV]; group
lemma template_a (a: Mach s): Set.EqOn (F.template W (W.reads (gauge a U)) (p*(W.framesE a)⁻¹)) (gauge (W.branchM a) (F.template W (W.reads U) p)) (inside W.mem):=by
 intro i h; let f := F.template W (W.reads (gauge a U)) (p*(W.framesE a)⁻¹); let q := F.template W (W.reads U) p; let t:= W.branchM a; change f i=_
 have he : i∈inside W.mem:=h; rcases link_cases i with ⟨x,j⟩|j; rw [j] at he; obtain ⟨k,h,e⟩:=W.tang_in x|>.mp he; rw [j,e]; change horizontal (W.rise k) f x= horizontal _ (gauge t q) x; unfold t f q; rw [F.readH _ _ _ h,adj_gauge, F.readH _ _ _ h,branchM,W.booked _ h, F.tarH_a]
 rw [j] at he; obtain ⟨k,h,e⟩:= W.normal_in _|>.mp he; rw [j,e]; change normal (W.rise k) f (Fin.tail i.1)= normal _ (gauge t q) _; unfold t f q; rw [vl_gauge,←rise_succ, F.readV _ _ _ h,F.readV _ _ _ h, branchM,W.booked _ h,W.booked _ h.le,F.tarV_a]; rfl -- tune
end Net
end YM.CF.BPress
