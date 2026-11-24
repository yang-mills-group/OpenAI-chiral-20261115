import YM.SU5.Relativistic.TriFlux
import YM.Lattice.Subdivision
/-! # tiled pressure proof. Positive positions. Mark plans. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count
theorem wing {N:Side}(x:Per N)(h:x.val+1=N.val) : x= - (1:Per N):=by
 apply ZMod.val_injective
 suffices h':ZMod.val (- (1:Per N))+1=N.val by omega
 obtain ⟨_|k,h⟩:=N; · simp at h
 change (- (1:ZMod (k+1))).val+1=k+1; rw [ZMod.val_neg_one]
lemma next_s {N:Side}(x:Site N)(i:Axis) (h:(x i).val+1<N.val) : (((x+step i) : Site N) i).val=(x i).val+1:=by simp only [Pi.add_apply,step_apply,ite_true]; rw [ZMod.val_add,ZMod.val_one_eq_one_mod,Nat.add_mod_mod,Nat.mod_eq_of_lt h]
lemma previous_s {N:Side}(x:Site N)(i:Axis)(h:x i≠0): (((x-step i) : Site N) i).val+1=(x i).val:=by
 let y:= x-step i; have hx: y+step i=x:=sub_add_cancel ..; have ht:(y i).val<N.val:= ZMod.val_lt _; by_cases e:(y i).val+1=N.val; · have hi:y i= - (1:Per N):= wing _ e; apply (h _).elim; apply Eq.trans (congrFun hx.symm i); simp [hi]
 exact (hx ▸ next_s y i (by omega)).symm -- beware y

def topUp (x:Site N) : Cover:= fun i=> (x i).val
lemma wrapsU(x:Site N) : wrap N (topUp x)=x:=by funext i; change (((((x i).val) : ℤ)) : Per N)=_; simp

def setDown (i:T_)(x:P_):F_:= L.embed i+wrap N (topUp x)
lemma evenShift (i:T_)(x:P_)(j:Axis)(v:(x j).val+1<L.count.val) : setDown L i (x+step j)= setDown L i x+step j:=by
 have h:topUp (x+step j)=topUp x+step j:= by
    funext k; obtain rfl|e:=eq_or_ne k j; · change ((((x+step k : P_) k).val) : ℤ)= (topUp x k)+step k k; rw [next_s x k v]; simp [topUp]
    simp [topUp,e]
 unfold setDown; rw [h,map_add]; simp [add_assoc]
lemma oddShift (i:T_)(x:P_)(j:Axis)(v:(x j).val+1=L.count.val):setDown L (i+step j) (x+step j)= setDown L i x+step j:=by
 have h:L.count.val • step j + topUp (x+step j) = topUp x+step j:= by
    funext k; obtain rfl|e:=eq_or_ne k j
    · have hp:((x+step k:P_) k).val=0:=by simp [wing _ v]
      change L.count.val • (step k : Cover) k+((((x+step k:P_) k).val):ℤ)= (((x k).val):ℤ)+(step k:Cover) k; rw [hp,nsmul_eq_mul,(show (L.count.val:ℤ)= ((x k).val:ℤ)+1 from (by exact_mod_cast v.symm))]; simp
    simp [topUp,e]
 have hp:L.embed (i+step j)= L.embed i+wrap N (L.count.val • step j):=by rw [←L.root_embed,L.root.map_add]; simp only [Ratio.root_embed]; rw [show (step j : T_)=wrap C (step j) from by simp]; rw [L.embed_wrap] -- tune
 unfold setDown; rw [hp,add_assoc, ← map_add,h,map_add]; simp [add_assoc]
lemma set_inj: Injective (fun p:T_×P_ => setDown L p.1 p.2):=by
 rintro ⟨i,x⟩ ⟨j,y⟩ h; change L.embed i+ _=L.embed j+ _ at h; have hx:x=y:=by
    have he:=congrArg L.residue h; change L.residue (setDown L i x)=L.residue (setDown L j y) at he; simpa only [setDown,map_add,Ratio.residue_embed,Ratio.residue_wrap,zero_add,wrapsU] using he
 subst y; rw [L.embed_injective (add_right_cancel h)]
lemma sets_onto : Surjective (fun p:T_×P_ => setDown L p.1 p.2):=((Fintype.bijective_iff_injective_and_card _).mpr ⟨set_inj L,by rw [Fintype.card_prod,site_card,site_card,site_card,L.exact_size,mul_pow]⟩).2
def slot : T_ × P_ ≃ F_:= Equiv.ofBijective _ ⟨set_inj L,sets_onto L⟩
def raise (i:T_)(a:Link W_) : Link N := (setDown L i a.1,a.2)
def lifted : T_ × Link W_ ↪ Link N where
 toFun p:= raise L p.1 p.2
 inj' := by rintro ⟨i,x⟩ ⟨j,y⟩ e; change raise L i x= raise L j y at e; have hx:(i,x.1)=(j,y.1):=set_inj L (congrArg Prod.fst e); exact Prod.ext (congrArg (fun a:T_ × Site L.count=>a.1) hx) (Prod.ext (congrArg (fun a:T_ × Site L.count=>a.2) hx) (show x.2=y.2 from congrArg (fun a:Link N=>a.2) e))
def vowel : Link N ≃ T_ × Link W_:= (Equiv.prodCongr (slot L).symm (Equiv.refl _)).trans (Equiv.prodAssoc ..)
@[simp] lemma vowel_p(i:T_)(x:Link W_): vowel L (raise L i x)=(i,x):= show vowel L ((vowel L).symm (i,x))=_ from Equiv.apply_symm_apply ..
def indoors {Y:Side} (x:Link Y): Prop := (x.1 x.2).val+1<Y.val
instance {Y:Side}(v:Link Y): Decidable (indoors v):= by unfold indoors; infer_instance
def livelies (V:Side):= (pivots V).filter indoors
lemma indoors_m {Y:Side}(x:Link Y)(h:indoors x): Fixed.Pivots.Active x↔ ¬ Fixed.Pivots.Tree x:= ⟨fun t=>t.1,fun t=>⟨t,fun g=>(show (x.1 x.2).val+1<Y.val from h).ne g.1⟩⟩
lemma live_mark {W:Side}{i:Link W}(p:indoors i)(q:Fixed.Pivots.Active i): tooth i q < i.2:=by
 by_contra w
 apply q.1; refine ⟨p,fun j g=>?_⟩
 by_contra h; exact (g.trans_le (le_of_not_gt w)).not_ge ((tooth_spec i q).2.2 j g.ne h)
-- show two other toll are tree, all toll indoors
lemma live_pins {Y:Side}(x:Site Y)(i:Axis)(p:indoors (x,i))(q:Active (x,i)): let k:=tooth (x,i) q; let y:= x-step k; Tree (y,k) ∧ Tree (y+step i,k)∧indoors (y,i):=by
 intro k y; let z:=y+step i
 have ht:k < i:=live_mark p q; have hh:= tooth_spec (x,i) q
 have hn:y i=x i:=by simp [y,ht.ne']
 have hu:z k=y k:=by simp [z,ht.ne]
 have hx:(y k).val+1< Y.val:= (previous_s x k hh.2.1).trans_lt (ZMod.val_lt _)
 have hf(j:Axis)(v:j<k) : y j=0:=by
    have he:x j=0:=by by_contra w; exact v.not_ge (hh.2.2 j (v.trans ht).ne w)
    simp [y,he,v.ne]
 refine ⟨⟨hx,hf⟩,⟨(show (z k).val+1<Y.val from hu.symm ▸ hx),fun j v=>?_⟩,(hn.symm ▸ (show (x i).val+1<Y.val from p) : (y i).val+1<Y.val)⟩
 change j<k at v; change z j=0; simp [z,hf j v,(v.trans ht).ne]
lemma win_shuffle{V : Side}(x:Site V)(i j:Axis)(h:i≠j) : support (x,PlaqAxes.ordered i j h) = window x i j:=by
 unfold Fixed.Pivots.support PlaqAxes.ordered; change window x (min i j) (max i j)=_; rcases le_total i j with l|l
 · rw [min_eq_left l,max_eq_right l]
 rw [min_eq_right l,max_eq_left l]; ext a; simp only [window,mem_insert,mem_singleton]; tauto
lemma window_p {x:T_} {y:P_}{i j:Axis}(h:indoors (y,i))(v:indoors (y,j)) : window (setDown L x y) i j= (window y i j).image (raise L x):=by simp [window,raise,evenShift L x y i h,evenShift L x y j v]
def loom(x:T_)(e:Link W_)(h:Active e):Face (Per N):= let t:=mark e h; (setDown L x t.1,t.2)
lemma at_loom (x:T_)(i:Link W_)(p:indoors i)(q:Active i): support (loom L x i q)=(support (mark i q)).image (raise L x):=by
 rcases i with ⟨a,b⟩; unfold loom mark; dsimp only; rw [win_shuffle,win_shuffle]; obtain ⟨r,s,t⟩:=live_pins a b p q; exact window_p L t r.1
lemma pin_space {Y:Side}(i:Link Y)(p:indoors i)(q:Active i)(x:Link Y)(e:x∈support (mark i q)): indoors x:=by
 rcases i with ⟨i,j⟩; obtain ⟨s,t,u⟩:=live_pins i j p q; rw [mark_window i j q] at e; simp only [window,sub_add_cancel,mem_insert,mem_singleton] at e; rcases e with rfl|rfl|rfl|rfl; exact u; exact t.1; exact p; exact s.1
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.at_loom
