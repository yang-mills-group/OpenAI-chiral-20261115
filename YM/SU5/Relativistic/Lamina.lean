import YM.SU5.Relativistic.Griddle
import YM.SU5.Relativistic.Windsail
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
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
open RG RG.PathData Work.F03 Pharos
def zipFace(i:T_)(p:Face (Per W_)):Face (Per N):=(setDown L i p.1,p.2)
def chip (x:T_):Face (Per W_) ↪ Face (Per N) where
 toFun:= zipFace L x
 inj' := by intro p q h; exact Prod.ext (congrArg (fun a:T_×P_=>a.2) (set_inj L (a₁:=(x,p.1)) (a₂:=(x,q.1)) (congrArg Prod.fst h))) (congrArg (fun a:Face (Per N)=>a.2) h) -- tune names
lemma room_diff(i j:T_)(e:i≠j) (p q :Face (Per W_)): zipFace L i p≠zipFace L j q:=by intro t; apply e; exact congrArg (fun a:T_×P_=>a.1) (set_inj L (a₁:=(i,p.1)) (a₂:=(j,q.1)) (congrArg Prod.fst t))
variable {V : Side}
abbrev here (x : Face (Per V)):Prop:= indoors (Y:=V) (x.1,x.2.val.1) ∧ indoors (Y:=V) (x.1,x.2.val.2) -- binder indoors Y
lemma here_lift (x:T_)(i:Face (Per W_))(v:here i): support (zipFace L x i)= (support i).image (raise L x):= window_p L v.1 v.2
lemma here_in (i:Face (Per V))(v:here i)(x:Link V)(hx:x∈ support i): indoors x:=by
 obtain ⟨j,⟨⟨a,b⟩,e⟩⟩:=i; simp only [Fixed.Pivots.support, window,mem_insert,mem_singleton] at hx; rcases hx with rfl|rfl|rfl|rfl
 · exact v.1
 · change (((j+step a : Site V) b) : Per V).val+1<V.val; simpa [e.ne'] using (show (j b).val+1<V.val from v.2) -- tune Ne simp goal
 · change ((((j+step b : Site V) a)).val)+1<V.val; simpa [e.ne] using (show (j a).val+1<V.val from v.1)
 exact v.2
def ort (V: Side):= (univ:Finset (Face (Per V))).filter here
def mounted (i:T_):= (ort W_).map (chip L i)
lemma mark_ort (x:Link V)(p:indoors x)(q:Active x) : mark x q ∈ ort V :=mem_filter.mpr ⟨mem_univ _,pin_space x p q _ (show _ ∈ Fixed.Pivots.support (mark x q) by simp [Fixed.Pivots.support,window]),pin_space x p q _ (show _ ∈ Fixed.Pivots.support (mark x q) by simp [Fixed.Pivots.support,window])⟩
lemma ort_vb {X : Type}[Group X](U:Links (Per N) X)(Z:Links (Per W_) X)(i:T_)(k:∀ a:Link W_,indoors a→U (raise L i a)=Z a)(p:Face (Per W_))(h:here p) : travel U (setDown L i p.1) (square p.2.val.1 p.2.val.2)= travel Z p.1 (square p.2.val.1 p.2.val.2):=by
 -- use universal. local duplicate
 obtain ⟨j,⟨⟨a,b⟩,e⟩⟩:=p
 let x:= setDown L i j
 have hv{Y:Side}(j:Site Y)(U: Links (Per Y) X):travel U j (square a b)= U (j,a)*U (j+step a,b)*(U (j+step b,a))⁻¹*(U (j,b))⁻¹:= by
   simp only [travel,square,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one,mul_assoc]; rw [show j+step a+step b-step a=j+step b by abel,show j+step a+step b+ -step a-step b=j by abel]
 change travel U x (square a b)= travel Z j (square a b)
 have he(p:Link W_)(w:p∈ window j a b):U (raise L i p)= Z p:= k p (here_in _ h p w)
 rw [hv,hv,←he (j,a) (by simp [window]), ← he (j+step a,b) (by simp [window]), ← he (j+step b,a) (by simp [window]), ← he (j,b) (by simp [window])]; unfold x raise; dsimp only; rw [evenShift L i j a h.1,evenShift L i j b h.2] -- tune rewrite metavars
lemma ort_s {G:Gauge}(U:Config G N)(Z:Config G W_)(i:T_)(k:∀ a:Link W_,indoors a→U (raise L i a)=Z a)(p:Face (Per W_))(e:p ∈ ort W_) : faceValue U (zipFace L i p)=faceValue Z p:= ort_vb L U Z i k p ((mem_filter.mp ‹_›).2)

-- cores
def deep (D:ℕ)(p:Site V):Prop:= ∀ i:Axis, D≤ (p i).val∧ (p i).val+D<V.val
instance(d:ℕ)(p:Site V): Decidable (deep d p):=by unfold deep; infer_instance
def plumb (V : Side)(D:ℕ):= (univ:Finset (Face (Per V))).filter fun p=> deep D p.1
def plumage (D:ℕ)(i:T_):= (plumb W_ D).map (chip L i)
lemma fade_d (D d:ℕ)(p:d≤ D)(x:Site V)(v:deep D x):deep d x:= by intro i; have h:=v i; omega
lemma subdeep (x:Site V)(i:Axis)(d:ℕ)(v:deep (d+1) x): deep d (x+step i)∧ indoors (x,i) ∧ deep d (x-step i) ∧ indoors (x-step i,i):=by
 have hh:= v i; have he:x i≠0:=by intro w; have hz: (x i).val=0:=w ▸ ZMod.val_zero; omega -- semicolon capture
 have ht:(x i).val+1<V.val:=by omega
 have hx:= next_s x i ht; have hr:= previous_s x i he
 refine ⟨fun j=>?_,ht,fun j=>?_,(show _ from hr.trans_lt (ZMod.val_lt _))⟩
 · obtain rfl|g:=eq_or_ne j i; · omega
   simpa [g] using fade_d _ _ (Nat.le_succ d) x v j
 obtain rfl|g:= eq_or_ne j i; · omega
 simpa [g] using fade_d _ _ (Nat.le_succ d) x v j
lemma stepping (d:ℕ)(x:P_)(i:T_)(s:Step)(h:deep (d+1) x) : deep d (x+s.vec) ∧ indoors (s.used x) ∧ setDown L i (x+s.vec)=setDown L i x+s.vec∧ raise L i (s.used x)= s.used (setDown L i x):=by
 cases s with
 | mk a u=>
   obtain ⟨p,t,w,e⟩:= subdeep x a d h; cases u
   · exact ⟨p,t,evenShift L i x a t,rfl⟩
   have hv:setDown L i (x-step a)= setDown L i x-step a:=by rw [eq_sub_iff_add_eq,← evenShift L i (x-step a) a e,sub_add_cancel]
   simp only [Step.vec,Step.used, ↓reduceIte]; rw [←sub_eq_add_neg]; exact ⟨w,e,hv.trans (sub_eq_add_neg ..), Prod.ext hv rfl⟩ -- tune
lemma rolling(d:ℕ)(v:Walk)(x:P_)(i:T_)(p:deep (v.length+d) x): deep d (stop x v) ∧ stop (setDown L i x) v= setDown L i (stop x v):=by
 induction v generalizing x with
 | nil=> simp only [stop,List.length_nil,zero_add] at *; exact ⟨p,trivial⟩
 | cons a t ih=> obtain ⟨u,g,l,r⟩:=stepping L (t.length+d) x i a (by simpa only [List.length_cons,Nat.add_right_comm _ 1 _] using p); obtain ⟨v,w⟩:= ih (x+a.vec) u; simp only [stop]; rw [← l]; exact ⟨v,w⟩ -- test add comm simp
lemma worked {X:Type}[Group X] (U:Links (Per N) X)(Z:Links (Per W_) X)(i:T_)(k:∀ a:Link W_,indoors a → U (raise L i a)= Z a)(v:Walk)(x:P_)(p:deep v.length x): travel U (setDown L i x) v=travel Z x v:=by
 induction v generalizing x with
 | nil => rfl
 | cons a t ih=>
    obtain ⟨u,g,l,r⟩:=stepping L t.length x i a p; simp only [travel]; rw [← l,ih _ u]; unfold Step.read; rw [← r,k _ g]
lemma offset_f (v:Slot)(x:Site V): (slotFace v x).1=stop x v.walk:=by
 have he (p:Walk)(y z:Site V) : stop (y+z) p= stop y p+z:=by induction p generalizing y with|nil=>rfl|cons a t ih=>simp only [stop]; rw [add_right_comm y z,ih]
 have hx (p:Walk)(y:Cover) : wrap V (stop y p)= stop (wrap V y) p:=by induction p generalizing y with|nil=>rfl|cons a t ih=> simp only [stop,ih,map_add,wrap_vec]
 change wrap V (stop _ _)+_= _; rw [hx,map_zero,←he,zero_add]
lemma stitched (D:ℕ)(i:T_)(p:P_)(v:Slot)(h:v.length≤ D)(q:deep D p) : slotFace v (setDown L i p)= zipFace L i (slotFace v p)∧slotFace v p∈ort W_:=by
 obtain ⟨g,y⟩:= rolling L 4 v.walk p i (fade_d _ _ h p q)
 have hc: (slotFace v p).1= _:= offset_f v p; refine ⟨Prod.ext ?_ rfl,?_⟩; · change _= setDown _ _ (slotFace _ p).1; rw [offset_f ..,hc,y]
 apply mem_filter.mpr; refine ⟨mem_univ _,?_,?_⟩
 · rw [hc]; exact (subdeep _ _ 3 g).2.1
 rw [hc]; exact (subdeep _ _ 3 g).2.1
lemma stitch_g {G:Gauge} (D:ℕ)(i:T_)(p:P_)(v:Slot)(h:v.length≤ D)(q:deep D p)(U:Config G N)(Z:Config G W_)(k:∀ a:Link W_, indoors a→ U (raise L i a)=Z a): v.atSite U (setDown L i p)=v.atSite Z p:=by
 rw [atSite_path,atSite_path]; obtain ⟨s,t⟩:= stitched L D i p v h q; rw [s,ort_s L U Z i k _ t,worked L U Z i k v.walk p (fade_d D _ (le_trans (by unfold Slot.length; omega) h) p q)]
lemma plum_s {G:Gauge}(U:Config G N)(Z:Config G W_)(W:PathData G)(R:ℕ)(i:T_)(x:Face (Per W_))(e:x∈ plumb W_ R)(k:∀ a:Link W_,indoors a → U (raise L i a)=Z a) : Pressure.shorten W R 1 U (zipFace L i x)= Pressure.shorten W R 1 Z x:=by
 apply tsum_congr; intro j; let D:= W.row x.2 j; change (if D.2.length*1≤R then D.1 • D.2.atSite U (setDown L i x.1) else 0)=(if D.2.length*1≤R then D.1 • D.2.atSite Z x.1 else 0); rw [mul_one]; split; next h=> rw [stitch_g L R i x.1 D.2 h ((mem_filter.mp e).2) _ _ k] -- tune syntax binder
 next=> rfl

lemma small_g {G:Gauge}{N:Side}(U V:Config G N)(p: Face (Per N))(R:ℕ)(x:deep R p.1)(k:∀ a:Link N,indoors a → U a=V a)(W:PathData G): Pressure.shorten W R 1 U p=Pressure.shorten W R 1 V p:=by
 -- self tile trick use worked but L carrier not same. alternatively simple
 apply tsum_congr; intro j; unfold Pressure.shortenTerm; rw [mul_one]; split; next h=>
    let i:= W.row p.2 j
    have hh:deep (i.2.walk.length+4) p.1:=fade_d _ _ h _ x
    have he(v:Walk)(u:Site N) : ∀ d:ℕ,deep (v.length+d) u→ travel U u v=travel V u v∧ deep d (stop u v):=by
      induction v generalizing u with
      | nil => intro d h; rw [List.length_nil,zero_add] at h; exact ⟨rfl,h⟩
      | cons a w ih=>
        intro d h; have hz:deep (w.length+d+1) u:=by rw [Nat.add_right_comm w.length d 1]; exact h
        obtain ⟨s,t,r,g⟩:= subdeep u a.dir (w.length+d) hz; have he: deep (w.length+d) (u+a.vec) ∧ indoors (a.used u):=by unfold Step.vec Step.used; split; rw [←sub_eq_add_neg]; exact ⟨r,g⟩; exact ⟨s,t⟩
        have hl:a.read U u=a.read V u:=by unfold Step.read; rw [k _ he.2];
        obtain ⟨x,y⟩:= ih _ _ he.1; refine ⟨?_,y⟩; simp only [travel,x,hl]
    let v:= i.2.walk; let z:=slotFace i.2 p.1; change i.1 • i.2.atSite U _=i.1 • i.2.atSite V _; obtain ⟨u,g⟩:=he v p.1 4 hh
    rw [atSite_path,atSite_path,u,show faceValue U (slotFace i.2 p.1)=faceValue V (slotFace i.2 p.1) from ?_]
    exact (he (square z.2.val.1 z.2.val.2) z.1 0 (show deep 4 z.1 from ((offset_f i.2 p.1).symm ▸ g))).1
 next=> rfl
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.plum_s
