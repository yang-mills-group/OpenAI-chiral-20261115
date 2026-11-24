import YM.CF.Cubes.Inside

/-! Cells around a macro site: intersection form. Only for tori with reserved margins. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Lattice CF.Cube Lat
variable {m B:Side}
lemma wide (m B:Side)(ht:2≤m.val):8*B.val≤(Domain m B).val:=by
  rw [(scaleR m B).exact_size]; apply Nat.mul_le_mul_right; unfold GridN; rw [natM,natM]; omega
lemma up_inj {a b:Per (GridN m)}(h:high m B a= high m B b):a=b:=by
  have he:=d_high (B:=B) a b; rw [h,d_id] at he; exact d_equal _ _ ((Nat.mul_eq_zero.mp he.symm).resolve_left B.property.ne')
def offs (a:Index m)(x:Site (Domain m B)): Cover:=lift (x-address m B a)
lemma off_cap {a x}(h:x∈room m B a)(i:Axis): ((offs a x) i).natAbs ≤ broadface m B (a i):=by
  have he: (address m B a) i=high m B (a i):= high_here ..; exact (room_mem ..).mp h i
lemma off_back (a:Index m)(x: Site (Domain m B)):x=address m B a+wrap _ (offs a x) :=by rw [offs,wrap_lift]; abel
lemma off_odd (a:Index m)(x:Site (Domain m B))(i:Axis): x i=high m B (a i)+ (((offs a x) i:ℤ):Per (Domain m B)):=by
  have he:=(congr_fun (off_back a x) i); exact he
lemma off_done {a x} (h: ∀ i, ((offs a x) i).natAbs≤ broadface m B (a i)): x∈room m B a:= (room_mem ..).mpr (fun i=>h i)
lemma lift_s {t:Cover}(h:∀ i, (t i).natAbs≤ 2*B.val)(hm:2≤m.val) : lift (wrap (Domain m B) t)=t:=by
  funext i; apply (ZMod.valMinAbs_spec ..).mpr; refine ⟨?_,?_⟩
  · rfl
  rw [Set.mem_Ioc]; have hp:=wide m B hm; have hy:0<B.val:=B.property; have hv:=h i; omega
lemma off_lift {a x y} (h:x∈room m B a)(g:y∈room m B a)(hm:2≤m.val) : lift (x-y)=offs a x-offs a y := by
  have he : x-y=wrap _ (offs a x-offs a y):=by rw [map_sub]; unfold offs; rw [wrap_lift,wrap_lift]; abel
  rw [he]; exact lift_s (fun i=> by rw [Pi.sub_apply]; have hq:=(off_cap h i).trans (broad_le ..); have ht:=(off_cap g i).trans (broad_le ..); omega) hm
lemma visit_patch {x y : Site (Domain m B)} {a:Index m} (hx:x∈room m B a)(hy:y∈room m B a)(hm:2≤m.val)(z)(h:z∈visits x (march x y 1)): z∈room m B a := by
  obtain ⟨v,hv,e⟩:= march_visit x y 1 z h
  have he : z=address m B a+wrap _ (offs a x+v):=by rw [map_add,←add_assoc,←off_back]; exact hv
  have hk (i:Axis) : ((offs a x+v) i).natAbs≤ broadface m B (a i):=by
    have hA:= off_lift hy hx hm; have ha:=e.left i; have ht:=e.right i; rw [hA,Pi.sub_apply] at ha ht; simp only [Pi.add_apply]; have hs:=off_cap hx i; have hS:=off_cap hy i; simp only [Pi.zero_apply] at *; omega
  apply off_done; rw [he,offs,add_sub_cancel_left,lift_s (fun i=> ((hk i).trans (broad_le ..)).trans (by omega)) hm]; exact hk

def Rim (a:Index m)(x:Site (Domain m B)):=∃ b, Fits m b a∧ b≠a∧ x∈room m B b
def FitsX (p q:Per (GridN m)):= p=q ∨ ¬OddAxis m p∧OddAxis m q∧delta1 _ q p≤1
lemma corner_one {p q:Per (GridN m)}{x}(h: FitsX p q)(g:p≠q)(hx:roomX m B p x): OddAxis m q∧delta1 _ x (high m B q)=B.val :=by
  obtain ⟨a,b,c⟩:= Or.resolve_left h g
  have he:delta1 (GridN m) q p ≠ 0:=fun X=>g (d_equal _ _ X).symm
  rw [(room_e m B p x a).mp hx,d_sym (high m B q), d_high, show delta1 (GridN m) q p=1 by omega,mul_one]; exact ⟨b,rfl⟩
lemma corner_back (q:Per (GridN m)) (h: OddAxis m q)(x:Per (Domain m B))(hx:delta1 (Domain m B) x (high m B q)=B.val): ∃ p:Per (GridN m),FitsX p q ∧ p≠q ∧ roomX m B p x:=by
  let z:ℤ:= ZMod.valMinAbs (x-high m B q); have he:z.natAbs=B.val:=hx
  have hg:x=high m B q+(z:Per (Domain m B)):=by unfold z; rw [ZMod.coe_valMinAbs]; abel
  have hi (p)(hp:¬OddAxis m p)(t:x=high m B p): FitsX p q∧p≠q∧roomX m B p x:=by
    refine ⟨Or.inr ⟨hp,h,?_⟩,fun v=> hp (v.symm ▸ h),(room_e m B p x hp).mpr t⟩
    rw [t,d_sym _ (_ : Per (Domain m B)), d_high] at hx
    apply le_of_eq; apply Nat.eq_of_mul_eq_mul_left B.property; simp only [mul_one]; exact hx
  rcases (show z=(B.val:ℤ) ∨ z= -(B.val:ℤ) by omega) with t|t
  · exact ⟨q+1, hi (q+1) (fun g=>(oddAtAdd _|>.mp g) h) (by rw [hg,t,high_inc]; push_cast; rfl)⟩
  exact ⟨q-1,hi (q-1) (fun g=>(oddAtSub _|>.mp g) h) (by rw [hg,t,high_dec]; push_cast; abel)⟩
lemma rim_eq {a x} (hx:x∈room m B a): Rim a x ↔ ∃ i∈os m a, ((offs a x) i).natAbs=B.val:=by
  constructor
  · rintro ⟨b,h,q,g⟩; obtain ⟨i,t⟩:= Function.ne_iff.mp q
    have he:= corner_one (h i) t ((room_mem ..).mp g i); exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.1⟩,he.2⟩
  rintro ⟨i,hi,e⟩; obtain ⟨p,hp,hk,h⟩:= corner_back (B:=B) (a i) (Finset.mem_filter.mp hi|>.2) (x i) e
  refine ⟨Function.update a i p,(fun k=>?_), (fun t=>hk ?_), (room_mem ..).mpr (fun k=>?_)⟩
  · change FitsX _ _; by_cases t:k=i; rw [t,update_self]; exact hp
    exact Or.inl (update_of_ne t ..)
  · simpa using congr_fun t i
  by_cases t:k=i; rw [t,update_self]; exact h
  rw [update_of_ne t]; exact (room_mem ..).mp hx k

private lemma same_face {a b:Per (GridN m)}(h:a≠b)(ga:OddAxis m a)(gb:OddAxis m b){x} (va:roomX m B a x)(vb:roomX m B b x) : delta1 _ x (high m B a)= B.val :=by
  have ht:= d_one_triangle (high m B a) x (high m B b); rw [d_high,d_sym x] at ht
  unfold roomX at *; rw [broadface,if_pos ga] at va;rw [broadface,if_pos gb] at vb
  have he:= Nat.mul_le_mul_left B.val (d_even_sep (iff_of_true ga gb) h); omega
private lemma seam_fit {a b: Per (GridN m)} (e:a≠b) (g:¬OddAxis m a) {x}(h:roomX m B a x)(t:roomX m B b x) : FitsX a b:=by
  have he : x=high m B a:=(room_e _ _ _ _ g).mp h
  have hb : OddAxis m b:=Classical.byContradiction fun l=>e (up_inj (he.symm.trans ((room_e _ _ _ _ l).mp t)))
  refine Or.inr ⟨g,hb,?_⟩
  unfold roomX at t; rw [he,d_sym (high m B b),d_high,broadface,if_pos hb] at t
  by_contra! H; have hk:=Nat.mul_le_mul_left B.val (show 2≤delta1 (GridN m) b a from H); have ho:0<B.val:=B.property; omega
private lemma fits_unique {x y:Per (GridN m)}(h:OddAxis m x) (v:¬OddAxis m y) (he:FitsX y x): y=x+1 ∨ y=x-1 :=by
  have hh : y ≠ x:= fun t=>v (t.symm ▸ h); obtain ⟨_,_,hv⟩:= Or.resolve_left he hh
  rw [d_sym] at hv; apply d_unit; exact le_antisymm hv (Nat.pos_of_ne_zero fun g=>hh (d_equal _ _ g))
private lemma gird {i:Per (GridN m)}(hm:2≤m.val): (i+1)+2 ≠ i-1:=by
  intro h; have he : (4:Per (GridN m))=0:=by linear_combination h
  have hp := (ZMod.natCast_eq_zero_iff 4 (GridN m).val).mp (by norm_num; exact he) -- tune
  have hx:=Nat.le_of_dvd (by norm_num) hp; unfold GridN at hx; rw [natM,natM] at hx; omega
private lemma concurX {a b:Per (GridN m)} (hm:2≤m.val)(h:a≠b)(ga:OddAxis m a)(gb:OddAxis m b){p q}(t:¬OddAxis m p)(u:¬OddAxis m q)
    (l:FitsX p a)(k:FitsX p b)(j:FitsX q a)(m':FitsX q b):p=q:=by
  have H:=gird (i:=a) hm
  rcases fits_unique ga t l with s|s <;> rcases fits_unique gb t k with u|u <;>
    rcases fits_unique ga (show ¬OddAxis m q from by assumption) j with v|v <;>
    rcases fits_unique gb (show ¬OddAxis m q from by assumption) m' with z|z <;>
    first
    | solve | rw [s,v]
    | solve | rw [u,z]
    | exact False.elim (h (by first | linear_combination s - u | linear_combination u - s | linear_combination z-v | linear_combination v-z))
    | exact False.elim (H (by first | linear_combination s-u+z-v | linear_combination v-z+u-s | linear_combination u+v-s-z | linear_combination z+s-v-u))
private lemma overlapX {a b:Per (GridN m)} (hm:2≤m.val){x}(h:roomX m B a x)(k:roomX m B b x): ∃ c:Per (GridN m),FitsX c a∧FitsX c b ∧∀ y,roomX m B a y→ roomX m B b y→ roomX m B c y:=by
  by_cases he:a=b
  · exact ⟨a,Or.inl rfl,Or.inl he,fun _ hu _=>hu⟩
  by_cases hp:OddAxis m a
  swap
  · exact ⟨a,Or.inl rfl,seam_fit he hp h k,fun _ hu _=>hu⟩
  by_cases hq:OddAxis m b
  swap
  · exact ⟨b,seam_fit (Ne.symm he) hq k h,Or.inl rfl,fun _ _ hu=>hu⟩
  have H(z)(v:roomX m B a z)(f:roomX m B b z) : ∃ c,¬ OddAxis m c∧ FitsX c a∧ FitsX c b∧roomX m B c z:=by
    obtain ⟨c,i,t,s⟩:=corner_back a hp z (same_face he hp hq v f); have hu : ¬OddAxis m c:=(Or.resolve_left i t).1
    exact ⟨c,hu,i,seam_fit (fun y=>hu (y.symm ▸ hq)) hu s f,s⟩
  obtain ⟨c,u,s,t,-⟩:=H x h k
  refine ⟨c,s,t,fun y r v=>?_⟩; obtain ⟨b,e,l,d,q⟩:=H y r v
  rwa [concurX hm he hp hq u e s t l d]
lemma overlap {a b x} (hm:2≤m.val)(h:x∈room m B a)(g:x∈room m B b):∃ c:Index m, Fits m c a∧ Fits m c b∧ ∀ y, y∈room m B a→ y∈room m B b→ y∈room m B c:=by
  choose c r l k using fun i=>overlapX hm ((room_mem ..).mp h i) ((room_mem ..).mp g i)
  exact ⟨c,r,l,fun y s t=>(room_mem ..).mpr fun i=> k _ _ ((room_mem ..).mp s i) ((room_mem ..).mp t i)⟩
end YM.CF.Mesa
