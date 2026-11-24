import YM.CF.Vp929.Law.Broil
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Lattice CF.Cube Lat
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {m B:Side}
private lemma deltaV (u v:SU.E): GDist u v=lambda (u*v⁻¹)*(Real.sqrt (SU.group.repDim:ℝ)):=by
  unfold GDist lambda Gauge.chord; rw [div_mul_cancel₀,← bolt u v v⁻¹,dist_eq_norm,mul_inv_cancel]; rfl
  exact (Real.sqrt_pos.mpr (by exact_mod_cast SU.group.dimPos)).ne'
lemma reserveB (B:Side):∃ r:ℝ, 0<r∧∀ U:Links ℤ SU.E,(∀ x∈box B.val, ∀ i:PlaqAxes,lambda (faceValue U (x,i))≤r) →∃ h:Cover→SU.E,∀(x) (i), x∈box B.val→x+step i∈box B.val→ GDist (h x*U (x,i)) (h (x+step i)) ≤ 1/(B.val:ℝ):=by
  let X:=box B.val
  let l:=allAxes 1; have ht:l.Nodup:=(List.nodup_finRange _).map (show Lattice.Order from 1).injective
  have he : Lattice.slab B.val 0 l=X :=by
    ext i
    simp only [slab_iff]
    have ha (j:Axis) : j ∈ l:=by simp [l,allAxes]
    simp [ha,X]
  let t:ℝ:=(Finset.univ:Finset PlaqAxes).card; let N:ℝ:=4*(l.length:ℝ)*(layers B.val).card
  let w:ℝ:=Real.sqrt (SU.group.repDim:ℝ)
  have hn : 0≤N:=by unfold N; positivity
  have hT:0≤t:=by unfold t; positivity
  have hw:0≤ w:=by unfold w; positivity
  let J:ℝ:=N*X.card*t*w; have hJ:0≤J:=by unfold J; positivity
  let k:ℝ:= 1/(B.val:ℝ); let r:=k/(J+1); have hp:0<r:=by unfold r k; positivity
  refine ⟨r,hp,fun U g=>?_⟩
  have hm:= Axial.existence l B.val 0 U ht (center_box _); rw [he] at hm
  obtain ⟨i,-,hx⟩:= hm
  let H:=Axial.traveller l U i; let V:=gauge H U
  have hr: Axial.faces X U ≤ (X.card:ℝ)*(t*r) := by
    unfold Axial.faces
    refine (Finset.sum_le_sum (g:=fun _=>t*r) (fun i hi=>?_)).trans (le_of_eq (by simp))
    refine (Finset.sum_le_sum (g:=fun x:PlaqAxes=>r) (fun x _=>show Axial.face X U i x≤ r from ?_)).trans (le_of_eq (by simp [t]))
    unfold Axial.face; split; exact g i hi x; exact hp.le
  have hL: ∀ x i, 0≤ Axial.perEdge X V x i:=fun x j=> by unfold Axial.perEdge; split; exact SU.group.chord_nonneg _; rfl
  refine ⟨H,fun x j u h=>?_⟩
  have hA :lambda (V (x,j))≤ Axial.edges X V :=by
    rw [show lambda _=Axial.perEdge X V x j from (if_pos h).symm]
    exact le_trans (Finset.single_le_sum (f:=Axial.perEdge X V x) (fun i _=>hL x i) (Finset.mem_univ j)) (Finset.single_le_sum (fun i _=> Finset.sum_nonneg (fun k _=>hL i k)) u)
  have hb:r*(J+1)=k:=by unfold r; field_simp
  rw [deltaV]; apply (mul_le_mul_of_nonneg_right (hA.trans (hx.trans (mul_le_mul_of_nonneg_left hr hn))) hw).trans
  change N*_*w ≤ k
  unfold J at hb; nlinarith only [hb,hp]
end YM.CF.Mesa

namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms Mos Mesa Cube Lat WalkBound
open scoped Topology Classical Matrix.Norms.Frobenius NNReal
namespace Palace
variable {x:Pal}{C:Side}{K:ℝ→ℝ} {A:Realms}{B:ℕ}
lemma Ranged(x p:Cover)(R:ℕ): Range R x p ↔ p-x ∈ box R:=by
 simp only [box_test,Pi.sub_apply]; constructor; exact fun e=> ⟨fun i=>by have h:= e i; omega,fun i=>by have h:=e i; omega⟩; intro ⟨a,b⟩ i; have a:=a i; have b:= b i; omega
private lemma screw (t y:Cover)(i:PlaqAxes) : faceValue (translate t A) (y,i)=faceValue A (y+t,i):=by
 unfold faceValue; rw [←pull_one t A, travel_pull]; simp [affine,List.map_id]
private lemma cubing(B C:Side):∃ r:ℝ,0<r∧ ∀ (A:Realms)(p:Cover)(x:Rooms), here p≤ x → x.bounded (B.val*C.val) → (∀ y:Cover,Range (B.val*C.val) p y →∀ i:PlaqAxes,lambda (faceValue A (y,i)) ≤ r) → wellF x A C 1:=by
 obtain ⟨r,t,h⟩:=reserveB (B*C); refine ⟨r,t,fun A p x t q v=>?_⟩; let U:=translate p A; let Z:= box (B*C).val
 obtain ⟨w,H⟩:=h U (fun y s i=>by rw [show _=faceValue A (y+p,i) from screw p y i]; apply v ; rw [Ranged,add_sub_cancel_right]; exact s)
 refine ⟨fun i=>w (i-p),fun a i e=>?_⟩; obtain ⟨s,e⟩:= spanFits.mp e
 have hp:(a+step i-p)∈Z:= (Ranged ..).1 (within q t e)
 have hc:= H (a-p) i ((Ranged ..).1 (within q t s)) (by rw [show a-p+_=a+step i-p by abel]; exact hp)
 rw [show a-p+_=a+step i-p by abel, show U (_,i)=A (a,i) by unfold U translate; rw [sub_add_cancel]] at hc; refine hc.trans (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1) (by positivity) ?_); exact_mod_cast (Nat.le_mul_of_pos_left C.val B.property)
variable {R:ℝ} (t:Ready C B x)(P:Pal.Guards C 5 R x A A)

private theorem flat_wind (p:Cover) (i j:Axis)(h:i≠j) : Tiny (span p (p+step i+step j)) ∧ (∀ y:Rooms, span p (p+step i+step j) ≤ y → here (p+step i) ≤ y):=by
 constructor
 · apply spanT.mpr; intro k; by_cases e:k=i; subst k; simp [h]; by_cases v:k=j; subst k; simp [Ne.symm h]; simp [e,v]
 intro y hz k; obtain ⟨e,v⟩:= spanFits.mp hz; obtain ⟨l,t⟩:=Wall.seen (e k); obtain ⟨a,q⟩:=Wall.seen (v k); change ((y k).a ≤ (p+step i:Cover) k) ∧ _ ≤ (y k).b; change _ ∧ (p+step i:Cover) k ≤ _; simp only [Pi.add_apply,step_apply] at a q ⊢; split_ifs at * <;> omega

include t
lemma sailL(D:Realms)(v:Pal.Guards C 5 R x A D)(p:Cover)(i:PlaqAxes):lambda (faceValue D (p,i))≤ 4*(R/((C.val:ℝ)*Real.sqrt (SU.group.repDim:ℝ))):=by
 rcases i with ⟨⟨a,b⟩,h⟩; let X:PlaqAxes:=⟨(a,b),h⟩; let g:= span p (p+step a+step b); change a < b at h; change lambda (faceValue D (p,X))≤_
 let hg:= flat_wind p a b h.ne; obtain ⟨z,e,w⟩:=t.roof.stand _ hg.1; obtain ⟨T,pT,W⟩:= trunk01 t.roof e hg.1 w
 obtain ⟨N,E⟩:= v.2 T ⟨pT.2.symm ▸ pT.1,rfl⟩ (by have h:=pT.2; omega); let w':= gauge N D
 let k:=Real.sqrt (SU.group.repDim:ℝ); have hk:0<k:=Real.sqrt_pos.mpr (by exact_mod_cast SU.group.dimPos)
 have ha j (t:zone j ≤ T):lambda (w' j) ≤ R/(C.val*k):= by
    rcases j with ⟨A,B'⟩; have he:=E A B' t; rw [March.capDistance] at he; exact le_trans (le_of_le_of_eq ((le_div_iff₀ hk).mpr he) (show R/(C.val:ℝ)/k=R/(C.val*k) by field)) le_rfl
 have z: p+step b+step a=p+step a+step b:=by abel
 have Y:= spanFits.mp W; have X1:=hg.2 _ W; have X2:= (flat_wind p b a (Ne.symm h.ne)).2 _ (z.symm ▸ W)
 rw [show lambda (faceValue D (p,X))=lambda (faceValue w' (p,X)) by unfold w'; rw [face_gauge]; exact (SU.group.chord_conj ..).symm]; rw [show faceValue w' (p,X)= w' (p,a)*w' (p+step a,b)*(w' (p+step b,a))⁻¹*(w' (p,b))⁻¹ by unfold faceValue; simp only [X,square,travel,Step.neg_read,Step.pos_read,Step.vec_neg,Step.vec_pos,inv_one,mul_one]; rw [show p+step a+step b-Lattice.step a=p+step b by abel,show p+step a+step b+ -step a-Lattice.step b=p by abel]; group]; unfold lambda
 apply (SU.group.chord_triangle ..).trans; rw [SU.group.chord_inv]; refine (add_le_add (le_trans (SU.group.chord_triangle ..) (add_le_add (le_trans (SU.group.chord_triangle ..) (add_le_add (ha _ (spanFits.mpr ⟨Y.1,X1⟩)) (ha _ (spanFits.mpr ⟨X1,Y.2⟩)))) (show SU.group.chord _≤ R/(C.val*k) from ?_))) (ha _ (spanFits.mpr ⟨Y.1,X2⟩))).trans ?_
 · rw [SU.group.chord_inv]; exact ha _ (spanFits.mpr ⟨X2,z ▸ Y.2⟩)
 change _ ≤ 4*(R/(C.val*k)); linarith
omit t
structure Sweater (C B :Side)(K:ℕ→ℝ)(u d:ℝ): Prop where
 wind:∀ {x:Pal},Ready C B.val x→∀ (A:Realms)(i:Cover)(p:PlaqAxes),lambda (faceValue (x.board C K A 5) (i,p)) ≤ d
 lamp(x:Pal): Ready C B.val x→∀ (A:Realms)(p:Edge Cover), (∀ y:Cover,Range (B.val*C.val) p.1 y→∀ i:PlaqAxes,lambda (faceValue A (y,i))≤u) → x.board C K A 5 p=A p
lemma boltH (B:Side)(d:ℝ)(p:0<d)(b:ℝ)(v:0<b):∃ (C:Side)(K:ℕ→ℝ)(u:ℝ),0<u∧u≤ b∧Sweater C B K u d:=by
 obtain ⟨R,t,K,N,l⟩:= Pal.fitBoard 5 B.val; let k:=Real.sqrt (SU.group.repDim:ℝ); have hk:0<k:=Real.sqrt_pos.mpr (by exact_mod_cast SU.group.dimPos); obtain ⟨n,u⟩:= exists_nat_gt (4*R/(k*d)); let C:Side:=⟨n+N+1,by omega⟩; have hC:N≤ C.val:=by change N ≤ n+N+1; omega
 obtain ⟨e,q,x⟩:=cubing B C; refine ⟨C,K,min b e,lt_min v q,min_le_left ..,⟨?_,?_⟩⟩
 · intro x t A i p'; apply (sailL t (R:=R) _ (l C hC x t A) i p').trans; rw [←mul_div_assoc]; apply (div_le_iff₀ (mul_pos (by positivity) hk)).2; have h:4*R/(k*d) < (C.val:ℝ):= u.trans_le (Nat.cast_le.mpr (show n≤n+N+1 by omega)); exact ((div_lt_iff₀ (mul_pos hk p)).mp h).le.trans_eq (show ↑C.val*(k*d)=d*(↑C.val*k) by ring)
 intro y t A p l'; obtain ⟨z,H⟩:= Pal.emerge t p; let F:= spanFits.mp (place H.2); let u:wellF z A C 1:= x A p.1 z F.1 (shoulder t.roof _ H.1.1) (fun a v p=> (l' a v p).trans (min_le_right ..)); exact ((l C hC y t A).1 _ H.1 u p F.1 F.2).symm
end Palace
end YM.CF.VolumeCape
