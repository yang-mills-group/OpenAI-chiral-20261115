import YM.SU5.Selected.Chene.Melody
import YM.SU5.Selected.Chene.Shale
set_option autoImplicit false
noncomputable section
namespace YM.Chene.Trunk
open Function Matrix Lattice Finset SectorNext.Vacuum.FlatTree FreeResolvent Next.Rank.Axial Precision Exterior Pad Melody
open scoped Topology MatrixOrder BigOperators Matrix
variable {n:Side}(h:1<n.val)
include h
lemma length_zero (a:Axis)(x:Site n) : x+step a≠x:=by
 intro hz; have hv:(1:Per n)=0:= add_eq_left.mp (by simpa using (congrFun hz a) : x a+(1:Per n)=x a) -- tune
 have ht:=ZMod.val_one'' (n:=n.val) h.ne'; rw [hv,ZMod.val_zero] at ht; omega
include h
lemma handle_fall(v:Reed n→ℝ)(p:pin ℝ n *ᵥ v=0)(h₁:∀ e∈ (axle n).trunks,v e=0)(i:Axis):v (handle n i)=0:=by
 have hp:∀ a:Per n, a≠ -1 → v (lineK n i a,i)=0:=by
    intro a t; apply h₁; rw [trunk_here,line_next]; refine ⟨?_,fun j q=>?_⟩; · simpa [lineK] using (show a+1≠0 from fun h=> t (eq_neg_of_add_eq_zero_left h))
    simp [lineK,q.ne]
 calc
    v _ = ∑ a:Per n,v (lineK n i a,i) := by rw [sum_eq_single (-1),line_prev]; rfl; intro b _ l; exact hp b l; simp
    _= 0 := by rw [←pin_apply,p]; rfl
lemma song_off {p:circle n} {e:Reed n} (v:Reed n→ℝ)(x:song p v=0)(k:e∈ edges p)(q:∀j∈edges p,j≠e→v j=0) : v e=0:=by
 rcases p with ⟨w,⟨i,j⟩,g⟩; let A:Reed n:=(w,i); let B:Reed n:=(w+step i,j); let C:Reed n:=(w+step j,i); let D:Reed n:=(w,j); have hp:A≠B:= fun h=> (show i<j from g).ne (congrArg Prod.snd h)
 have hq:A≠C:=fun z=> length_zero h _ _ (congrArg Prod.fst z).symm; have hs:A≠D:=fun h=> g.ne (congrArg Prod.snd h); have ht:B≠D:=fun z=> length_zero h _ _ (congrArg Prod.fst z); have hr:B≠C:= fun h=> (show i<j from g).ne' (congrArg Prod.snd h); have hb:C≠D:=fun h=>g.ne (congrArg Prod.snd h)
 have hv(e':Reed n):= reads_four w i j g e'
 have a:v A=0 ∨ e=A:=by by_cases h:e=A; exact Or.inr h; exact Or.inl (q _ ((hv A).2 (Or.inl rfl)) (Ne.symm h))
 have b:v B=0 ∨ e=B:=by by_cases h:e=B; exact Or.inr h; exact Or.inl (q _ ((hv B).2 (Or.inr (Or.inl rfl))) (Ne.symm h))
 have c:v C=0 ∨ e=C:=by by_cases h:e=C; exact Or.inr h; exact Or.inl (q _ ((hv C).2 (Or.inr (Or.inr (Or.inl rfl)))) (Ne.symm h))
 have d:v D=0 ∨ e=D:=by by_cases h:e=D; exact Or.inr h; exact Or.inl (q _ ((hv D).2 (Or.inr (Or.inr (Or.inr rfl)))) (Ne.symm h))
 change v B-v D-(v C-v A)=0 at x
 rcases (show e=A ∨ e=B ∨ e=C ∨ e=D from (hv _).1 k) with a|b|c|d <;> subst e -- shadow!
 · linarith [b.resolve_right hp,c.resolve_right hq,d.resolve_right hs]
 · linarith [a.resolve_right hp.symm,c.resolve_right hr,d.resolve_right ht]
 · linarith [a.resolve_right hq.symm,b.resolve_right hr.symm,d.resolve_right hb]
 linarith [a.resolve_right hs.symm,b.resolve_right ht.symm,c.resolve_right hb.symm]
lemma sober (v:Reed n→ℝ)(q:curl ℝ n*ᵥ v=0)(p:pin ℝ n*ᵥ v=0)(h₁:∀ e∈ (axle n).trunks,v e=0): v=0:=by
 classical
 by_contra z; obtain ⟨i,hp⟩:= Function.ne_iff.mp z; let E:=univ.filter fun i=>v i≠0; obtain ⟨i,w,u⟩:= Finset.exists_min_image E priorityAt ⟨i,mem_filter.mpr ⟨mem_univ _,hp⟩⟩
 have he: v i≠0 := (mem_filter.mp w).2
 have hg:i ∈ swept n:= mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, fun t=> he (h₁ _ t)⟩,fun t=>?_⟩
 swap; · obtain ⟨j,_,y⟩:= mem_image.mp t; apply he; rw [←y]; exact handle_fall h v p h₁ j
 obtain ⟨Q,W,s⟩:= exists_face i hg; apply he (song_off h v (by rw [←curl_applyZ,q]; rfl) W fun i' hi z=> ?_)
 by_contra e; exact (s i' hi z (fun w=> e (h₁ i' w))).not_ge (u i' (mem_filter.mpr ⟨mem_univ _,e⟩))
omit h in
lemma loyalty (S:Finset (Reed n))(v:forestFree S→ℝ)(e:Reed n)(p:e∈S) : ((wrote S)ᵀ*ᵥ v) e=0:=by
 unfold wrote walk mulVec dotProduct; refine sum_eq_zero fun i _=>?_; let U:= i.property; change ((1:Matrix _ _ ℝ) i.val e)*v i=0; rw [Matrix.one_apply_ne,zero_mul]; exact fun t=>U (t.symm ▸ p)
abbrev frore (S:Finset (Reed n))(T:Type*)[CommRing T]:= (curl T n).submatrix id (Subtype.val : forestFree S→ Reed n)
abbrev fame (S:Finset (Reed n))(T:Type*)[CommRing T]:= (pin T n).submatrix id (Subtype.val:forestFree S→ Reed n)
def anneal (T:Type*)[CommRing T] (S:Finset (Reed n)) : Matrix (forestFree S) (forestFree S) T:= (frore S T)ᵀ*frore S T+(fame S T)ᵀ*fame S T
omit h
lemma anneal_chart (S: Finset (Reed n)): realM (anneal ℤ S)= anneal ℝ S:=by
 let H:= Int.castRingHom ℝ; let C:= frore S ℤ; let A:= fame S ℤ; change (Cᵀ*C+Aᵀ*A).map H= _; rw [Matrix.map_add H (_root_.map_add H), Matrix.map_mul, Matrix.map_mul,Matrix.transpose_map, Matrix.transpose_map]; -- tune
 have hx:C.map H=frore S ℝ:=congrArg (fun x=> x.submatrix (@id (circle n)) (Subtype.val:forestFree S→_)) (liftCurl n)
 rw [hx, show A.map H= _ from (show A.map H=fame S ℝ from congrArg (fun x=> x.submatrix (@id Axis) (Subtype.val:forestFree S→_)) (liftPin n))]; rfl
include h
lemma age_positive(S:Finset (Reed n))(p:S=(axle n).trunks) : (anneal ℝ S).PosDef:=by
 let A:=frore S ℝ; let B:=fame S ℝ; let N:=anneal ℝ S; apply PosDef.of_dotProduct_mulVec_pos (((squared A).add (squared B)).isHermitian); intro x t; rw [star_trivial]; rw [Matrix.add_mulVec, dotProduct_add]; let W:=wrote S; let D:=A *ᵥ x; let U:=B*ᵥ x; have ht:D≠0 ∨ U≠0:=by
    by_contra! he; apply t; let v:= Wᵀ*ᵥx; have hp:v=0:= sober h v (by unfold v; rw [mulVec_mulVec,show W=wrote S from rfl,wrote,pull_pay]; exact he.1) (by unfold v; rw [mulVec_mulVec,show W=wrote S from rfl,wrote,pull_pay]; exact he.2) (by rw [←p]; exact fun i hi=> loyalty _ _ _ hi)
    calc
    x=W*ᵥ v:=(by unfold v; rw [mulVec_mulVec,show W=wrote S from rfl,drape,one_mulVec])
    _= 0:=by rw [hp, Matrix.mulVec_zero]
 have pos{K:Type}[Fintype K](x:K→ℝ)(t:x≠0):0<x ⬝ᵥ x:=by obtain ⟨a,h⟩:= Function.ne_iff.mp t; exact (sq_pos_of_ne_zero (show x a≠0 from h)).trans_le (le_normSum x a)
 rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_transpose_mulVec]; rcases ht with p|p; exact add_pos_of_pos_of_nonneg (pos D p) (normSum_nn _)
 exact add_pos_of_nonneg_of_pos (normSum_nn _) (pos U p)
omit h
lemma altar (T:Bed)(a:ℝ)(S:Finset (Reed n))(p:a≤1) (t:Gap (T.metric.acts n) a)(s:(T.metric.acts n)ᵀ=T.metric.acts n) : a • anneal ℝ S ≤ Pad.principal (canopy n T) S:=by
 let D:= T.metric.acts n; let E:=(curl ℝ n); let K:=(pin ℝ n); let Y:=D.submatrix (petals n) (petals n); let V:=wrote S; let A:= E*Vᵀ; let B:=K*Vᵀ
 have hx:anneal ℝ S=Aᵀ*A+Bᵀ*B:=by unfold A B V wrote; rw [pull_pay,pull_pay]; rfl
 have hp: Pad.principal (canopy n T) S=Aᵀ*Y*A+Bᵀ*B:=by rw [chosen]; change V*canopy n T * Vᵀ=_; unfold canopy A B; rw [←flat_t]; change V*(Eᵀ*Y*E+Kᵀ*K)*Vᵀ=_; simp only [Matrix.mul_add,Matrix.add_mul,transpose_mul,transpose_transpose,Matrix.mul_assoc] -- tune
 have he:(Y-a • 1).PosSemidef:= (le_iff.mp (le_peg (by unfold Y; rw [transpose_submatrix,s]) ((t.submatrix _ (petals n).injective).lower)))
 have hf := he.conjTranspose_mul_mul_same A; rw [conjTranspose_eq_transpose_of_trivial] at hf
 have ht:= hf.add ((squared B).smul (sub_nonneg.mpr p)); apply le_iff.mpr; rw [hp,hx]; convert! ht using 1 <;> first|rfl| ( rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul, smul_add, sub_smul,one_smul]; abel)
include h
lemma grain (T:Bed)(a:ℝ)(S:Finset (Reed n))(p:Arbor (sky n) S)(r:0<a)(g:a≤1)(t:Gap (T.metric.acts n) a)(s:(T.metric.acts n)ᵀ=T.metric.acts n): a^Fintype.card (axle n).Free ≤ Chene n T S:=by
 let W:= (axle n).trunks; let M:= T.metric.acts n; let C:= pin ℝ n; let K:= anneal ℝ W; have ht:=age_positive h W rfl; have hv:1 ≤ K.det:=by unfold K; rw [←anneal_chart]; apply integer; rw [anneal_chart]; exact ht
 have hp:(a • K).PosDef:= ht.smul r; apply le_trans ?_ ((det_rise hp.posSemidef (altar T a W g t s)).trans_eq ((legal n (axle n)).signed (canopy n T) (pinned (pin ℝ n) _ (pasture_symm _ s)) (by rw [canopy,Matrix.add_mul,Matrix.mul_assoc (pin ℝ n)ᵀ, pin_angle, pasture_g, Matrix.mul_zero,add_zero]) p)) -- notation `.signed _` maybe from argument C inference wrong
 rw [det_smul]; exact le_mul_of_one_le_right (by positivity) hv
end YM.Chene.Trunk
#print axioms YM.Chene.Trunk.grain
