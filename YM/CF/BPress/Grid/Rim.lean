import YM.CF.BPress.Grid.Entity
import YM.CF.BPress.Smooth.SU
/-! Support/scaled-coordinate costs for discrete skeleton entities. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
open Function Finset Lattice MeasureTheory Filter
open scoped Topology BigOperators NNReal ENNReal Classical
variable {s : Side} {k : Tiling s} {d : ℕ}

abbrev Desk (d : ℕ) := Fin d → ℝ
-- note NOT sup sphere, though one after shifting center & changing units
def table (d : ℕ) := Set.Icc (0 : Desk d) 1
def rim (d : ℕ) := table d ∩ {x : Desk d| ∃ i, x i=0 ∨ x i=1}
lemma table_compact (d : ℕ) : IsCompact (table d):= isCompact_Icc
lemma rim_compact (d : ℕ) : IsCompact (rim d):= by unfold rim; apply IsCompact.inter_right (table_compact _); simp_rw [Set.setOf_exists,Set.setOf_or]; exact isClosed_iUnion_of_finite fun i=>(isClosed_eq (continuous_apply i) continuous_const).union (isClosed_eq (continuous_apply i) continuous_const)
lemma rim_price (d : ℕ) : dimH (rim (d+1))≤ d:= by
  let f(i:Fin (d+1))(a:ℝ) : Desk d → Desk (d+1) := i.insertNth (α:=fun _=>ℝ) a
  let M(i:Fin (d+1))(a:ℝ) := Set.range (f i a); have h (i a) : dimH (M i a) ≤ d:=by
    have he:LipschitzWith 1 (f i a):= LipschitzWith.of_dist_le_mul fun x y=>by dsimp only [f]; rw [Fin.dist_insertNth_insertNth]; simp
    exact he.dimH_range_le.trans_eq (Real.dimH_univ_pi_fin _)
  have e : rim (d+1) ⊆ ⋃ i, M i 0 ∪ M i 1:=by
    rintro x ⟨l,i,hi|hi⟩ <;> apply Set.mem_iUnion.mpr
    exact ⟨i,.inl ⟨i.removeNth x,by unfold f; rw [← hi,Fin.insertNth_self_removeNth]⟩⟩
    exact ⟨i,.inr ⟨i.removeNth x,by unfold f; rw [← hi,Fin.insertNth_self_removeNth]⟩⟩
  apply (dimH_mono e).trans; simp_rw [dimH_iUnion,dimH_union]; exact iSup_le fun i=> max_le (h ..) (h ..)
namespace Entity
variable (J : Entity k d)
def ration (x: Coord d) : Desk d:= fun i=> (x i:ℝ)/k.b.val
-- J arg?
abbrev bound (i:Fin d) : ℕ:=if i∈ J.axes then k.b.val else 0
variable {a b : Coord d}{i j : Fin d}{t:Bool}
lemma ration_mem (h : J.Valid a) : ration (k:=k) a ∈ table d := by
  have hp: 0<(k.b.val:ℝ):= by exact_mod_cast k.b.property
  exact ⟨fun i=>div_nonneg (Nat.cast_nonneg _) hp.le,fun i=> (div_le_one hp).mpr (Nat.cast_le.mpr (J.dim_max h i))⟩
lemma rim_mem (h : J.Valid a)(e:J.Boundary a): ration (k:=k) a∈rim d:= by
  obtain ⟨i,t,g,f⟩:= e; refine ⟨J.ration_mem h,i,?_⟩; unfold ration; rw [f]; cases t <;> simp [k.b.property.ne']
variable (k) in
lemma ration_tick (a : Coord d)(i : Fin d): dist (ration (k:=k) a) (ration (k:=k) (tick a i)) ≤ (k.b.val:ℝ)⁻¹:= by
  refine (dist_pi_le_iff (by positivity : 0 ≤ (k.b.val:ℝ)⁻¹)).mpr fun j=>?_; unfold ration; by_cases p:j=i; subst j; rw [tick_self,Nat.cast_add_one,Real.dist_eq,add_div,sub_add_eq_sub_sub,sub_self] -- tune
  · simp
  rw [tick_ne _ p,dist_self]; positivity
variable {F : Type} [PseudoMetricSpace F] (f : Coord d→ F)

abbrev edgeBudget (u : ℝ) : Prop := ∀ (a : Coord d) (i : Fin d), J.Valid a → J.Valid (tick a i) →
    ∀ j t, J.OnFace a j t → J.OnFace (tick a i) j t → dist (f a) (f (tick a i))≤ u / k.b.val
lemma alter_valid (a:Coord d)(h:J.Valid a)(i:Fin d)(u:ℕ)(p:u≤ J.bound i) : J.Valid (Function.update a i u):= by intro j; by_cases p:j=i; subst j; rw [update_self]; apply ‹_›; rw [update_of_ne p]; exact h j
lemma alter_face (a:Coord d)(t:Bool)(u:ℕ)(h:J.OnFace a i t)(p:j≠i): J.OnFace (Function.update a j u) i t:= ⟨h.1, (update_of_ne p.symm ..|>.trans h.2)⟩
-- travel along one axis on a fixed face
lemma axis_price (p : ℝ) (e : J.edgeBudget f p) (h:J.Valid a) (y:J.OnFace a i t) (g:j≠i)(u:ℕ) (l:u≤J.bound j) (v: a j≤u) :
    dist (f a) (f (Function.update a j u))≤ ((u-a j:ℕ):ℝ)* (p/k.b.val) := by
  obtain ⟨r,rfl⟩:= Nat.exists_eq_add_of_le v; clear v; induction r with
  | zero => simp
  | succ n ih =>
    let b:=Function.update a j (a j+n)
    have hh:J.Valid b:= J.alter_valid a h j _ (by omega)
    have hz : tick b j=Function.update a j (a j+(n+1)):= by unfold b tick; rw [update_self,update_idem]; rw [Nat.add_assoc]
    have he := e b j hh (hz.symm ▸ J.alter_valid a h j _ l) i t (J.alter_face a t _ y g) (hz.symm ▸ J.alter_face a t _ y g); rw [hz] at he
    apply le_trans (dist_triangle _ (f b) _); refine (add_le_add (ih (by omega)) he).trans_eq ?_; rw [Nat.add_sub_cancel_left,Nat.add_sub_cancel_left]; push_cast; ring
lemma axis_both (p:ℝ)(e:J.edgeBudget f p)(h:J.Valid a)(y:J.OnFace a i t)(g:j≠i)(u:ℕ)(l:u≤J.bound j) :
    dist (f a) (f (Function.update a j u)) ≤ p * |ration (k:=k) a j - (u:ℝ)/k.b.val| := by
  have hz:0 < (k.b.val:ℝ):= by positivity
  rcases le_total u (a j) with v|v
  · let b:= update a j u
    have hh:= J.axis_price f p e (J.alter_valid _ h j _ l) (J.alter_face a t u y g) g _ (h j) (by rwa [update_self]); rw [update_self,Nat.cast_sub v, update_idem,update_eq_self] at hh; rw [dist_comm]; apply hh.trans_eq; rw [ration, ← sub_div,abs_of_nonneg (div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr v)) hz.le)]; ring
  apply (J.axis_price f p e h y g u l v).trans_eq; rw [Nat.cast_sub v,ration,abs_sub_comm, ← sub_div,abs_of_nonneg (div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr v)) hz.le)]; ring -- pattern abs_div

lemma axis_dist (a : Coord d) (b : Coord d)(i:Fin d) : |(ration (k:=k) a i)-(b i:ℝ)/k.b.val|≤ dist (ration (k:=k) a) (ration (k:=k) b):= dist_le_pi_dist (ration (k:=k) a) (ration (k:=k) b) i
-- implement within common face by updating coordinates carrying same face i. record remaining differences via set of coords, strengthen lemma using bound on max individual to swap. yields d factor.
lemma face_price (p : ℝ)(hp:0≤p)(e:J.edgeBudget f p) (h:J.Valid a) (u:J.Valid b)(x:J.OnFace a i t)(y:J.OnFace b i t) :
    dist (f a) (f b)≤ (d:ℝ)*p * dist (ration (k:=k) a) (ration (k:=k) b) := by
  let R:=dist (ration (k:=k) a) (ration (k:=k) b)
  have hv:0≤R:=dist_nonneg
  have he (S: Finset (Fin d)) (c:Coord d)(v:J.Valid c)(w:J.OnFace c i t)(g:∀ j∉S,c j=b j)
     (t₀:dist (ration (k:=k) c) (ration (k:=k) b)≤R): dist (f c) (f b)≤ (S.card:ℝ)*p * R:= by
    induction S using Finset.induction_on generalizing c with
    | empty=> rw [show c=b from funext fun _=>g _ (by simp)]; simp
    | @insert j S p' ih=>
      let z:= update c j (b j); have hi:J.Valid z:= J.alter_valid c v j _ (u j); have he : c i=b i:= w.2.trans y.2.symm -- tune
      have H (k) (h:k∉ S): z k=b k:= by
         by_cases e:k=j; · simp [z,e]
         rw [show z k=c k from update_of_ne e ..]; exact g k (by simp [h,e]) -- tune
      have hr:J.OnFace z i t:= by
         by_cases k:j=i; · unfold z; rw [k,←he,update_eq_self]; exact w
         exact J.alter_face c _ _ w k
      have hz:dist (ration (k:=k) z) (ration (k:=k) b)≤ R:= (dist_pi_le_iff hv).mpr fun j' => by
         by_cases e:j'=j; · subst j'; simp [z, ration,hv]
         unfold ration z; rw [update_of_ne e]; exact (dist_pi_le_iff hv).mp t₀ j'
      refine (dist_triangle _ (f z) _).trans ((add_le_add (show dist (f c) (f z)≤ p*R from ?_) (ih _ hi hr H hz)).trans_eq ?_)
      · by_cases l:j=i; · unfold z; rw [l,←he,update_eq_self,dist_self]; positivity
        exact (J.axis_both f p e v w l _ (u j)).trans (mul_le_mul_of_nonneg_left ((axis_dist ..).trans t₀) hp)
      rw [card_insert_of_notMem p']; push_cast; ring
  simpa only [card_univ,Fintype.card_fin] using he univ a h x (fun i l=> (l (mem_univ _)).elim) le_rfl
lemma across_price (L H:ℝ)(hp:0≤L)(p:0≤H)(e:J.edgeBudget f L) (g : dist (f a) (f b)≤H)
    (u:J.Valid a)(v:J.Valid b)(x:J.Boundary a)(y:J.Boundary b) :
    dist (f a) (f b) ≤ (2*(d:ℝ)*L+H)*dist (ration (k:=k) a) (ration (k:=k) b) := by
  obtain ⟨i,t,x⟩:=x; obtain ⟨j,s',y⟩:=y; let r:=dist (ration (k:=k) a) (ration (k:=k) b); have hm:0≤r:=dist_nonneg
  by_cases h:i=j
  · subst j; by_cases h:t=s'
    · subst s'; refine (J.face_price f L hp e u v x y).trans ?_; change _≤ _* r; apply mul_le_mul_of_nonneg_right _ hm; nlinarith only [hp,p, show 0 ≤ (d:ℝ) by positivity]
    have he:=J.dim_max u i; have ht:= (axis_dist (k:=k) a b i); refine g.trans (le_trans (le_mul_of_one_le_right p (b:=r) ?_) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hm));
    unfold ration at ht; change _≤ r at ht; cases t <;> cases s' <;> first | contradiction| simpa [x.2,y.2] using ht
  let c:= Function.update a j (b j); have hc:J.Valid c:=J.alter_valid _ u j _ (v j); have hx:J.OnFace c i t:= J.alter_face _ _ _ x (Ne.symm h); have hy:J.OnFace c j s':=⟨y.1,(update_self ..|>.trans y.2)⟩
  have η(α : Coord d)(β:Coord d)(h:∀ i, α i=β i ∨ (α i=a i∧β i=b i)): dist (ration (k:=k) α) (ration (k:=k) β)≤r:= by
    refine (dist_pi_le_iff hm).mpr fun i=>?_ ; unfold ration; rcases h i with x|⟨x,y⟩; rw [x,dist_self]; exact hm; rw [x,y]; exact axis_dist .. -- expected definitional
  have ha:= J.face_price f L hp e u hc x hx; have hb:= J.face_price f L hp e hc v hy y
  have h1:= η a c (fun i=>by by_cases g:i=j <;> simp [c,g]); have h2:=η c b (fun i=>by by_cases g:i=j <;> simp [c,g]); apply (dist_triangle _ (f c) _).trans; change _≤_*r; replace ha:=ha.trans (mul_le_mul_of_nonneg_left h1 (by positivity)); replace hb:=hb.trans (mul_le_mul_of_nonneg_left h2 (by positivity)); nlinarith only [ha,hb,p,hm]
lemma ration_inj (k : Tiling s) : Injective (ration (d:=d) (k:=k)):=by
 intro i j h; ext t; have he:=congrFun h t; unfold ration at he; field_simp at he; exact_mod_cast he

end Entity
end YM.CF.BPress.Grid
