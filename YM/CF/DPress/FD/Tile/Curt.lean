import YM.CF.DPress.FD.Tile.Arch
import YM.CF.BPress.Grid.Coarse
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.FD.Ramp
open Function Metric Filter Set Module MeasureTheory BPress.Grid BPress.Smooth SU
open scoped Topology NNReal ENNReal ContDiff InnerProductSpace Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {I:Type*}[Fintype I]{m:ℕ}
-- arch to four coordinate dim actual. uniform.
abbrev ft(i:Fin 4) : Desk 3 → Desk 4:= i.insertNth (α:=fun _=>ℝ) 1
lemma ℓft(i:Fin 4) : LipschitzWith 1 (ft i):= LipschitzWith.of_dist_le_mul fun x y=>by dsimp only [ft]; rw [Fin.dist_insertNth_insertNth]; simp
-- rim image
abbrev CURT := ⋃ i:Fin 4, (ft i '' (BPress.Grid.rim 3))
lemma closed : IsCompact CURT:=isCompact_iUnion fun i=> (rim_compact 3).image (ℓft i).continuous
lemma price : dimH CURT ≤2:=by unfold CURT; rw [dimH_iUnion]; exact iSup_le fun i=> (LipschitzOnWith.dimH_image_le (ℓft i|>.lipschitzOnWith)).trans ((rim_price 2).trans_eq (by norm_num))
lemma ψcur : CURT ⊆ table 4:=by
 intro x h; obtain ⟨i,y,b,rfl⟩:= mem_iUnion.mp h; obtain ⟨⟨r,s⟩,h⟩:=b; refine ⟨fun j=>?_,fun j=>?_⟩; all_goals cases j using Fin.succAboveCases i; all_goals simp only [ft,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,Pi.zero_apply,Pi.one_apply]; all_goals first|norm_num1 <;> done| exact r _| exact s _
lemma curtain {x:Desk 4}(p:x∈table 4)(h:∃ i,x i=1) (q:∃ i,x i=0) : x ∈ CURT:=by
 obtain ⟨i,h⟩:= h; obtain ⟨j,q⟩:=q; let y:= i.removeNth x; have hv:j≠i:=by intro e; rw [e,h] at q; linarith
 apply mem_iUnion.mpr; refine ⟨i,y,⟨⟨fun j=>p.1 (i.succAbove j),fun j=> p.2 (i.succAbove j)⟩,?_⟩,(show ft i y=x from by unfold ft; rw [←h]; exact Fin.insertNth_self_removeNth ..)⟩ -- constructor set comprehension
 obtain ⟨k,rfl⟩:= Fin.exists_succAbove_eq hv; exact ⟨_,Or.inl (show y k=0 from q)⟩
variable {U : Finset I}
abbrev mapD(e:↥U ↪ Fin 4) (x:Ramp I m): Desk 4:= fun i=> if h:∃ t, e t=i then ((x h.choose.val).val:ℝ)/(m:ℝ) else 0
lemma mapD_right(e:↥U ↪ Fin 4)(x:Ramp I m)(i:↥U):mapD e x (e i)= ((x i.val).val:ℝ)/(m:ℝ):=by
 unfold mapD; let p:∃ t,e t=e i:= ⟨i,rfl⟩; rw [dif_pos p,e.injective p.choose_spec]
variable (e:↥U ↪ Fin 4)(p:0<m){x y: Ramp I m}
include p
lemma slot (x:Ramp I m): mapD e x∈table 4:=by
 have he:0<(m:ℝ):=by positivity
 constructor<;> intro j; change 0 ≤ mapD e x j; unfold mapD; split <;> positivity
 change mapD e x j≤1; unfold mapD; split; exact (div_le_one he).2 (Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Fin.isLt _))); exact zero_le_one
lemma bound(x:Ramp I m)(t:x∈boundary U) : mapD e x ∈ CURT:= by
 obtain ⟨i,h,v⟩:= exists_right p (border t); obtain ⟨j,k,E⟩:= Finset.exists_of_ssubset t.2; apply curtain (slot e p x) ⟨e ⟨i,h⟩,by rw [mapD_right]; simp [v,right,p.ne']⟩; refine ⟨e ⟨j,k⟩,?_ ⟩; rw [mapD_right]; have hp: x j=0:= not_not.mp (fun v=> E ((mem_h ..).2 v)); simp [hp]
lemma fin_cost(i j:Fin (m+1)) : dist ( (i.val:ℝ) / (m:ℝ)) ((j.val:ℝ)/(m:ℝ))= (DistU i j:ℝ)/(m:ℝ):=by
 rw [Real.dist_eq,←sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg m : (0:ℝ)≤m)]; congr 1; unfold DistU; rw [Nat.cast_add]; rcases le_total i.val j.val with h|h
 · rw [abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h)),Nat.sub_eq_zero_of_le h,Nat.cast_zero,zero_add,Nat.cast_sub h,neg_sub]
 rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h)), Nat.sub_eq_zero_of_le h,Nat.cast_zero,add_zero,Nat.cast_sub h]
lemma metric (v: On x U)(w:On y U): dist (mapD e x) (mapD e y)= δR x y:=by
 apply le_antisymm
 · refine (dist_pi_le_iff δp).mpr fun j=>?_ ; by_cases h:j∈ Set.range e
   · obtain ⟨j,rfl⟩:=h; rw [mapD_right,mapD_right,fin_cost p]; exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (tick ..)) (Nat.cast_nonneg _)
   unfold mapD; rw [dif_neg (show ¬∃ t,e t=j from h),dif_neg (show ¬∃ t,e t=j from h),dist_self]; exact δp
 obtain ⟨i,h,g⟩:= exists_right p v; obtain ⟨k,_,t⟩:= Finset.exists_mem_eq_sup (s:=Finset.univ) ⟨i,Finset.mem_univ _⟩ (fun j=> DistU (x j) (y j)); unfold δR; by_cases s:k∈ U; swap; · rw [show d x y= _ from t,dark v s,dark w s]; simp [DistU]
 have ht:= dist_le_pi_dist (mapD e x) (mapD e y) (e ⟨k,s⟩); rw [mapD_right,mapD_right,fin_cost p] at ht; rw [show d x y= _ from t]; exact ht
lemma monoD : InjOn (mapD (m:=m) e) (facet U):=by
 intro x v y w h; ext i; have hp:0<(m:ℝ):=by positivity
 by_cases H:i∈U; · have hv:= congrFun h (e ⟨i,H⟩); rw [mapD_right,mapD_right] at hv; change (x i).val=(y i).val; exact_mod_cast (div_left_inj' hp.ne').mp hv -- div names
 rw [dark v H,dark w H]
-- su wrapper using physical gauge metric (frob)
omit p
theorem externalT(a:ℝ≥0): ∃ b:ℝ≥0,∀ D ⊆ CURT, ∀ f: Desk 4→ E,LipschitzOnWith a f D→∃ g: Desk 4→ E,LipschitzOnWith b g (table 4)∧EqOn f g D:=by
 have d: dimH CURT<3:= price.trans_lt (by norm_num); obtain ⟨C,H⟩:=su_extension (table_compact 4) closed ψcur d 4 a; refine ⟨C,?_⟩; intro D s f F; obtain ⟨g,h,v,q⟩:=H D s (fun i=>fund (f i)) (LipschitzOnWith.of_dist_le_mul (fun i p j q=> (F.dist_le_mul i p j q))) (fun i _=> (show Mesa.trueS _ from ⟨SU.fund_U _, SU.fund_det _⟩)); let T (i:Desk 4): E:= if p:i∈table _ then (⟨⟨g i,(show Mesa.trueS _ from v p).1⟩,(show Mesa.trueS _ from v p).2⟩ : E) else 1; have hT (i) (u:i∈table 4) : fund (T i)=g i:=by unfold T; rw [dif_pos u]; rfl
 refine ⟨T,LipschitzOnWith.of_dist_le_mul (fun i u j p=>?_),fun i p=> group.mat_injective ((q p).trans (hT _ (ψcur (s p))).symm)⟩; change dist (fund (T i)) (fund (T j))≤ _; rw [hT i u,hT j p]; exact h.dist_le_mul i u j p
lemma budgetL(a:ℝ): ∃ b:ℝ, 0≤b∧∀ {I:Type*} [Fintype I](S:Finset I), S.card≤4 → ∀ (m:ℕ),0 < m → ∀ f:Ramp I m→E,Speed (boundary S) f a→∃ g:Ramp I m→E,full S g b∧EqOn f g (boundary S):=by
 obtain ⟨b,hb⟩:= externalT (Real.toNNReal a)
 refine ⟨b,b.property,?_⟩; intro I A S P m h f F; let D:= boundary (m:=m) S; obtain ⟨e⟩:= Function.Embedding.nonempty_of_card_le (show Fintype.card S ≤ Fintype.card (Fin 4) from by simpa using P)
 let φ:= mapD (m:=m) e; let g'(i:Desk 4):E:=if p:i∈ φ '' D then f p.choose else 1; have he(i)(u:i∈D):g' (φ i)= f i:=by
    let p: φ i∈φ '' D:= mem_image_of_mem _ u; unfold g'; rw [dif_pos p,show p.choose=i from monoD e h (border p.choose_spec.1) (border u) p.choose_spec.2]
 have H:LipschitzOnWith (Real.toNNReal a) g' (φ '' D):=by
    apply LipschitzOnWith.of_dist_le_mul; intro i x j t; obtain ⟨i,x,rfl⟩:=x; obtain ⟨j,t,rfl⟩:=t; rw [he i x,he j t,show dist (φ i) (φ j)=δR i j from metric e h (border x) (border t)]; exact (F i x j t).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal a) δp)
 obtain ⟨g,v,q⟩:=hb (φ '' D) (Set.image_subset_iff.mpr fun i p=> bound e h i p) g' H; exact ⟨g ∘ φ, fun i p j s=> (v.dist_le_mul _ (slot e h i) _ (slot e h j)).trans_eq (congrArg _ (metric e h p s)),fun i v=> (he i v).symm.trans (q (mem_image_of_mem _ v))⟩
end YM.CF.DPress.FD.Ramp
