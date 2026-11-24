import YM.SU5.FiniteGaugeData.Mist.Kodiak
/-!
# Ordered tapes of markers paying from the engine

Gaps on perspectives. Relative future product,
energy and cost porting via any refinement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist
open Function Filter Metric Finset Lattice Hills
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace
section
variable {X T:Type}[Monoid T](f:X→ T)(Q:X→ X→T)
abbrev spool : X→ List X→ T
 | x, [] => f x
 | x, b::l=> f x * (Q x b * spool b l)
def TapeT : List X→T
 | []=>1
 | x::l=> spool f Q x l
end
-- movement with relative coordinates along Vista on ALL axes. time part uses cap.Pos.
variable {L:Side}{H:Hilbert}{a:Axis}(X:Terrace H L a)
abbrev Carousel (L:Side):= Axis→VistaQ L
local notation "R"=> VistaQ L
variable (s t:ℕ)
-- at ANY support chart
abbrev reportQ (u:Four ℤ): Carousel L:= fun i=> ticQ L s (u i)
lemma report_add (v w:Four ℤ): reportQ (L:=L) s (v+w)= reportQ s v+reportQ s w:= funext fun i=> addQ ..
lemma report_neg (x:Four ℤ): reportQ (L:=L) s (-x)=-reportQ s x:=funext fun i=> negQ ..
lemma report_sub(x y:Four ℤ): reportQ (L:=L) s (x-y)=reportQ s x-reportQ s y:=by rw [sub_eq_add_neg,report_add,report_neg,sub_eq_add_neg]
lemma report_often (x:Carousel L): ∀ᶠ i:ℕ in atTop,∃ z:Four ℤ,x=reportQ i z:=by
 filter_upwards [eventually_all.mpr (fun i:Axis=>frequentT _ (x i))] with i t; choose r u using t; exact ⟨r,funext fun v=> (u v).symm⟩
abbrev Maneu (X:Terrace H L a): Carousel L→ List Axis→ H.Op:=fun x v=> (v.map fun i=> ramble X i (x i)).prod
abbrev spireT (X:Terrace H L a): Carousel L→ H.Op:= fun x=> Maneu X x Terrace.scheduleL
variable (B:List Axis)(x y:Carousel L)(U:H.Op)
lemma glide_group (p:∀ i∈B, Commute U (ramble X i (x i))) : Commute U (Maneu X x B):= by induction B with
 | nil=>exact Commute.one_right _
 | cons i s ih=> exact (p i (by simp)).mul_right (ih (fun i v=>p i (by simp [v])))
lemma glide_norm (w:H): ‖Maneu X x B w‖= ‖w‖:=by induction B with
 | nil=>rfl
 | cons i s ih=> exact (ramble_price X i (x i) (Maneu X x s w)).trans ih
lemma glide_o : Maneu X 0 B=1:=by induction B with
 | nil=>rfl
 | cons i s ih=> change ramble X i 0 * Maneu X 0 s=1; rw [ramble_zero, ih,one_mul]
lemma glide_more : Maneu X (x+y) B=Maneu X x B*Maneu X y B:=by induction B with
 | nil=>exact (mul_one ..).symm
 | cons i s ih=> unfold Maneu; simp only [List.map_cons,List.prod_cons]; change ramble X i (x i+y i)*Maneu X _ s=(ramble X i (x i)*_)*(_*_); rw [ramble_two,ih]; exact eq' _ _ _ _ (glide_group X s x (ramble X i (y i)) (fun v _=> ramble_across ..))
where eq'(a b c d:H.Op)(p:Commute b c): (a*b)*(c*d)=(a*c)*(b*d):=by rw [mul_assoc,mul_assoc, ←mul_assoc b c,p.eq,mul_assoc]
lemma glide_one (b:Axis)(v:VistaQ L) : spireT X (Pi.single b v)=ramble X b v:=by fin_cases b <;> simp [spireT,Maneu,Terrace.scheduleL,ramble_zero]
lemma glide_self (x y:Carousel L)(h:∀ i:Axis,i≠a→x i=y i): spireT X x=spireT X y:=by
 have he:(fun i=>ramble X i (x i))=(fun i=>ramble X i (y i)):= funext fun i=> by
    by_cases p:i=a; · subst i; rw [ramble_self,ramble_self]
    rw [h _ p] -- indent
 unfold spireT Maneu; rw [he]
end YM.CF.Buffered.Afterglow.Hierarchy.Mist
